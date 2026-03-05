//! Generic candidate index for rule/pattern lookup.
//!
//! Callers provide compact keys for rule LHS patterns and query expressions.

use std::collections::HashMap;
use std::hash::Hash;

/// Classification key for one rule-pattern LHS.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PatternIndexKey<H> {
    AtomConst(H),
    AtomAny,
    ListHeadConst { arity: usize, head: H },
    ListArityAny { arity: usize },
}

/// Classification key for one query expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QueryIndexKey<H> {
    AtomConst(H),
    AtomOther,
    List { arity: usize, head: Option<H> },
}

/// Rule-candidate index.
#[derive(Debug, Clone)]
pub struct RuleIndex<H>
where
    H: Clone + Eq + Hash,
{
    atom_const: HashMap<H, Vec<usize>>,
    atom_any: Vec<usize>,
    list_head_const: HashMap<usize, HashMap<H, Vec<usize>>>,
    list_arity_any: HashMap<usize, Vec<usize>>,
}

impl<H> Default for RuleIndex<H>
where
    H: Clone + Eq + Hash,
{
    fn default() -> Self {
        Self {
            atom_const: HashMap::new(),
            atom_any: Vec::new(),
            list_head_const: HashMap::new(),
            list_arity_any: HashMap::new(),
        }
    }
}

impl<H> RuleIndex<H>
where
    H: Clone + Eq + Hash,
{
    /// Build from a sequence of per-pattern keys.
    ///
    /// Each entry index in `keys` becomes the corresponding rule index.
    pub fn from_pattern_keys<I>(keys: I) -> Self
    where
        I: IntoIterator<Item = PatternIndexKey<H>>,
    {
        let mut idx = Self::default();
        for (rule_idx, key) in keys.into_iter().enumerate() {
            match key {
                PatternIndexKey::AtomConst(a) => {
                    idx.atom_const.entry(a).or_default().push(rule_idx);
                },
                PatternIndexKey::AtomAny => {
                    idx.atom_any.push(rule_idx);
                },
                PatternIndexKey::ListHeadConst { arity, head } => {
                    idx.list_head_const
                        .entry(arity)
                        .or_default()
                        .entry(head)
                        .or_default()
                        .push(rule_idx);
                },
                PatternIndexKey::ListArityAny { arity } => {
                    idx.list_arity_any.entry(arity).or_default().push(rule_idx);
                },
            }
        }
        idx
    }

    /// Return candidate rule indices for a query expression key.
    ///
    /// Order is deterministic and intentionally mirrors the prior surface logic:
    /// atom-any first, then arity-any, then head-specific buckets.
    pub fn candidates_for_query(&self, query: QueryIndexKey<H>) -> Vec<usize> {
        match query {
            QueryIndexKey::AtomConst(atom) => {
                let mut out = Vec::with_capacity(
                    self.atom_any.len() + self.atom_const.get(&atom).map_or(0, Vec::len),
                );
                out.extend(self.atom_any.iter().copied());
                if let Some(bucket) = self.atom_const.get(&atom) {
                    out.extend(bucket.iter().copied());
                }
                out
            },
            QueryIndexKey::AtomOther => self.atom_any.clone(),
            QueryIndexKey::List { arity, head } => {
                let head_bucket_len = head
                    .as_ref()
                    .and_then(|h| {
                        self.list_head_const
                            .get(&arity)
                            .and_then(|per_head| per_head.get(h))
                    })
                    .map_or(0, Vec::len);
                let mut out = Vec::with_capacity(
                    self.atom_any.len()
                        + self.list_arity_any.get(&arity).map_or(0, Vec::len)
                        + head_bucket_len,
                );
                out.extend(self.atom_any.iter().copied());
                if let Some(bucket) = self.list_arity_any.get(&arity) {
                    out.extend(bucket.iter().copied());
                }
                if let Some(head) = head.as_ref() {
                    if let Some(bucket) = self
                        .list_head_const
                        .get(&arity)
                        .and_then(|per_head| per_head.get(head))
                    {
                        out.extend(bucket.iter().copied());
                    }
                }
                out
            },
        }
    }
}
