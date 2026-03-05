//! Generic lookup-family index for mixed exact/pattern query paths.
//!
//! This is intended for generated language helpers that need:
//! - exact key lookup (O(1))
//! - candidate narrowing for pattern rules via `RuleIndex`

use crate::{PatternIndexKey, QueryIndexKey, RuleIndex};
use std::collections::HashMap;
use std::hash::Hash;

/// Lookup index with separate exact and pattern stores.
#[derive(Debug, Clone)]
pub struct LookupFamilyIndex<K, E, P>
where
    K: Clone + Eq + Hash,
    E: Clone,
    P: Clone,
{
    exact_values: HashMap<K, Vec<E>>,
    pattern_values: Vec<P>,
    pattern_index: RuleIndex<K>,
}

impl<K, E, P> Default for LookupFamilyIndex<K, E, P>
where
    K: Clone + Eq + Hash,
    E: Clone,
    P: Clone,
{
    fn default() -> Self {
        Self {
            exact_values: HashMap::new(),
            pattern_values: Vec::new(),
            pattern_index: RuleIndex::default(),
        }
    }
}

impl<K, E, P> LookupFamilyIndex<K, E, P>
where
    K: Clone + Eq + Hash,
    E: Clone,
    P: Clone,
{
    /// Build from exact values and pattern (index-key, payload) entries.
    pub fn from_parts(
        exact_values: HashMap<K, Vec<E>>,
        pattern_entries: Vec<(PatternIndexKey<K>, P)>,
    ) -> Self {
        let mut keys = Vec::with_capacity(pattern_entries.len());
        let mut values = Vec::with_capacity(pattern_entries.len());
        for (k, v) in pattern_entries {
            keys.push(k);
            values.push(v);
        }
        Self {
            exact_values,
            pattern_values: values,
            pattern_index: RuleIndex::from_pattern_keys(keys),
        }
    }

    /// Exact values for a query key.
    pub fn exact_values(&self, key: &K) -> Option<&[E]> {
        self.exact_values.get(key).map(Vec::as_slice)
    }

    /// True if there is at least one exact value for this key.
    pub fn has_exact(&self, key: &K) -> bool {
        self.exact_values.contains_key(key)
    }

    /// Candidate pattern payloads for the query key.
    pub fn pattern_candidates(&self, query: QueryIndexKey<K>) -> Vec<&P> {
        self.pattern_index
            .candidates_for_query(query)
            .into_iter()
            .filter_map(|idx| self.pattern_values.get(idx))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::LookupFamilyIndex;
    use crate::{PatternIndexKey, QueryIndexKey};
    use std::collections::HashMap;

    #[test]
    fn exact_and_pattern_paths_work_together() {
        let mut exact = HashMap::new();
        exact.insert("a", vec![1, 2]);
        let index = LookupFamilyIndex::from_parts(
            exact,
            vec![
                (PatternIndexKey::AtomAny, "any"),
                (PatternIndexKey::ListHeadConst { arity: 2, head: "h" }, "head"),
            ],
        );

        assert_eq!(index.exact_values(&"a"), Some([1, 2].as_slice()));
        assert!(index.has_exact(&"a"));
        assert!(!index.has_exact(&"x"));
        let cands = index.pattern_candidates(QueryIndexKey::List { arity: 2, head: Some("h") });
        assert_eq!(cands, vec![&"any", &"head"]);
    }
}
