//! Shared MeTTa-family pattern matching and substitution helpers.
//!
//! Language backends provide a thin adapter trait implementation for their
//! concrete term type.

use std::collections::HashMap;
use std::hash::Hash;

use crate::{PatternIndexKey, QueryIndexKey};

/// Supported binary constructor kinds for generic traversal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MettaBinaryKind {
    ExprCons,
    EqAtom,
}

/// Adapter trait for MeTTa-family pattern matching/substitution.
pub trait MettaFamilyPattern: Clone + PartialEq {
    /// Pattern variable name, if this node is a pattern variable.
    fn pattern_var_name(&self) -> Option<String>;

    /// Decompose supported binary constructors.
    fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)>;

    /// Recompose a binary constructor.
    fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self;
}

/// Optional list-shape adapter for MeTTa-family expression lists.
///
/// This enables shared rule/query indexing helpers used by language backends.
pub trait MettaFamilyListForm: MettaFamilyPattern + Eq + Hash {
    /// Decompose one expression-list cons cell.
    fn expr_cons_parts(&self) -> Option<(&Self, &Self)>;

    /// True when this node is expression-list nil.
    fn is_expr_nil(&self) -> bool;
}

/// Recursive match with binding accumulation.
pub fn metta_match_rec<T>(pattern: &T, concrete: &T, bindings: &mut HashMap<String, T>) -> bool
where
    T: MettaFamilyPattern,
{
    if let Some(var_name) = pattern.pattern_var_name() {
        if let Some(bound) = bindings.get(&var_name) {
            return bound == concrete;
        }
        bindings.insert(var_name, concrete.clone());
        return true;
    }

    match (pattern.decompose_binary(), concrete.decompose_binary()) {
        (Some((pk, pl, pr)), Some((ck, cl, cr))) if pk == ck => {
            metta_match_rec(pl, cl, bindings) && metta_match_rec(pr, cr, bindings)
        },
        _ => pattern == concrete,
    }
}

/// Pattern match wrapper returning bindings on success.
pub fn metta_match<T>(pattern: &T, concrete: &T) -> Option<HashMap<String, T>>
where
    T: MettaFamilyPattern,
{
    let mut bindings = HashMap::new();
    if metta_match_rec(pattern, concrete, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

/// Apply bindings to an atom/tree.
pub fn metta_subst<T>(atom: &T, bindings: &HashMap<String, T>) -> T
where
    T: MettaFamilyPattern,
{
    if let Some(var_name) = atom.pattern_var_name() {
        if let Some(v) = bindings.get(&var_name) {
            return v.clone();
        }
        return atom.clone();
    }

    if let Some((kind, l, r)) = atom.decompose_binary() {
        return T::recompose_binary(kind, metta_subst(l, bindings), metta_subst(r, bindings));
    }

    atom.clone()
}

/// True when a pattern subtree contains at least one pattern variable.
pub fn metta_pattern_contains_var<T>(atom: &T) -> bool
where
    T: MettaFamilyPattern,
{
    if atom.pattern_var_name().is_some() {
        return true;
    }
    if let Some((_, left, right)) = atom.decompose_binary() {
        return metta_pattern_contains_var(left) || metta_pattern_contains_var(right);
    }
    false
}

fn expr_head_and_arity<T>(atom: &T) -> Option<(&T, usize)>
where
    T: MettaFamilyListForm,
{
    let mut cur = atom;
    let mut head: Option<&T> = None;
    let mut arity = 0usize;
    loop {
        if cur.is_expr_nil() {
            return head.map(|h| (h, arity));
        }
        if let Some((h, t)) = cur.expr_cons_parts() {
            if head.is_none() {
                head = Some(h);
            }
            arity = arity.saturating_add(1);
            cur = t;
            continue;
        }
        return None;
    }
}

/// Shared index keying for rule-pattern LHS classification.
pub fn metta_pattern_index_key<T>(lhs: &T) -> PatternIndexKey<T>
where
    T: MettaFamilyListForm,
{
    if let Some((head, arity)) = expr_head_and_arity(lhs) {
        if head.pattern_var_name().is_some() {
            return PatternIndexKey::ListArityAny { arity };
        }
        return PatternIndexKey::ListHeadConst { arity, head: head.clone() };
    }

    if lhs.pattern_var_name().is_some() {
        PatternIndexKey::AtomAny
    } else {
        PatternIndexKey::AtomConst(lhs.clone())
    }
}

/// Shared index keying for query expression classification.
pub fn metta_query_index_key<T>(atom: &T) -> QueryIndexKey<T>
where
    T: MettaFamilyListForm,
{
    if let Some((head, arity)) = expr_head_and_arity(atom) {
        return QueryIndexKey::List {
            arity,
            head: if head.pattern_var_name().is_some() {
                None
            } else {
                Some(head.clone())
            },
        };
    }

    if atom.pattern_var_name().is_some() {
        QueryIndexKey::AtomOther
    } else {
        QueryIndexKey::AtomConst(atom.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        metta_match, metta_pattern_contains_var, metta_pattern_index_key, metta_query_index_key,
        metta_subst, MettaBinaryKind, MettaFamilyListForm, MettaFamilyPattern,
    };
    use crate::{PatternIndexKey, QueryIndexKey};
    use std::collections::HashMap;

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum T {
        Var(&'static str),
        Sym(&'static str),
        Cons(Box<T>, Box<T>),
        Eq(Box<T>, Box<T>),
        Nil,
    }

    impl MettaFamilyPattern for T {
        fn pattern_var_name(&self) -> Option<String> {
            match self {
                T::Var(v) => Some((*v).to_string()),
                _ => None,
            }
        }

        fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)> {
            match self {
                T::Cons(h, t) => Some((MettaBinaryKind::ExprCons, h, t)),
                T::Eq(l, r) => Some((MettaBinaryKind::EqAtom, l, r)),
                _ => None,
            }
        }

        fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self {
            match kind {
                MettaBinaryKind::ExprCons => T::Cons(Box::new(left), Box::new(right)),
                MettaBinaryKind::EqAtom => T::Eq(Box::new(left), Box::new(right)),
            }
        }
    }

    impl MettaFamilyListForm for T {
        fn expr_cons_parts(&self) -> Option<(&Self, &Self)> {
            match self {
                T::Cons(h, t) => Some((h, t)),
                _ => None,
            }
        }

        fn is_expr_nil(&self) -> bool {
            matches!(self, T::Nil)
        }
    }

    #[test]
    fn match_variable_consistency() {
        let pat = T::Cons(Box::new(T::Var("x")), Box::new(T::Var("x")));
        let ok = T::Cons(Box::new(T::Sym("a")), Box::new(T::Sym("a")));
        let bad = T::Cons(Box::new(T::Sym("a")), Box::new(T::Sym("b")));
        assert!(metta_match(&pat, &ok).is_some());
        assert!(metta_match(&pat, &bad).is_none());
    }

    #[test]
    fn subst_replaces_vars() {
        let atom = T::Eq(
            Box::new(T::Var("x")),
            Box::new(T::Cons(Box::new(T::Var("y")), Box::new(T::Sym("z")))),
        );
        let mut b = HashMap::new();
        b.insert("x".to_string(), T::Sym("left"));
        b.insert("y".to_string(), T::Sym("head"));
        let out = metta_subst(&atom, &b);
        let expected = T::Eq(
            Box::new(T::Sym("left")),
            Box::new(T::Cons(Box::new(T::Sym("head")), Box::new(T::Sym("z")))),
        );
        assert_eq!(out, expected);
    }

    #[test]
    fn pattern_key_helpers_work() {
        let pat_list = T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil));
        let pat_var_head = T::Cons(Box::new(T::Var("x")), Box::new(T::Nil));
        let pat_atom_var = T::Var("y");
        let query_list = T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil));

        assert!(!metta_pattern_contains_var(&pat_list));
        assert!(metta_pattern_contains_var(&pat_var_head));
        assert!(metta_pattern_contains_var(&pat_atom_var));

        assert_eq!(
            metta_pattern_index_key(&pat_list),
            PatternIndexKey::ListHeadConst { arity: 1, head: T::Sym("h") }
        );
        assert_eq!(
            metta_pattern_index_key(&pat_var_head),
            PatternIndexKey::ListArityAny { arity: 1 }
        );
        assert_eq!(metta_pattern_index_key(&pat_atom_var), PatternIndexKey::AtomAny);
        assert_eq!(
            metta_query_index_key(&query_list),
            QueryIndexKey::List { arity: 1, head: Some(T::Sym("h")) }
        );
    }
}
