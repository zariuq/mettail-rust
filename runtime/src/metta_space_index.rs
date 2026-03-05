//! Shared MeTTa-family space index orchestration.
//!
//! This is the reusable engine-side container for lookup families used by
//! generated language helpers (equation/type lookup + memoized query results).

use crate::{
    metta_match, metta_query_index_key, metta_subst, HashEqCache, LookupFamilyIndex,
    MettaFamilyListForm, PatternIndexKey,
};
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, Mutex};

/// Shared cache wrapper for space-derived indexes keyed by space atom payload.
///
/// Language backends should use this instead of implementing custom
/// `HashEqCache + Mutex` plumbing in each backend file.
#[derive(Debug)]
pub struct MettaFamilySpaceIndexCache<A, I>
where
    A: Clone + Eq + Hash,
{
    by_atoms: Mutex<HashEqCache<A, Arc<I>>>,
}

impl<A, I> Default for MettaFamilySpaceIndexCache<A, I>
where
    A: Clone + Eq + Hash,
{
    fn default() -> Self {
        Self {
            by_atoms: Mutex::new(HashEqCache::default()),
        }
    }
}

impl<A, I> MettaFamilySpaceIndexCache<A, I>
where
    A: Clone + Eq + Hash,
{
    /// Return cached index for `atoms` or build/store it once.
    ///
    /// The builder may run more than once under races, but only one value is
    /// retained in the cache.
    pub fn get_or_build_with<F>(&self, atoms: &A, build: F) -> Arc<I>
    where
        F: FnOnce(&A) -> I,
    {
        if let Some(hit) = self
            .by_atoms
            .lock()
            .ok()
            .and_then(|guard| guard.get(atoms))
        {
            return hit;
        }

        let built = Arc::new(build(atoms));
        let mut guard = self
            .by_atoms
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        if let Some(hit) = guard.get(atoms) {
            return hit;
        }
        guard.insert(atoms.clone(), Arc::clone(&built));
        built
    }
}

/// One equation entry prepared for indexing.
#[derive(Debug, Clone)]
pub struct MettaEqEntry<A>
where
    A: Clone + Eq + Hash,
{
    pub lhs: A,
    pub rhs: A,
    pub has_pattern_var: bool,
    pub pattern_key: PatternIndexKey<A>,
}

/// One type entry prepared for indexing.
#[derive(Debug, Clone)]
pub struct MettaTypeEntry<A>
where
    A: Clone + Eq + Hash,
{
    pub atom: A,
    pub ty: A,
    /// Packed applicable function-type payload for this head (if function type).
    pub applicable_func_type: Option<A>,
    /// True iff this type is explicitly non-function.
    pub non_func_type: bool,
}

/// Shared lookup index + caches for one space value.
#[derive(Debug)]
pub struct MettaFamilySpaceIndex<A>
where
    A: Clone + Eq + Hash,
{
    pub equation_lookup: LookupFamilyIndex<A, A, (A, A)>,
    pub type_lookup: LookupFamilyIndex<A, A, A>,
    pub first_applicable_func_type_by_op: HashMap<A, A>,
    pub first_non_func_type_by_op: HashMap<A, A>,
    pub equation_query_memo: Arc<Mutex<HashEqCache<A, Arc<Vec<A>>>>>,
}

/// Lazy equation-query result stream.
///
/// - If results are already memoized, iterates cached values.
/// - Otherwise iterates exact + pattern paths lazily and memoizes once exhausted.
#[derive(Debug, Clone)]
pub struct MettaEqMatches<A>
where
    A: Clone + Eq + Hash,
{
    cached: Option<Arc<Vec<A>>>,
    query: A,
    exact_values: Vec<A>,
    pattern_candidates: Vec<(A, A)>,
    memo: Option<Arc<Mutex<HashEqCache<A, Arc<Vec<A>>>>>>,
}

impl<A> MettaEqMatches<A>
where
    A: Clone + Eq + Hash,
{
    pub fn empty(query: A) -> Self {
        Self {
            cached: Some(Arc::new(Vec::new())),
            query,
            exact_values: Vec::new(),
            pattern_candidates: Vec::new(),
            memo: None,
        }
    }
}

pub struct MettaEqMatchesIter<A>
where
    A: MettaFamilyListForm,
{
    cached: Option<std::vec::IntoIter<A>>,
    query: A,
    exact_iter: std::vec::IntoIter<A>,
    pattern_iter: std::vec::IntoIter<(A, A)>,
    emitted: Vec<A>,
    memo: Option<Arc<Mutex<HashEqCache<A, Arc<Vec<A>>>>>>,
    finalized: bool,
}

impl<A> MettaEqMatchesIter<A>
where
    A: MettaFamilyListForm,
{
    fn finalize_if_needed(&mut self) {
        if self.finalized {
            return;
        }
        self.finalized = true;
        let Some(memo) = self.memo.take() else {
            return;
        };
        let built = Arc::new(self.emitted.clone());
        let mut guard = memo.lock().unwrap_or_else(|poison| poison.into_inner());
        if guard.get(&self.query).is_none() {
            guard.insert(self.query.clone(), built);
        }
    }
}

impl<A> Iterator for MettaEqMatchesIter<A>
where
    A: MettaFamilyListForm,
{
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut cached) = self.cached {
            return cached.next();
        }
        if let Some(next_exact) = self.exact_iter.next() {
            self.emitted.push(next_exact.clone());
            return Some(next_exact);
        }
        while let Some((lhs, rhs)) = self.pattern_iter.next() {
            if let Some(bindings) = metta_match(&lhs, &self.query) {
                let next_match = metta_subst(&rhs, &bindings);
                self.emitted.push(next_match.clone());
                return Some(next_match);
            }
        }
        self.finalize_if_needed();
        None
    }
}

impl<A> IntoIterator for MettaEqMatches<A>
where
    A: MettaFamilyListForm,
{
    type Item = A;
    type IntoIter = MettaEqMatchesIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        let cached = self
            .cached
            .map(|values| values.as_ref().clone().into_iter());
        MettaEqMatchesIter {
            cached,
            query: self.query,
            exact_iter: self.exact_values.into_iter(),
            pattern_iter: self.pattern_candidates.into_iter(),
            emitted: Vec::new(),
            memo: self.memo,
            finalized: false,
        }
    }
}

impl<A> MettaFamilySpaceIndex<A>
where
    A: Clone + Eq + Hash,
{
    /// Build all lookup-family maps from extracted equation/type entries.
    pub fn from_entries(
        eq_entries: Vec<MettaEqEntry<A>>,
        ty_entries: Vec<MettaTypeEntry<A>>,
    ) -> Self {
        let mut exact_equation_rhs: HashMap<A, Vec<A>> = HashMap::new();
        let mut equation_pattern_entries: Vec<(PatternIndexKey<A>, (A, A))> = Vec::new();
        for entry in eq_entries {
            if entry.has_pattern_var {
                equation_pattern_entries.push((entry.pattern_key, (entry.lhs, entry.rhs)));
            } else {
                exact_equation_rhs
                    .entry(entry.lhs)
                    .or_default()
                    .push(entry.rhs);
            }
        }

        let mut type_exact_values: HashMap<A, Vec<A>> = HashMap::new();
        let mut first_applicable_func_type_by_op: HashMap<A, A> = HashMap::new();
        let mut first_non_func_type_by_op: HashMap<A, A> = HashMap::new();
        for entry in ty_entries {
            type_exact_values
                .entry(entry.atom.clone())
                .or_default()
                .push(entry.ty.clone());
            if let Some(payload) = entry.applicable_func_type {
                first_applicable_func_type_by_op
                    .entry(entry.atom.clone())
                    .or_insert(payload);
            }
            if entry.non_func_type {
                first_non_func_type_by_op
                    .entry(entry.atom)
                    .or_insert(entry.ty);
            }
        }

        Self {
            equation_lookup: LookupFamilyIndex::from_parts(
                exact_equation_rhs,
                equation_pattern_entries,
            ),
            type_lookup: LookupFamilyIndex::from_parts(type_exact_values, Vec::new()),
            first_applicable_func_type_by_op,
            first_non_func_type_by_op,
            equation_query_memo: Arc::new(Mutex::new(HashEqCache::default())),
        }
    }
}

impl<A> MettaFamilySpaceIndex<A>
where
    A: MettaFamilyListForm,
{
    /// Return equation-query results for `atom` using exact and pattern paths.
    ///
    /// Results are memoized by query atom to avoid repeated match/subst work
    /// across related premise checks in one run.
    pub fn query_equation_results(&self, atom: &A) -> Arc<Vec<A>> {
        if let Some(hit) = self
            .equation_query_memo
            .lock()
            .ok()
            .and_then(|memo| memo.get(atom))
        {
            return hit;
        }

        let mut results = self
            .equation_lookup
            .exact_values(atom)
            .map_or_else(Vec::new, |vals| vals.to_vec());
        for (lhs, rhs) in self
            .equation_lookup
            .pattern_candidates(metta_query_index_key(atom))
        {
            if let Some(bindings) = metta_match(lhs, atom) {
                results.push(metta_subst(rhs, &bindings));
            }
        }

        let built = Arc::new(results);
        let mut memo = self
            .equation_query_memo
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        if let Some(hit) = memo.get(atom) {
            return hit;
        }
        memo.insert(atom.clone(), Arc::clone(&built));
        built
    }

    /// Return equation-query matches as a lazy stream.
    ///
    /// This enables cheap existence checks (`next().is_none()`) without forcing
    /// full materialization on cache miss, while still memoizing fully consumed
    /// queries for reuse.
    pub fn equation_matches(&self, atom: &A) -> MettaEqMatches<A> {
        if let Some(hit) = self
            .equation_query_memo
            .lock()
            .ok()
            .and_then(|memo| memo.get(atom))
        {
            return MettaEqMatches {
                cached: Some(hit),
                query: atom.clone(),
                exact_values: Vec::new(),
                pattern_candidates: Vec::new(),
                memo: None,
            };
        }

        let exact_values = self
            .equation_lookup
            .exact_values(atom)
            .map_or_else(Vec::new, |vals| vals.to_vec());
        let pattern_candidates = self
            .equation_lookup
            .pattern_candidates(metta_query_index_key(atom))
            .into_iter()
            .map(|(lhs, rhs)| (lhs.clone(), rhs.clone()))
            .collect();
        MettaEqMatches {
            cached: None,
            query: atom.clone(),
            exact_values,
            pattern_candidates,
            memo: Some(Arc::clone(&self.equation_query_memo)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{MettaEqEntry, MettaFamilySpaceIndex, MettaFamilySpaceIndexCache, MettaTypeEntry};
    use crate::{MettaBinaryKind, MettaFamilyListForm, MettaFamilyPattern, PatternIndexKey};

    #[test]
    fn builds_exact_pattern_and_type_maps() {
        let index = MettaFamilySpaceIndex::from_entries(
            vec![
                MettaEqEntry {
                    lhs: "a",
                    rhs: "b",
                    has_pattern_var: false,
                    pattern_key: PatternIndexKey::AtomConst("a"),
                },
                MettaEqEntry {
                    lhs: "x",
                    rhs: "y",
                    has_pattern_var: true,
                    pattern_key: PatternIndexKey::AtomAny,
                },
            ],
            vec![
                MettaTypeEntry {
                    atom: "f",
                    ty: "T1",
                    applicable_func_type: Some("pack"),
                    non_func_type: false,
                },
                MettaTypeEntry {
                    atom: "f",
                    ty: "T2",
                    applicable_func_type: None,
                    non_func_type: true,
                },
            ],
        );
        assert!(index.equation_lookup.has_exact(&"a"));
        assert_eq!(index.type_lookup.exact_values(&"f").map(|v| v.len()), Some(2));
        assert_eq!(index.first_applicable_func_type_by_op.get(&"f"), Some(&"pack"));
        assert_eq!(index.first_non_func_type_by_op.get(&"f"), Some(&"T2"));
    }

    #[test]
    fn shared_cache_builds_once_per_key() {
        let cache: MettaFamilySpaceIndexCache<&'static str, usize> = Default::default();
        let built_a = cache.get_or_build_with(&"A", |_| 7);
        let built_a_again = cache.get_or_build_with(&"A", |_| 11);
        let built_b = cache.get_or_build_with(&"B", |_| 3);
        assert_eq!(*built_a, 7);
        assert_eq!(*built_a_again, 7);
        assert_eq!(*built_b, 3);
    }

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
    fn query_equation_results_exact_and_pattern() {
        let index = MettaFamilySpaceIndex::from_entries(
            vec![
                MettaEqEntry {
                    lhs: T::Sym("a"),
                    rhs: T::Sym("exact"),
                    has_pattern_var: false,
                    pattern_key: PatternIndexKey::AtomConst(T::Sym("a")),
                },
                MettaEqEntry {
                    lhs: T::Cons(
                        Box::new(T::Sym("h")),
                        Box::new(T::Cons(Box::new(T::Var("x")), Box::new(T::Nil))),
                    ),
                    rhs: T::Var("x"),
                    has_pattern_var: true,
                    pattern_key: PatternIndexKey::ListHeadConst { arity: 2, head: T::Sym("h") },
                },
            ],
            Vec::new(),
        );

        let exact = index.query_equation_results(&T::Sym("a"));
        assert_eq!(exact.as_ref(), &vec![T::Sym("exact")]);

        let list_query = T::Cons(
            Box::new(T::Sym("h")),
            Box::new(T::Cons(Box::new(T::Sym("payload")), Box::new(T::Nil))),
        );
        let matched = index.query_equation_results(&list_query);
        assert_eq!(matched.as_ref(), &vec![T::Sym("payload")]);
    }

    #[test]
    fn equation_matches_iter_is_lazy_and_memoizes_on_exhaustion() {
        let index = MettaFamilySpaceIndex::from_entries(
            vec![MettaEqEntry {
                lhs: T::Cons(
                    Box::new(T::Sym("h")),
                    Box::new(T::Cons(Box::new(T::Var("x")), Box::new(T::Nil))),
                ),
                rhs: T::Var("x"),
                has_pattern_var: true,
                pattern_key: PatternIndexKey::ListHeadConst { arity: 2, head: T::Sym("h") },
            }],
            Vec::new(),
        );

        let list_query = T::Cons(
            Box::new(T::Sym("h")),
            Box::new(T::Cons(Box::new(T::Sym("payload")), Box::new(T::Nil))),
        );
        let mut iter = index.equation_matches(&list_query).into_iter();
        assert_eq!(iter.next(), Some(T::Sym("payload")));
        assert_eq!(iter.next(), None);

        // Exhausting the iterator should populate memo for this query.
        let cached = index.query_equation_results(&list_query);
        assert_eq!(cached.as_ref(), &vec![T::Sym("payload")]);

        let mut miss_iter = index.equation_matches(&T::Sym("absent")).into_iter();
        assert_eq!(miss_iter.next(), None);
        let miss_cached = index.query_equation_results(&T::Sym("absent"));
        assert!(miss_cached.is_empty());
    }
}
