//! Generic re-entrant memoization helper.
//!
//! This supports recursive evaluation scenarios where a key may be requested
//! while already being computed. Callers can treat that case explicitly
//! (typically as a cycle/in-progress guard).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Result of one memoized compute-or-fetch operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoComputeOutcome<V> {
    /// Value was already in cache.
    Hit(V),
    /// Value is currently being computed in an outer recursive call.
    InProgress,
    /// Value was computed now and stored.
    Stored(V),
    /// Computation produced no value to store.
    Empty,
}

/// Re-entrant memo store with in-progress tracking.
#[derive(Debug)]
pub struct ReentrantMemo<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    cache: RefCell<HashMap<K, V>>,
    in_progress: RefCell<HashSet<K>>,
}

impl<K, V> Clone for ReentrantMemo<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            cache: RefCell::new(self.cache.borrow().clone()),
            in_progress: RefCell::new(self.in_progress.borrow().clone()),
        }
    }
}

impl<K, V> Default for ReentrantMemo<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn default() -> Self {
        Self {
            cache: RefCell::new(HashMap::new()),
            in_progress: RefCell::new(HashSet::new()),
        }
    }
}

impl<K, V> ReentrantMemo<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    /// Try cache first; otherwise compute, store, and return the outcome.
    pub fn get_or_try_compute<F>(&self, key: K, compute: F) -> MemoComputeOutcome<V>
    where
        F: FnOnce() -> Option<V>,
    {
        if let Some(cached) = self.cache.borrow().get(&key).cloned() {
            return MemoComputeOutcome::Hit(cached);
        }
        if self.in_progress.borrow().contains(&key) {
            return MemoComputeOutcome::InProgress;
        }

        self.in_progress.borrow_mut().insert(key.clone());
        let computed = compute();
        self.in_progress.borrow_mut().remove(&key);

        match computed {
            Some(value) => {
                self.cache.borrow_mut().insert(key, value.clone());
                MemoComputeOutcome::Stored(value)
            },
            None => MemoComputeOutcome::Empty,
        }
    }

    /// Retain memoized keys matching `keep`.
    pub fn retain_keys<F>(&self, mut keep: F)
    where
        F: FnMut(&K) -> bool,
    {
        self.cache.borrow_mut().retain(|k, _| keep(k));
        self.in_progress.borrow_mut().retain(|k| keep(k));
    }
}
