//! Generic frontier-based rewrite search utilities.
//!
//! This module is language-agnostic: callers provide one-step expansion for
//! their term/state type, and the runtime handles bounded frontier traversal,
//! deduplication, and truncation accounting.

use std::collections::HashSet;
use std::hash::Hash;

use crate::RewriteLimits;

/// Generic frontier traversal counters.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FrontierSearchStats {
    pub steps: usize,
    pub frontier_terms: usize,
    pub max_frontier: usize,
    pub truncated_by_branch_cap: usize,
    pub truncated_by_outcome_cap: bool,
    pub hit_step_cap: bool,
    pub normal_forms: usize,
}

/// Output of one bounded frontier search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontierSearchOutcome<T> {
    pub normal_forms: Vec<T>,
    pub stats: FrontierSearchStats,
}

/// Deduplicate while preserving first-seen order.
pub fn dedup_stable<T>(items: Vec<T>) -> Vec<T>
where
    T: Clone + Eq + Hash,
{
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for item in items {
        if seen.insert(item.clone()) {
            out.push(item);
        }
    }
    out
}

/// Explore a rewrite/search frontier under `RewriteLimits`.
///
/// `expand_once` returns direct successors for one element. If the returned
/// vector is empty, the element is treated as a normal form.
pub fn explore_rewrite_frontier<T, F>(
    initial: T,
    limits: RewriteLimits,
    mut expand_once: F,
) -> FrontierSearchOutcome<T>
where
    T: Clone + Eq + Hash,
    F: FnMut(&T) -> Vec<T>,
{
    let mut stats = FrontierSearchStats::default();
    let mut frontier = vec![initial];
    let mut normal_forms = Vec::new();

    for step in 0..limits.max_steps {
        stats.steps = step + 1;
        if frontier.is_empty() {
            let mut out = dedup_stable(normal_forms);
            if out.len() > limits.max_outcomes {
                out.truncate(limits.max_outcomes);
                stats.truncated_by_outcome_cap = true;
            }
            stats.normal_forms = out.len();
            return FrontierSearchOutcome { normal_forms: out, stats };
        }

        stats.frontier_terms += frontier.len();
        stats.max_frontier = stats.max_frontier.max(frontier.len());

        let mut next_frontier = Vec::new();
        for cur in frontier {
            let next = expand_once(&cur);
            if next.is_empty() {
                normal_forms.push(cur);
            } else {
                next_frontier.extend(next);
            }
        }

        normal_forms = dedup_stable(normal_forms);
        next_frontier = dedup_stable(next_frontier);
        if normal_forms.len() + next_frontier.len() > limits.max_branches {
            let keep = limits.max_branches.saturating_sub(normal_forms.len());
            stats.truncated_by_branch_cap += next_frontier.len().saturating_sub(keep);
            next_frontier.truncate(keep);
        }
        frontier = next_frontier;
    }

    stats.hit_step_cap = true;
    normal_forms.extend(frontier);
    let mut out = dedup_stable(normal_forms);
    if out.len() > limits.max_outcomes {
        out.truncate(limits.max_outcomes);
        stats.truncated_by_outcome_cap = true;
    }
    stats.normal_forms = out.len();
    FrontierSearchOutcome { normal_forms: out, stats }
}
