//! Runtime-agnostic execution diagnostics.
//!
//! These counters are intentionally backend/language neutral. Specific runtimes
//! can define adapter aliases (for example `SurfaceEvalDiagnostics`) without
//! re-defining the payload shape.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::AscentResults;

/// Rewrite/fixpoint diagnostics for one evaluation request.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RewriteEvalDiagnostics {
    pub steps: usize,
    pub frontier_terms: usize,
    pub max_frontier: usize,
    pub rewrite_calls: usize,
    pub cache_hits: usize,
    pub cache_misses: usize,
    pub candidate_rules: usize,
    pub rule_checks: usize,
    pub rule_matches: usize,
    pub child_rewrites: usize,
    pub ground_rewrites: usize,
    pub memo_hits: usize,
    pub memo_misses: usize,
    pub memo_stores: usize,
    pub memo_in_progress_blocks: usize,
    pub truncated_by_branch_cap: usize,
    pub truncated_by_outcome_cap: bool,
    pub hit_step_cap: bool,
    pub normal_forms: usize,
    pub elapsed_ms: f64,
}

/// Core fixpoint-evaluation diagnostics derived from `AscentResults`.
#[derive(Debug, Clone)]
pub struct CoreEvalDiagnostics {
    pub mode: String,
    pub elapsed_ms: f64,
    pub term_count: usize,
    pub rewrite_count: usize,
    pub normal_form_count: usize,
    pub root_out_degree: usize,
    pub max_out_degree: usize,
    pub avg_out_degree: f64,
    pub p95_out_degree: usize,
    pub reachable_term_count: usize,
    pub reachable_rewrite_count: usize,
    pub relation_cardinalities: Vec<(String, usize)>,
    pub relation_extract_total_ms: f64,
    pub relation_timings_ms: Vec<(String, f64)>,
    pub core_phase_total_ms: f64,
    pub core_phase_timings_ms: Vec<(String, f64)>,
}

/// Build one diagnostics record from a single core evaluation run.
pub fn build_core_eval_diagnostics(
    results: &AscentResults,
    initial_id: u64,
    elapsed_ms: f64,
    mode: &str,
) -> CoreEvalDiagnostics {
    let mut out_degree: HashMap<u64, usize> = HashMap::new();
    let mut adjacency: HashMap<u64, Vec<u64>> = HashMap::new();
    for rw in &results.rewrites {
        *out_degree.entry(rw.from_id).or_insert(0) += 1;
        adjacency.entry(rw.from_id).or_default().push(rw.to_id);
    }

    let root_out_degree = out_degree.get(&initial_id).copied().unwrap_or(0);
    let max_out_degree = out_degree.values().copied().max().unwrap_or(0);
    let out_degrees: Vec<usize> = out_degree.values().copied().collect();
    let avg_out_degree = if out_degrees.is_empty() {
        0.0
    } else {
        out_degrees.iter().sum::<usize>() as f64 / out_degrees.len() as f64
    };
    let p95_out_degree = if out_degrees.is_empty() {
        0
    } else {
        let mut ordered = out_degrees.clone();
        ordered.sort_unstable();
        let idx = (((ordered.len() as f64) * 0.95).ceil() as usize).saturating_sub(1);
        ordered[idx.min(ordered.len().saturating_sub(1))]
    };

    let mut reachable_terms: HashSet<u64> = HashSet::new();
    let mut queue: VecDeque<u64> = VecDeque::new();
    reachable_terms.insert(initial_id);
    queue.push_back(initial_id);
    let mut reachable_rewrite_count = 0usize;
    while let Some(cur) = queue.pop_front() {
        if let Some(next_ids) = adjacency.get(&cur) {
            reachable_rewrite_count += next_ids.len();
            for next in next_ids {
                if reachable_terms.insert(*next) {
                    queue.push_back(*next);
                }
            }
        }
    }

    let mut relation_cardinalities: Vec<(String, usize)> = results
        .custom_relations
        .iter()
        .map(|(name, data)| (name.clone(), data.tuples.len()))
        .collect();
    relation_cardinalities.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut relation_timings_ms: Vec<(String, f64)> = results
        .relation_timings_ms
        .iter()
        .map(|(name, elapsed_ms)| (name.clone(), *elapsed_ms))
        .collect();
    relation_timings_ms.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let relation_extract_total_ms = relation_timings_ms.iter().map(|(_, ms)| *ms).sum::<f64>();

    let mut core_phase_timings_ms: Vec<(String, f64)> = results
        .phase_timings_ms
        .iter()
        .map(|(name, elapsed_ms)| (name.clone(), *elapsed_ms))
        .collect();
    core_phase_timings_ms.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let core_phase_total_ms = core_phase_timings_ms.iter().map(|(_, ms)| *ms).sum::<f64>();

    CoreEvalDiagnostics {
        mode: mode.to_string(),
        elapsed_ms,
        term_count: results.all_terms.len(),
        rewrite_count: results.rewrites.len(),
        normal_form_count: results.normal_forms().len(),
        root_out_degree,
        max_out_degree,
        avg_out_degree,
        p95_out_degree,
        reachable_term_count: reachable_terms.len(),
        reachable_rewrite_count,
        relation_cardinalities,
        relation_extract_total_ms,
        relation_timings_ms,
        core_phase_total_ms,
        core_phase_timings_ms,
    }
}

/// Aggregate branch-level diagnostics into one summary record.
pub fn aggregate_core_eval_diagnostics(
    diagnostics: &[CoreEvalDiagnostics],
) -> Option<CoreEvalDiagnostics> {
    let first = diagnostics.first()?.clone();
    if diagnostics.len() == 1 {
        return Some(first);
    }

    let mut relation_counts: HashMap<String, usize> = HashMap::new();
    let mut relation_timing_sums: HashMap<String, f64> = HashMap::new();
    let mut core_phase_timing_sums: HashMap<String, f64> = HashMap::new();
    let mut elapsed_ms = 0.0_f64;
    let mut term_count = 0usize;
    let mut rewrite_count = 0usize;
    let mut normal_form_count = 0usize;
    let mut root_out_degree = 0usize;
    let mut max_out_degree = 0usize;
    let mut avg_out_degree = 0.0_f64;
    let mut p95_out_degree = 0usize;
    let mut reachable_term_count = 0usize;
    let mut reachable_rewrite_count = 0usize;
    let mut relation_extract_total_ms = 0.0_f64;
    let mut core_phase_total_ms = 0.0_f64;

    for diag in diagnostics {
        elapsed_ms += diag.elapsed_ms;
        term_count += diag.term_count;
        rewrite_count += diag.rewrite_count;
        normal_form_count += diag.normal_form_count;
        root_out_degree += diag.root_out_degree;
        max_out_degree = max_out_degree.max(diag.max_out_degree);
        avg_out_degree += diag.avg_out_degree;
        p95_out_degree = p95_out_degree.max(diag.p95_out_degree);
        reachable_term_count += diag.reachable_term_count;
        reachable_rewrite_count += diag.reachable_rewrite_count;
        relation_extract_total_ms += diag.relation_extract_total_ms;
        core_phase_total_ms += diag.core_phase_total_ms;
        for (name, count) in &diag.relation_cardinalities {
            *relation_counts.entry(name.clone()).or_insert(0) += count;
        }
        for (name, elapsed_ms) in &diag.relation_timings_ms {
            *relation_timing_sums.entry(name.clone()).or_insert(0.0) += *elapsed_ms;
        }
        for (name, elapsed_ms) in &diag.core_phase_timings_ms {
            *core_phase_timing_sums.entry(name.clone()).or_insert(0.0) += *elapsed_ms;
        }
    }

    let mut relation_cardinalities: Vec<(String, usize)> = relation_counts.into_iter().collect();
    relation_cardinalities.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut relation_timings_ms: Vec<(String, f64)> = relation_timing_sums.into_iter().collect();
    relation_timings_ms.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let mut core_phase_timings_ms: Vec<(String, f64)> =
        core_phase_timing_sums.into_iter().collect();
    core_phase_timings_ms.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    Some(CoreEvalDiagnostics {
        mode: "multi-branch".to_string(),
        elapsed_ms,
        term_count,
        rewrite_count,
        normal_form_count,
        root_out_degree,
        max_out_degree,
        avg_out_degree: avg_out_degree / diagnostics.len() as f64,
        p95_out_degree,
        reachable_term_count,
        reachable_rewrite_count,
        relation_cardinalities,
        relation_extract_total_ms,
        relation_timings_ms,
        core_phase_total_ms,
        core_phase_timings_ms,
    })
}
