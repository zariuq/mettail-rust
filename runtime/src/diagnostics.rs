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

const FLOAT_TOLERANCE: f64 = 1e-9;

/// Runtime audit payload for evidence-conservation checks.
///
/// This is intentionally numeric and backend-agnostic so any evaluator can
/// report:
/// - hallucination (conclusion mass > premise mass),
/// - monotonicity break (conclusion mass < previous mass),
/// - leakage budget violations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct EvidenceConservationAudit {
    pub premise_mass: f64,
    pub conclusion_mass: f64,
    pub previous_mass: Option<f64>,
    pub leakage: f64,
    pub leakage_ratio: Option<f64>,
    pub leakage_budget: Option<f64>,
    pub hallucination_detected: bool,
    pub monotonicity_violated: bool,
    pub leakage_budget_exceeded: bool,
}

/// Evaluate basic evidence-conservation invariants from numeric mass summaries.
pub fn evaluate_evidence_conservation(
    premise_mass: f64,
    conclusion_mass: f64,
    previous_mass: Option<f64>,
    leakage_budget: Option<f64>,
) -> EvidenceConservationAudit {
    let premise_mass = premise_mass.max(0.0);
    let conclusion_mass = conclusion_mass.max(0.0);
    let previous_mass = previous_mass.map(|v| v.max(0.0));
    let leakage_budget = leakage_budget.map(|v| v.max(0.0));

    let leakage = (premise_mass - conclusion_mass).max(0.0);
    let leakage_ratio = if premise_mass > FLOAT_TOLERANCE {
        Some(leakage / premise_mass)
    } else {
        None
    };
    let hallucination_detected = conclusion_mass > premise_mass + FLOAT_TOLERANCE;
    let monotonicity_violated = previous_mass
        .map(|prev| conclusion_mass + FLOAT_TOLERANCE < prev)
        .unwrap_or(false);
    let leakage_budget_exceeded = leakage_budget
        .map(|budget| leakage > budget + FLOAT_TOLERANCE)
        .unwrap_or(false);

    EvidenceConservationAudit {
        premise_mass,
        conclusion_mass,
        previous_mass,
        leakage,
        leakage_ratio,
        leakage_budget,
        hallucination_detected,
        monotonicity_violated,
        leakage_budget_exceeded,
    }
}

/// Runtime audit payload for non-commutative scheduling cost.
#[derive(Debug, Clone, PartialEq)]
pub struct ScheduleOrderCostAudit {
    pub transition_count: usize,
    pub total_order_cost: f64,
    pub total_swap_anomaly: f64,
    pub max_pair_cost: f64,
    pub order_sensitive_pairs: usize,
    pub unresolved_pairs: usize,
    pub budget: Option<f64>,
    pub budget_exceeded: bool,
}

/// Evaluate order-cost on one concrete schedule.
///
/// `pair_swap_defects[(a,b)]` is the cost of placing `a` before `b`.
/// The audit sums adjacent costs and tracks antisymmetric anomaly
/// `|cost(a,b) - cost(b,a)|` as a non-commutativity signal.
pub fn evaluate_schedule_order_cost(
    schedule: &[String],
    pair_swap_defects: &HashMap<(String, String), f64>,
    budget: Option<f64>,
) -> ScheduleOrderCostAudit {
    let budget = budget.map(|v| v.max(0.0));
    let mut total_order_cost = 0.0_f64;
    let mut total_swap_anomaly = 0.0_f64;
    let mut max_pair_cost = 0.0_f64;
    let mut order_sensitive_pairs = 0usize;
    let mut unresolved_pairs = 0usize;

    for pair in schedule.windows(2) {
        let a = &pair[0];
        let b = &pair[1];
        let forward = pair_swap_defects
            .get(&(a.clone(), b.clone()))
            .copied()
            .unwrap_or(0.0)
            .max(0.0);
        let reverse = pair_swap_defects
            .get(&(b.clone(), a.clone()))
            .copied()
            .unwrap_or(0.0)
            .max(0.0);

        if !pair_swap_defects.contains_key(&(a.clone(), b.clone())) {
            unresolved_pairs += 1;
        }

        total_order_cost += forward;
        total_swap_anomaly += (forward - reverse).abs();
        max_pair_cost = max_pair_cost.max(forward);
        if forward > FLOAT_TOLERANCE {
            order_sensitive_pairs += 1;
        }
    }

    let budget_exceeded = budget
        .map(|cap| total_order_cost > cap + FLOAT_TOLERANCE)
        .unwrap_or(false);

    ScheduleOrderCostAudit {
        transition_count: schedule.len().saturating_sub(1),
        total_order_cost,
        total_swap_anomaly,
        max_pair_cost,
        order_sensitive_pairs,
        unresolved_pairs,
        budget,
        budget_exceeded,
    }
}

/// Coarse overlap-topology kind for merge-safety policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OverlapTopologyKind {
    /// No overlap edges were observed.
    Empty,
    /// Overlap graph is acyclic (forest/tree-like).
    TreeLike,
    /// Overlap graph has at least one cycle.
    Cyclic,
}

/// Runtime audit payload for overlap-topology safety classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OverlapTopologyAudit {
    pub node_count: usize,
    pub edge_count: usize,
    pub component_count: usize,
    pub max_component_size: usize,
    pub has_cycle: bool,
    pub kind: OverlapTopologyKind,
}

impl OverlapTopologyAudit {
    /// Conservative merge strategy is recommended exactly when cycles are present.
    pub fn requires_conservative_overlap_merge(&self) -> bool {
        self.has_cycle
    }
}

/// Classify overlap graph shape from module-level overlap edges.
///
/// The graph is treated as undirected because overlap risk is symmetric.
pub fn classify_overlap_topology(
    nodes: &[String],
    overlap_edges: &[(String, String)],
) -> OverlapTopologyAudit {
    let mut index_of: HashMap<String, usize> = HashMap::new();
    let mut next_idx = 0usize;

    for n in nodes {
        index_of.entry(n.clone()).or_insert_with(|| {
            let idx = next_idx;
            next_idx += 1;
            idx
        });
    }
    for (a, b) in overlap_edges {
        index_of.entry(a.clone()).or_insert_with(|| {
            let idx = next_idx;
            next_idx += 1;
            idx
        });
        index_of.entry(b.clone()).or_insert_with(|| {
            let idx = next_idx;
            next_idx += 1;
            idx
        });
    }

    let node_count = index_of.len();
    let mut adjacency: Vec<HashSet<usize>> = vec![HashSet::new(); node_count];
    let mut edge_count = 0usize;
    let mut has_cycle = false;

    for (a, b) in overlap_edges {
        let Some(&ia) = index_of.get(a) else { continue };
        let Some(&ib) = index_of.get(b) else { continue };

        if ia == ib {
            has_cycle = true;
            continue;
        }
        if adjacency[ia].insert(ib) {
            adjacency[ib].insert(ia);
            edge_count += 1;
        }
    }

    let mut visited = vec![false; node_count];
    let mut component_count = 0usize;
    let mut max_component_size = 0usize;

    for start in 0..node_count {
        if visited[start] {
            continue;
        }
        component_count += 1;
        let mut stack: Vec<(usize, Option<usize>)> = vec![(start, None)];
        let mut comp_size = 0usize;

        while let Some((node, parent)) = stack.pop() {
            if visited[node] {
                continue;
            }
            visited[node] = true;
            comp_size += 1;

            for &nbr in &adjacency[node] {
                if !visited[nbr] {
                    stack.push((nbr, Some(node)));
                } else if Some(nbr) != parent {
                    has_cycle = true;
                }
            }
        }

        max_component_size = max_component_size.max(comp_size);
    }

    let kind = if edge_count == 0 {
        OverlapTopologyKind::Empty
    } else if has_cycle {
        OverlapTopologyKind::Cyclic
    } else {
        OverlapTopologyKind::TreeLike
    };

    OverlapTopologyAudit {
        node_count,
        edge_count,
        component_count,
        max_component_size,
        has_cycle,
        kind,
    }
}
