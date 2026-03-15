use anyhow::Result;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::lookup_plan::LookupRelationMetadata;
use crate::metta_surface::{SExpr, SurfaceStmt};
use mettail_languages::metta_file as shared_metta_file;
pub use mettail_languages::metta_file::{
    BatchCaptureAssignment, ExpandedMettaLine, ImportEdge, ImportExpansionMeta,
    DEFAULT_BATCH_SPACE_IDENT,
};
use mettail_runtime::{
    CoreEvalDiagnostics, RewriteEvalDiagnostics as SurfaceEvalDiagnostics, RuntimeDispatchContracts,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunReportMode {
    Text,
    Json,
    Jsonl,
}

#[derive(Debug, Clone)]
pub struct RunMettaFileEntry {
    pub line: usize,
    pub input: String,
    pub status: &'static str,
    pub error: Option<String>,
    pub surface_results: Option<Vec<String>>,
    pub expected_surface: Option<Vec<String>>,
    pub elapsed_ms: Option<f64>,
    pub source_file: Option<String>,
    pub source_line: Option<usize>,
    pub binding_name: Option<String>,
    pub binding_value: Option<String>,
    pub surface_diagnostics: Option<SurfaceEvalDiagnostics>,
    pub core_diagnostics: Option<CoreEvalDiagnostics>,
}

#[derive(Debug, Clone)]
pub struct BatchBindingEvent {
    pub name: String,
    pub value: String,
    pub expanded_line: usize,
    pub source_file: String,
    pub source_line: usize,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct RuntimeImportStats {
    pub directives_executed: usize,
    pub injected_lines: usize,
}

pub fn runtime_import_stats_consistent(stats: RuntimeImportStats) -> bool {
    stats.directives_executed == 0 || stats.injected_lines > 0
}

#[derive(Debug, Clone, Copy, Default)]
struct RunMettaFileSummaryStats {
    total_entries: usize,
    lines_with_expectations: usize,
    expectation_failures: usize,
    assertion_mismatch_failures: usize,
    command_failures: usize,
}

fn summarize_run_metta_file_entries(entries: &[RunMettaFileEntry]) -> RunMettaFileSummaryStats {
    let mut stats = RunMettaFileSummaryStats {
        total_entries: entries.len(),
        ..RunMettaFileSummaryStats::default()
    };
    for entry in entries {
        if entry.expected_surface.is_some() {
            stats.lines_with_expectations += 1;
        }
        if entry.status != "fail" {
            continue;
        }
        if entry.expected_surface.is_some() {
            stats.expectation_failures += 1;
        }
        let is_assertion = entry
            .error
            .as_deref()
            .is_some_and(|e| e.starts_with("surface assertion mismatch:"));
        if is_assertion {
            stats.assertion_mismatch_failures += 1;
        } else {
            stats.command_failures += 1;
        }
    }
    stats
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn json_string_array(items: &[String]) -> String {
    items
        .iter()
        .map(|s| format!("\"{}\"", json_escape(s)))
        .collect::<Vec<_>>()
        .join(",")
}

fn relation_cardinalities_json(
    items: &[(String, usize)],
    lookup_relation_metadata: Option<&HashMap<String, LookupRelationMetadata>>,
) -> String {
    items
        .iter()
        .map(|(name, card)| {
            let mut row = format!("{{\"name\":\"{}\",\"count\":{}", json_escape(name), card);
            if let Some(meta) = lookup_relation_metadata.and_then(|m| m.get(name)) {
                row.push_str(&format!(
                    ",\"logical_relation_id\":\"{}\",\"scope_signature\":\"{}\"",
                    json_escape(&meta.logical_relation_id),
                    json_escape(&meta.scope_signature)
                ));
                if let Some(kind) = &meta.usage_kind {
                    row.push_str(&format!(",\"usage_kind\":\"{}\"", json_escape(kind)));
                }
            }
            row.push('}');
            row
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn relation_timings_json(
    items: &[(String, f64)],
    lookup_relation_metadata: Option<&HashMap<String, LookupRelationMetadata>>,
) -> String {
    items
        .iter()
        .map(|(name, elapsed_ms)| {
            let mut row =
                format!("{{\"name\":\"{}\",\"elapsed_ms\":{:.3}", json_escape(name), elapsed_ms);
            if let Some(meta) = lookup_relation_metadata.and_then(|m| m.get(name)) {
                row.push_str(&format!(
                    ",\"logical_relation_id\":\"{}\",\"scope_signature\":\"{}\"",
                    json_escape(&meta.logical_relation_id),
                    json_escape(&meta.scope_signature)
                ));
                if let Some(kind) = &meta.usage_kind {
                    row.push_str(&format!(",\"usage_kind\":\"{}\"", json_escape(kind)));
                }
            }
            row.push('}');
            row
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn surface_diagnostics_json(diag: &SurfaceEvalDiagnostics) -> String {
    format!(
        "\"steps\":{},\"frontier_terms\":{},\"max_frontier\":{},\"rewrite_calls\":{},\"cache_hits\":{},\"cache_misses\":{},\"candidate_rules\":{},\"rule_checks\":{},\"rule_matches\":{},\"child_rewrites\":{},\"ground_rewrites\":{},\"memo_hits\":{},\"memo_misses\":{},\"memo_stores\":{},\"memo_in_progress_blocks\":{},\"truncated_by_branch_cap\":{},\"truncated_by_outcome_cap\":{},\"hit_step_cap\":{},\"normal_forms\":{},\"elapsed_ms\":{:.3}",
        diag.steps,
        diag.frontier_terms,
        diag.max_frontier,
        diag.rewrite_calls,
        diag.cache_hits,
        diag.cache_misses,
        diag.candidate_rules,
        diag.rule_checks,
        diag.rule_matches,
        diag.child_rewrites,
        diag.ground_rewrites,
        diag.memo_hits,
        diag.memo_misses,
        diag.memo_stores,
        diag.memo_in_progress_blocks,
        diag.truncated_by_branch_cap,
        if diag.truncated_by_outcome_cap { "true" } else { "false" },
        if diag.hit_step_cap { "true" } else { "false" },
        diag.normal_forms,
        diag.elapsed_ms
    )
}

pub fn run_metta_file_report_json(
    file_path: &str,
    passed: usize,
    failed: usize,
    skipped: usize,
    entries: &[RunMettaFileEntry],
    import_meta: &ImportExpansionMeta,
    binding_events: &[BatchBindingEvent],
    runtime_imports: RuntimeImportStats,
    surface_policy: &str,
    dispatch_contracts: RuntimeDispatchContracts,
    lookup_relation_metadata: Option<&HashMap<String, LookupRelationMetadata>>,
) -> String {
    let stats = summarize_run_metta_file_entries(entries);
    let mut out = String::new();
    out.push('{');
    out.push_str("\"command\":\"run-metta-file\",");
    out.push_str(&format!("\"file\":\"{}\",", json_escape(file_path)));
    out.push_str(&format!("\"passed\":{passed},\"failed\":{failed},\"skipped\":{skipped},"));
    out.push_str(&format!("\"total_entries\":{},", stats.total_entries));
    out.push_str(&format!("\"lines_with_expectations\":{},", stats.lines_with_expectations));
    out.push_str(&format!("\"expectation_failures\":{},", stats.expectation_failures));
    out.push_str(&format!(
        "\"assertion_mismatch_failures\":{},",
        stats.assertion_mismatch_failures
    ));
    out.push_str(&format!("\"command_failures\":{},", stats.command_failures));
    out.push_str(&format!("\"surface_policy\":\"{}\",", json_escape(surface_policy)));
    out.push_str("\"dispatch_contracts\":{");
    out.push_str(&format!(
        "\"deterministic_reduction\":{},\"memoization_safe\":{},\"specialization_safe\":{},\"core_ground_eval_safe\":{}",
        if dispatch_contracts.deterministic_reduction { "true" } else { "false" },
        if dispatch_contracts.memoization_safe { "true" } else { "false" },
        if dispatch_contracts.specialization_safe { "true" } else { "false" },
        if dispatch_contracts.core_ground_eval_safe { "true" } else { "false" }
    ));
    out.push_str("},");
    out.push_str("\"imports\":{");
    out.push_str(&format!(
        "\"directives_seen\":{},\"non_self_directives\":{},\"expanded_lines\":{},\"skipped_cycles\":{},\"edge_count\":{},",
        import_meta.directives_seen,
        import_meta.non_self_directives,
        import_meta.expanded_lines,
        import_meta.skipped_cycles,
        import_meta.import_edges.len()
    ));
    out.push_str("\"target_spaces\":[");
    let mut target_spaces: Vec<String> = import_meta.target_spaces.iter().cloned().collect();
    target_spaces.sort();
    for (sidx, space) in target_spaces.iter().enumerate() {
        if sidx > 0 {
            out.push(',');
        }
        out.push('"');
        out.push_str(&json_escape(space));
        out.push('"');
    }
    out.push_str("],");
    out.push_str("\"imported_files\":[");
    let mut imported_files: Vec<String> = import_meta.imported_files.iter().cloned().collect();
    imported_files.sort();
    for (fidx, path) in imported_files.iter().enumerate() {
        if fidx > 0 {
            out.push(',');
        }
        out.push('"');
        out.push_str(&json_escape(path));
        out.push('"');
    }
    out.push_str("],");
    out.push_str("\"edges\":[");
    for (eidx, edge) in import_meta.import_edges.iter().enumerate() {
        if eidx > 0 {
            out.push(',');
        }
        out.push('{');
        out.push_str(&format!(
            "\"source_file\":\"{}\",\"source_line\":{},\"import_path\":\"{}\",\"source_space\":\"{}\",\"effective_space\":\"{}\",\"target_file\":\"{}\",\"skipped_cycle\":{},\"cycle_chain\":[{}]",
            json_escape(&edge.source_file),
            edge.source_line,
            json_escape(&edge.import_path),
            json_escape(&edge.source_space),
            json_escape(&edge.effective_space),
            json_escape(&edge.target_file),
            if edge.skipped_cycle { "true" } else { "false" },
            json_string_array(&edge.cycle_chain)
        ));
        out.push('}');
    }
    out.push_str("]},");
    out.push_str("\"runtime_imports\":{");
    out.push_str(&format!(
        "\"directives_executed\":{},\"injected_lines\":{},\"consistent\":{}",
        runtime_imports.directives_executed,
        runtime_imports.injected_lines,
        if runtime_import_stats_consistent(runtime_imports) {
            "true"
        } else {
            "false"
        }
    ));
    out.push_str("},");
    out.push_str("\"binding_events\":[");
    for (bidx, ev) in binding_events.iter().enumerate() {
        if bidx > 0 {
            out.push(',');
        }
        out.push('{');
        out.push_str(&format!(
            "\"name\":\"{}\",\"value\":\"{}\",\"expanded_line\":{},\"source_file\":\"{}\",\"source_line\":{}",
            json_escape(&ev.name),
            json_escape(&ev.value),
            ev.expanded_line,
            json_escape(&ev.source_file),
            ev.source_line
        ));
        out.push('}');
    }
    out.push_str("],");
    out.push_str("\"entries\":[");
    for (idx, entry) in entries.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push('{');
        out.push_str(&format!("\"line\":{},", entry.line));
        out.push_str(&format!("\"input\":\"{}\",", json_escape(&entry.input)));
        out.push_str(&format!("\"status\":\"{}\"", entry.status));
        if let Some(elapsed_ms) = entry.elapsed_ms {
            out.push_str(&format!(",\"elapsed_ms\":{elapsed_ms:.3}"));
        }
        if let Some(diag) = &entry.core_diagnostics {
            out.push_str(",\"core_diagnostics\":{");
            out.push_str(&format!(
                "\"mode\":\"{}\",\"elapsed_ms\":{:.3},\"term_count\":{},\"rewrite_count\":{},\"normal_form_count\":{},\"root_out_degree\":{},\"max_out_degree\":{},\"avg_out_degree\":{:.3},\"p95_out_degree\":{},\"reachable_term_count\":{},\"reachable_rewrite_count\":{},\"relation_cardinalities\":[{}],\"relation_extract_total_ms\":{:.3},\"relation_timings_ms\":[{}],\"core_phase_total_ms\":{:.3},\"core_phase_timings_ms\":[{}]",
                json_escape(&diag.mode),
                diag.elapsed_ms,
                diag.term_count,
                diag.rewrite_count,
                diag.normal_form_count,
                diag.root_out_degree,
                diag.max_out_degree,
                diag.avg_out_degree,
                diag.p95_out_degree,
                diag.reachable_term_count,
                diag.reachable_rewrite_count,
                relation_cardinalities_json(&diag.relation_cardinalities, lookup_relation_metadata),
                diag.relation_extract_total_ms,
                relation_timings_json(&diag.relation_timings_ms, lookup_relation_metadata),
                diag.core_phase_total_ms,
                relation_timings_json(&diag.core_phase_timings_ms, None)
            ));
            out.push('}');
        }
        if let Some(diag) = &entry.surface_diagnostics {
            out.push_str(",\"surface_diagnostics\":{");
            out.push_str(&surface_diagnostics_json(diag));
            out.push('}');
        }
        if let Some(source_file) = &entry.source_file {
            out.push_str(&format!(",\"source_file\":\"{}\"", json_escape(source_file)));
        }
        if let Some(source_line) = entry.source_line {
            out.push_str(&format!(",\"source_line\":{source_line}"));
        }
        if let Some(binding_name) = &entry.binding_name {
            out.push_str(&format!(",\"binding_name\":\"{}\"", json_escape(binding_name)));
        }
        if let Some(binding_value) = &entry.binding_value {
            out.push_str(&format!(",\"binding_value\":\"{}\"", json_escape(binding_value)));
        }
        if let Some(results) = &entry.surface_results {
            out.push_str(",\"surface_results\":[");
            for (ridx, item) in results.iter().enumerate() {
                if ridx > 0 {
                    out.push(',');
                }
                out.push('"');
                out.push_str(&json_escape(item));
                out.push('"');
            }
            out.push(']');
        }
        if let Some(expected) = &entry.expected_surface {
            out.push_str(",\"expected_surface\":[");
            for (eidx, item) in expected.iter().enumerate() {
                if eidx > 0 {
                    out.push(',');
                }
                out.push('"');
                out.push_str(&json_escape(item));
                out.push('"');
            }
            out.push(']');
        }
        if let Some(err) = &entry.error {
            out.push_str(&format!(",\"error\":\"{}\"", json_escape(err)));
        }
        out.push('}');
    }
    out.push_str("]}");
    out
}

pub fn run_metta_file_report_jsonl(
    file_path: &str,
    passed: usize,
    failed: usize,
    skipped: usize,
    entries: &[RunMettaFileEntry],
    import_meta: &ImportExpansionMeta,
    binding_events: &[BatchBindingEvent],
    runtime_imports: RuntimeImportStats,
    surface_policy: &str,
    dispatch_contracts: RuntimeDispatchContracts,
    lookup_relation_metadata: Option<&HashMap<String, LookupRelationMetadata>>,
) -> String {
    let stats = summarize_run_metta_file_entries(entries);
    let mut lines = Vec::with_capacity(entries.len() + 1);
    let mut imported_files: Vec<String> = import_meta.imported_files.iter().cloned().collect();
    imported_files.sort();
    let imported_json = imported_files
        .iter()
        .map(|p| format!("\"{}\"", json_escape(p)))
        .collect::<Vec<_>>()
        .join(",");
    let mut target_spaces: Vec<String> = import_meta.target_spaces.iter().cloned().collect();
    target_spaces.sort();
    let target_spaces_json = target_spaces
        .iter()
        .map(|s| format!("\"{}\"", json_escape(s)))
        .collect::<Vec<_>>()
        .join(",");
    lines.push(format!(
        "{{\"kind\":\"summary\",\"command\":\"run-metta-file\",\"file\":\"{}\",\"passed\":{},\"failed\":{},\"skipped\":{},\"total_entries\":{},\"lines_with_expectations\":{},\"expectation_failures\":{},\"assertion_mismatch_failures\":{},\"command_failures\":{},\"surface_policy\":\"{}\",\"dispatch_contracts\":{{\"deterministic_reduction\":{},\"memoization_safe\":{},\"specialization_safe\":{},\"core_ground_eval_safe\":{}}},\"import_directives_seen\":{},\"import_non_self_directives\":{},\"import_expanded_lines\":{},\"import_skipped_cycles\":{},\"import_edge_count\":{},\"binding_events\":{},\"target_spaces\":[{}],\"imported_files\":[{}]}}",
        json_escape(file_path),
        passed,
        failed,
        skipped,
        stats.total_entries,
        stats.lines_with_expectations,
        stats.expectation_failures,
        stats.assertion_mismatch_failures,
        stats.command_failures,
        json_escape(surface_policy),
        if dispatch_contracts.deterministic_reduction { "true" } else { "false" },
        if dispatch_contracts.memoization_safe { "true" } else { "false" },
        if dispatch_contracts.specialization_safe { "true" } else { "false" },
        if dispatch_contracts.core_ground_eval_safe { "true" } else { "false" },
        import_meta.directives_seen,
        import_meta.non_self_directives,
        import_meta.expanded_lines,
        import_meta.skipped_cycles,
        import_meta.import_edges.len(),
        binding_events.len(),
        target_spaces_json,
        imported_json
    ));
    if let Some(first) = lines.first_mut() {
        let suffix = format!(
            ",\"runtime_import_directives\":{},\"runtime_import_injected_lines\":{},\"runtime_import_consistent\":{}",
            runtime_imports.directives_executed,
            runtime_imports.injected_lines,
            if runtime_import_stats_consistent(runtime_imports) {
                "true"
            } else {
                "false"
            }
        );
        if let Some(without_brace) = first.strip_suffix('}') {
            *first = format!("{without_brace}{suffix}}}");
        }
    }
    for edge in &import_meta.import_edges {
        lines.push(format!(
            "{{\"kind\":\"import_edge\",\"source_file\":\"{}\",\"source_line\":{},\"import_path\":\"{}\",\"source_space\":\"{}\",\"effective_space\":\"{}\",\"target_file\":\"{}\",\"skipped_cycle\":{},\"cycle_chain\":[{}]}}",
            json_escape(&edge.source_file),
            edge.source_line,
            json_escape(&edge.import_path),
            json_escape(&edge.source_space),
            json_escape(&edge.effective_space),
            json_escape(&edge.target_file),
            if edge.skipped_cycle { "true" } else { "false" },
            json_string_array(&edge.cycle_chain)
        ));
    }
    for ev in binding_events {
        lines.push(format!(
            "{{\"kind\":\"binding\",\"name\":\"{}\",\"value\":\"{}\",\"expanded_line\":{},\"source_file\":\"{}\",\"source_line\":{}}}",
            json_escape(&ev.name),
            json_escape(&ev.value),
            ev.expanded_line,
            json_escape(&ev.source_file),
            ev.source_line
        ));
    }
    for entry in entries {
        let mut line = format!(
            "{{\"kind\":\"entry\",\"line\":{},\"input\":\"{}\",\"status\":\"{}\"",
            entry.line,
            json_escape(&entry.input),
            entry.status
        );
        if let Some(elapsed_ms) = entry.elapsed_ms {
            line.push_str(&format!(",\"elapsed_ms\":{elapsed_ms:.3}"));
        }
        if let Some(diag) = &entry.core_diagnostics {
            line.push_str(",\"core_diagnostics\":{");
            line.push_str(&format!(
                "\"mode\":\"{}\",\"elapsed_ms\":{:.3},\"term_count\":{},\"rewrite_count\":{},\"normal_form_count\":{},\"root_out_degree\":{},\"max_out_degree\":{},\"avg_out_degree\":{:.3},\"p95_out_degree\":{},\"reachable_term_count\":{},\"reachable_rewrite_count\":{},\"relation_cardinalities\":[{}],\"relation_extract_total_ms\":{:.3},\"relation_timings_ms\":[{}],\"core_phase_total_ms\":{:.3},\"core_phase_timings_ms\":[{}]",
                json_escape(&diag.mode),
                diag.elapsed_ms,
                diag.term_count,
                diag.rewrite_count,
                diag.normal_form_count,
                diag.root_out_degree,
                diag.max_out_degree,
                diag.avg_out_degree,
                diag.p95_out_degree,
                diag.reachable_term_count,
                diag.reachable_rewrite_count,
                relation_cardinalities_json(&diag.relation_cardinalities, lookup_relation_metadata),
                diag.relation_extract_total_ms,
                relation_timings_json(&diag.relation_timings_ms, lookup_relation_metadata),
                diag.core_phase_total_ms,
                relation_timings_json(&diag.core_phase_timings_ms, None)
            ));
            line.push('}');
        }
        if let Some(diag) = &entry.surface_diagnostics {
            line.push_str(",\"surface_diagnostics\":{");
            line.push_str(&surface_diagnostics_json(diag));
            line.push('}');
        }
        if let Some(source_file) = &entry.source_file {
            line.push_str(&format!(",\"source_file\":\"{}\"", json_escape(source_file)));
        }
        if let Some(source_line) = entry.source_line {
            line.push_str(&format!(",\"source_line\":{source_line}"));
        }
        if let Some(binding_name) = &entry.binding_name {
            line.push_str(&format!(",\"binding_name\":\"{}\"", json_escape(binding_name)));
        }
        if let Some(binding_value) = &entry.binding_value {
            line.push_str(&format!(",\"binding_value\":\"{}\"", json_escape(binding_value)));
        }
        if let Some(results) = &entry.surface_results {
            line.push_str(",\"surface_results\":[");
            for (ridx, item) in results.iter().enumerate() {
                if ridx > 0 {
                    line.push(',');
                }
                line.push('"');
                line.push_str(&json_escape(item));
                line.push('"');
            }
            line.push(']');
        }
        if let Some(expected) = &entry.expected_surface {
            line.push_str(",\"expected_surface\":[");
            for (eidx, item) in expected.iter().enumerate() {
                if eidx > 0 {
                    line.push(',');
                }
                line.push('"');
                line.push_str(&json_escape(item));
                line.push('"');
            }
            line.push(']');
        }
        if let Some(err) = &entry.error {
            line.push_str(&format!(",\"error\":\"{}\"", json_escape(err)));
        }
        line.push('}');
        lines.push(line);
    }
    lines.join("\n")
}

fn shared_err(err: String) -> anyhow::Error {
    anyhow::anyhow!(err)
}

#[allow(dead_code)]
fn split_top_level_forms(raw: &str) -> Vec<String> {
    shared_metta_file::split_top_level_forms(raw)
}

#[allow(dead_code)]
pub(crate) fn coalesce_source_forms(
    content: &str,
    source_file: &str,
    default_space: &str,
) -> Result<Vec<ExpandedMettaLine>> {
    shared_metta_file::coalesce_source_forms(content, source_file, default_space)
        .map_err(shared_err)
}

pub fn split_run_metta_file_line(raw_line: &str) -> Result<Option<(String, Option<Vec<String>>)>> {
    shared_metta_file::split_run_metta_file_line(raw_line).map_err(shared_err)
}

pub fn is_hyperon_compat_ignorable_prose_line(line: &str) -> bool {
    shared_metta_file::is_hyperon_compat_ignorable_prose_line(line)
}

pub fn parse_batch_capture_assignment(line: &str) -> Option<BatchCaptureAssignment> {
    shared_metta_file::parse_batch_capture_assignment(line)
}

pub fn substitute_batch_bindings(input: &str, bindings: &HashMap<String, String>) -> String {
    shared_metta_file::substitute_batch_bindings(input, bindings)
}

pub fn parse_import_directive(line: &str) -> Option<(String, String)> {
    shared_metta_file::parse_import_directive(line)
}

pub fn effective_import_target_space(space: &str, current_default_space: &str) -> String {
    shared_metta_file::effective_import_target_space(space, current_default_space)
}

#[allow(dead_code)]
fn resolve_import_file_path(
    base_dir: &Path,
    import_path: &str,
    library_aliases: &HashMap<String, String>,
) -> PathBuf {
    shared_metta_file::resolve_import_file_path(base_dir, import_path, library_aliases)
}

pub fn expand_metta_file_with_imports(
    file_path: &Path,
    seen: &mut HashSet<PathBuf>,
    depth: usize,
    meta: &mut ImportExpansionMeta,
    current_default_space: &str,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>> {
    shared_metta_file::expand_metta_file_with_imports(
        file_path,
        seen,
        depth,
        meta,
        current_default_space,
        library_aliases,
    )
    .map_err(shared_err)
}

pub fn expand_import_directive_from_source(
    source_file: &str,
    source_line: usize,
    source_space: &str,
    import_path: &str,
    current_default_space: &str,
    seen: &mut HashSet<PathBuf>,
    meta: &mut ImportExpansionMeta,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>> {
    shared_metta_file::expand_import_directive_from_source(
        source_file,
        source_line,
        source_space,
        import_path,
        current_default_space,
        seen,
        meta,
        library_aliases,
    )
    .map_err(shared_err)
}

fn normalized_surface_values(values: &[String]) -> Vec<String> {
    let mut out: Vec<String> = values
        .iter()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    out.sort();
    out.dedup();
    out
}

pub fn expected_surface_mismatch(expected: &[String], actual: &[String]) -> Option<String> {
    let exp = normalized_surface_values(expected);
    let exp_set: std::collections::HashSet<String> = exp.clone().into_iter().collect();
    let act = normalized_surface_values(actual);
    if act.is_empty() {
        return Some(format!(
            "surface assertion mismatch: got no surface results, expected one of {:?}",
            exp
        ));
    }
    // Each actual result must appear in the expected set.
    // `;=> a | b` means "every result must be one of {a, b}".
    let disallowed: Vec<&String> = act.iter().filter(|v| !exp_set.contains(*v)).collect();
    if disallowed.is_empty() {
        return None;
    }
    Some(format!(
        "surface assertion mismatch: got {:?}, not all in allowed set {:?}",
        act, exp
    ))
}

fn remap_stmt_space(space: String, default_space: &str) -> String {
    if space == DEFAULT_BATCH_SPACE_IDENT {
        default_space.to_string()
    } else {
        space
    }
}

pub fn retarget_surface_stmt(stmt: SurfaceStmt, default_space: &str) -> SurfaceStmt {
    if default_space == DEFAULT_BATCH_SPACE_IDENT {
        return stmt;
    }
    match stmt {
        SurfaceStmt::DefineEq(lhs, rhs) => SurfaceStmt::AddAtom {
            space: default_space.to_string(),
            atom_expr: SExpr::List(vec![SExpr::Atom("=".to_string()), lhs, rhs]),
        },
        SurfaceStmt::DefineType(atom, ty) => SurfaceStmt::AddAtom {
            space: default_space.to_string(),
            atom_expr: SExpr::List(vec![SExpr::Atom(":".to_string()), atom, ty]),
        },
        SurfaceStmt::Eval(expr) => SurfaceStmt::EvalIn { space: default_space.to_string(), expr },
        SurfaceStmt::EvalIn { space, expr } => SurfaceStmt::EvalIn {
            space: remap_stmt_space(space, default_space),
            expr,
        },
        SurfaceStmt::AddAtom { space, atom_expr } => SurfaceStmt::AddAtom {
            space: remap_stmt_space(space, default_space),
            atom_expr,
        },
        SurfaceStmt::RemoveAtom { space, atom_expr } => SurfaceStmt::RemoveAtom {
            space: remap_stmt_space(space, default_space),
            atom_expr,
        },
        SurfaceStmt::DeclareMemoized { space, head } => SurfaceStmt::DeclareMemoized {
            space: remap_stmt_space(space, default_space),
            head,
        },
        SurfaceStmt::NewSpace { space } => SurfaceStmt::NewSpace {
            space: remap_stmt_space(space, default_space),
        },
        SurfaceStmt::AllocSpace => SurfaceStmt::AllocSpace,
        SurfaceStmt::Import { target_space, path } => SurfaceStmt::Import {
            target_space: remap_stmt_space(target_space, default_space),
            path,
        },
        SurfaceStmt::SetFuel(n) => SurfaceStmt::SetFuel(n),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        coalesce_source_forms, effective_import_target_space, expand_import_directive_from_source,
        expand_metta_file_with_imports, expected_surface_mismatch,
        is_hyperon_compat_ignorable_prose_line, parse_batch_capture_assignment,
        parse_import_directive, resolve_import_file_path, retarget_surface_stmt,
        run_metta_file_report_json, run_metta_file_report_jsonl, runtime_import_stats_consistent,
        split_top_level_forms, substitute_batch_bindings, BatchBindingEvent, ImportEdge,
        ImportExpansionMeta, RunMettaFileEntry, RuntimeDispatchContracts, RuntimeImportStats,
        DEFAULT_BATCH_SPACE_IDENT,
    };
    use crate::lookup_plan::LookupRelationMetadata;
    use crate::metta_surface::{SExpr, SurfaceStmt};
    use mettail_runtime::CoreEvalDiagnostics;
    use std::collections::{HashMap, HashSet};
    use std::path::Path;

    #[test]
    fn expected_surface_or_accepts_subset() {
        let expected = vec!["5".to_string(), "6".to_string()];
        let actual = vec!["5".to_string()];
        assert!(expected_surface_mismatch(&expected, &actual).is_none());
    }

    #[test]
    fn expected_surface_or_rejects_disallowed_values() {
        let expected = vec!["6".to_string(), "7".to_string()];
        let actual = vec!["5".to_string()];
        assert!(expected_surface_mismatch(&expected, &actual).is_some());
    }

    #[test]
    fn expected_surface_or_rejects_empty_actual() {
        let expected = vec!["true".to_string()];
        let actual: Vec<String> = vec![];
        assert!(expected_surface_mismatch(&expected, &actual).is_some());
    }

    #[test]
    fn coalesce_source_forms_combines_multiline_statements() {
        let src = "(= (inc $x)\n   (+ $x 1))\n!(inc 4)\n";
        let out = coalesce_source_forms(src, "suite.metta", "&self").expect("coalesce");
        assert_eq!(out.len(), 2);
        assert_eq!(out[0].source_line, 1);
        assert!(out[0].text.contains('\n'));
        assert_eq!(out[1].source_line, 3);
        assert_eq!(out[1].text.trim(), "!(inc 4)");
    }

    #[test]
    fn coalesce_source_forms_errors_on_unclosed_form() {
        let src = "(= (inc $x)\n  (+ $x 1)\n";
        let err = coalesce_source_forms(src, "bad.metta", "&self").expect_err("should fail");
        assert!(err.to_string().contains("unterminated multiline statement"));
    }

    #[test]
    fn coalesce_source_forms_handles_inline_comments_in_multiline_expr() {
        let src = "(= (f) ; inline\n  ; only comment line\n  42)\n!(test (f) 42)\n";
        let out = coalesce_source_forms(src, "comments.metta", "&self").expect("coalesce");
        assert_eq!(out.len(), 2);
        assert!(out[0].text.contains("(= (f)"));
        assert!(!out[0].text.contains("inline"));
        assert_eq!(out[1].text.trim(), "!(test (f) 42)");
    }

    #[test]
    fn hyperon_compat_prose_line_filter_detects_headers() {
        assert!(is_hyperon_compat_ignorable_prose_line("Auto type-checking can be enabled"));
        assert!(is_hyperon_compat_ignorable_prose_line("This script checks grounded operators"));
        assert!(!is_hyperon_compat_ignorable_prose_line("!(pragma! type-check auto)"));
        assert!(!is_hyperon_compat_ignorable_prose_line("(= (f $x) $x)"));
        assert!(!is_hyperon_compat_ignorable_prose_line("$tmp = !(new-space!)"));
        assert!(!is_hyperon_compat_ignorable_prose_line("foo"));
    }

    #[test]
    fn split_top_level_forms_splits_flat_concatenated_forms() {
        let forms = split_top_level_forms("(a 1) (b 2) (c 3)");
        assert_eq!(forms, vec!["(a 1)", "(b 2)", "(c 3)"]);
    }

    #[test]
    fn split_top_level_forms_keeps_bang_prefixed_form_intact() {
        let forms = split_top_level_forms("! (new-goal-status! lunch-order inactive)");
        assert_eq!(forms, vec!["! (new-goal-status! lunch-order inactive)"]);
    }

    #[test]
    fn split_top_level_forms_keeps_prose_header_line_intact() {
        let forms = split_top_level_forms("Auto type-checking can be enabled");
        assert_eq!(forms, vec!["Auto type-checking can be enabled"]);
    }

    #[test]
    fn split_top_level_forms_keeps_batch_capture_assignment_intact() {
        let forms = split_top_level_forms("$tmp = !(new-space!)");
        assert_eq!(forms, vec!["$tmp = !(new-space!)"]);
    }

    #[test]
    fn parse_batch_capture_assignment_works() {
        let got = parse_batch_capture_assignment("$tmp = !(new-space!)").expect("assignment");
        assert_eq!(got.name, "tmp");
        assert_eq!(got.rhs, "!(new-space!)");
        assert_eq!(got.index, 0);
        let got_idx = parse_batch_capture_assignment("$vals[2] = !(choose)").expect("assignment");
        assert_eq!(got_idx.name, "vals");
        assert_eq!(got_idx.rhs, "!(choose)");
        assert_eq!(got_idx.index, 2);
        assert!(parse_batch_capture_assignment("(= foo true)").is_none());
        assert!(parse_batch_capture_assignment("$vals[x] = !(choose)").is_none());
        assert!(parse_batch_capture_assignment("$vals[] = !(choose)").is_none());
    }

    #[test]
    fn substitute_batch_bindings_replaces_only_outside_strings() {
        let mut bindings = HashMap::new();
        bindings.insert("tmp".to_string(), "&space7".to_string());
        let in_line = "!(add-atom! $tmp (= msg \"$tmp\"))";
        let out_line = substitute_batch_bindings(in_line, &bindings);
        assert_eq!(out_line, "!(add-atom! &space7 (= msg \"$tmp\"))");
    }

    #[test]
    fn parse_import_directive_accepts_he_forms() {
        let a = parse_import_directive("!(import! &self ../lib/lib_he)").expect("import");
        assert_eq!(a.0, "&self");
        assert_eq!(a.1, "../lib/lib_he");
        let b = parse_import_directive("(import! \"./foo.metta\")").expect("import");
        assert_eq!(b.0, "&self");
        assert_eq!(b.1, "./foo.metta");
        let c = parse_import_directive("!(import! &self (library lib_pln))").expect("import");
        assert_eq!(c.0, "&self");
        assert_eq!(c.1, "library:lib_pln");
    }

    #[test]
    fn resolve_import_file_path_supports_missing_metta_extension() {
        let base = Path::new("/home/zar/claude/hyperon/PeTTa/examples");
        let lib_he = resolve_import_file_path(base, "../lib/lib_he", &HashMap::new());
        assert!(
            lib_he.ends_with("lib_he.metta"),
            "expected lib_he to resolve with .metta extension"
        );
        let lib_he_from_parent = resolve_import_file_path(base, "lib/lib_he", &HashMap::new());
        assert!(
            lib_he_from_parent.ends_with("lib_he.metta"),
            "expected parent-relative lib/ import to resolve with .metta extension"
        );
        let fibsmart = resolve_import_file_path(base, "fibsmart", &HashMap::new());
        assert!(
            fibsmart.ends_with("fibsmart.metta"),
            "expected sibling import to resolve with .metta extension"
        );
    }

    #[test]
    fn resolve_import_file_path_uses_parent_lib_dir() {
        // When base_dir is PeTTa/examples/, library:lib_pln should resolve
        // to PeTTa/lib/lib_pln.metta via parent directory search.
        let base = Path::new("/home/zar/claude/hyperon/PeTTa/examples");
        let aliases = HashMap::new();
        let resolved = resolve_import_file_path(base, "library:lib_pln", &aliases);
        assert!(
            resolved.to_string_lossy().contains("PeTTa/lib/lib_pln.metta"),
            "library import should resolve via parent lib/ dir, got: {}",
            resolved.display()
        );
    }

    #[test]
    fn effective_import_target_space_maps_self_to_current_default() {
        assert_eq!(effective_import_target_space("&self", "&tmp"), "&tmp".to_string());
        assert_eq!(effective_import_target_space("&other", "&tmp"), "&other".to_string());
    }

    #[test]
    fn retarget_surface_stmt_rewrites_default_space_bindings() {
        let stmt =
            SurfaceStmt::DefineEq(SExpr::Atom("foo".to_string()), SExpr::Atom("true".to_string()));
        let mapped = retarget_surface_stmt(stmt, "&tmp");
        match mapped {
            SurfaceStmt::AddAtom { space, .. } => assert_eq!(space, "&tmp"),
            _ => panic!("expected retargeted AddAtom"),
        }
        let eval = SurfaceStmt::EvalIn {
            space: "&self".to_string(),
            expr: SExpr::Atom("foo".to_string()),
        };
        let mapped_eval = retarget_surface_stmt(eval, "&tmp");
        match mapped_eval {
            SurfaceStmt::EvalIn { space, .. } => assert_eq!(space, "&tmp"),
            _ => panic!("expected retargeted EvalIn"),
        }
    }

    #[test]
    fn nested_import_self_is_remapped_to_parent_space() {
        let mut seen = HashSet::new();
        let mut meta = ImportExpansionMeta::default();
        let rel = Path::new("repl/src/examples/mettafullstate_surface_import_nested_main.metta");
        let local = Path::new("src/examples/mettafullstate_surface_import_nested_main.metta");
        let import_path = if rel.exists() { rel } else { local };
        let expanded = expand_metta_file_with_imports(
            import_path,
            &mut seen,
            0,
            &mut meta,
            DEFAULT_BATCH_SPACE_IDENT,
            &HashMap::new(),
        )
        .expect("expand imports");

        let nested_leaf_lines: Vec<_> = expanded
            .iter()
            .filter(|line| {
                line.source_file
                    .ends_with("mettafullstate_surface_import_nested_leaf.metta")
            })
            .collect();
        assert!(!nested_leaf_lines.is_empty(), "expected expanded lines from nested leaf import");
        assert!(
            nested_leaf_lines
                .iter()
                .all(|line| line.default_space == "&tmp"),
            "nested leaf lines should inherit &tmp default space"
        );

        let has_self_to_tmp_edge = meta.import_edges.iter().any(|edge| {
            edge.source_file
                .ends_with("mettafullstate_surface_import_nested_mid.metta")
                && edge.source_space == "&self"
                && edge.effective_space == "&tmp"
        });
        assert!(
            has_self_to_tmp_edge,
            "expected import edge from nested mid with source_space=&self remapped to effective_space=&tmp"
        );
    }

    #[test]
    fn cycle_import_edge_contains_materialized_chain() {
        let mut seen = HashSet::new();
        let mut meta = ImportExpansionMeta::default();
        let rel = Path::new("repl/src/examples/mettafullstate_surface_import_cycle_a.metta");
        let local = Path::new("src/examples/mettafullstate_surface_import_cycle_a.metta");
        let import_path = if rel.exists() { rel } else { local };

        let _expanded = expand_metta_file_with_imports(
            import_path,
            &mut seen,
            0,
            &mut meta,
            DEFAULT_BATCH_SPACE_IDENT,
            &HashMap::new(),
        )
        .expect("expand cycle imports");

        let cyc = meta
            .import_edges
            .iter()
            .find(|edge| edge.skipped_cycle && !edge.cycle_chain.is_empty())
            .expect("expected skipped-cycle edge with materialized cycle_chain");
        assert!(
            cyc.cycle_chain.len() >= 2,
            "cycle chain should include at least origin and repeated target"
        );
        let first = cyc.cycle_chain.first().expect("cycle chain first");
        let last = cyc.cycle_chain.last().expect("cycle chain last");
        assert_eq!(first, last, "cycle chain should close by repeating the origin target");
    }

    #[test]
    fn repeated_import_same_file_in_distinct_spaces_expands_twice() {
        let mut seen = HashSet::new();
        let mut meta = ImportExpansionMeta::default();
        let rel = Path::new("repl/src/examples/mettafullstate_surface_import_lib.metta");
        let local = Path::new("src/examples/mettafullstate_surface_import_lib.metta");
        let import_path = if rel.exists() { rel } else { local };
        let source = import_path
            .parent()
            .expect("import fixture parent")
            .join("mettafullstate_surface_import_main.metta");
        let source_display = source.display().to_string();
        let import_token = import_path
            .file_name()
            .expect("import fixture filename")
            .to_string_lossy()
            .to_string();

        let first = expand_import_directive_from_source(
            &source_display,
            1,
            "&self",
            &import_token,
            DEFAULT_BATCH_SPACE_IDENT,
            &mut seen,
            &mut meta,
            &HashMap::new(),
        )
        .expect("first import");
        let second = expand_import_directive_from_source(
            &source_display,
            2,
            "&tmp",
            &import_token,
            DEFAULT_BATCH_SPACE_IDENT,
            &mut seen,
            &mut meta,
            &HashMap::new(),
        )
        .expect("second import");
        assert!(!first.is_empty(), "first import should expand");
        assert!(!second.is_empty(), "second import into another space should expand");
        assert_eq!(
            meta.skipped_cycles, 0,
            "repeated import in another space should not count as cycle"
        );
    }

    #[test]
    fn python_import_is_tracked_but_not_parsed_as_metta() {
        let mut seen = HashSet::new();
        let mut meta = ImportExpansionMeta::default();
        let rel = Path::new("../PeTTa/examples/python_import.metta");
        let local = Path::new("../../PeTTa/examples/python_import.metta");
        let import_path = if rel.exists() { rel } else { local };

        let expanded = expand_metta_file_with_imports(
            import_path,
            &mut seen,
            0,
            &mut meta,
            DEFAULT_BATCH_SPACE_IDENT,
            &HashMap::new(),
        )
        .expect("expand python imports");

        assert!(
            expanded
                .iter()
                .all(|line| !line.source_file.ends_with(".py")),
            "python source should not be parsed as MeTTa"
        );
        assert!(
            meta.imported_files
                .iter()
                .any(|f| f.ends_with("python_import_file.py")),
            "python import should still be tracked in imported_files"
        );
        assert!(
            meta.import_edges
                .iter()
                .any(|e| e.target_file.ends_with("python_import_file.py")),
            "python import edge should be preserved"
        );
    }

    fn extract_json_usize(line: &str, field: &str) -> Option<usize> {
        let key = format!("\"{field}\":");
        let idx = line.find(&key)?;
        let mut rest = &line[idx + key.len()..];
        rest = rest.trim_start();
        let mut end = 0usize;
        for ch in rest.chars() {
            if ch.is_ascii_digit() {
                end += ch.len_utf8();
            } else {
                break;
            }
        }
        if end == 0 {
            return None;
        }
        rest[..end].parse::<usize>().ok()
    }

    fn extract_json_bool(line: &str, field: &str) -> Option<bool> {
        let key = format!("\"{field}\":");
        let idx = line.find(&key)?;
        let rest = line[idx + key.len()..].trim_start();
        if rest.starts_with("true") {
            Some(true)
        } else if rest.starts_with("false") {
            Some(false)
        } else {
            None
        }
    }

    #[test]
    fn jsonl_summary_counts_match_kinds_and_runtime_fields() {
        let entries = vec![RunMettaFileEntry {
            line: 1,
            input: "!(+ 2 3)".to_string(),
            status: "pass",
            error: None,
            surface_results: Some(vec!["5".to_string()]),
            expected_surface: Some(vec!["5".to_string()]),
            elapsed_ms: Some(1.0),
            source_file: Some("suite.metta".to_string()),
            source_line: Some(1),
            binding_name: Some("tmp".to_string()),
            binding_value: Some("&space1".to_string()),
            surface_diagnostics: None,
            core_diagnostics: None,
        }];

        let mut import_meta = ImportExpansionMeta::default();
        import_meta.import_edges.push(ImportEdge {
            source_file: "suite.metta".to_string(),
            source_line: 1,
            import_path: "lib.metta".to_string(),
            source_space: "&tmp".to_string(),
            effective_space: "&tmp".to_string(),
            target_file: "lib.metta".to_string(),
            skipped_cycle: false,
            cycle_chain: Vec::new(),
        });
        import_meta.directives_seen = 1;
        import_meta.non_self_directives = 1;
        import_meta.target_spaces.insert("&tmp".to_string());
        import_meta.imported_files.insert("lib.metta".to_string());

        let binding_events = vec![BatchBindingEvent {
            name: "tmp".to_string(),
            value: "&space1".to_string(),
            expanded_line: 1,
            source_file: "suite.metta".to_string(),
            source_line: 1,
        }];

        let report = run_metta_file_report_jsonl(
            "suite.metta",
            1,
            0,
            0,
            &entries,
            &import_meta,
            &binding_events,
            RuntimeImportStats {
                directives_executed: 2,
                injected_lines: 5,
            },
            "deterministic",
            RuntimeDispatchContracts {
                deterministic_reduction: true,
                memoization_safe: true,
                specialization_safe: true,
                core_ground_eval_safe: true,
            },
            None,
        );
        let lines: Vec<&str> = report.lines().collect();
        assert!(!lines.is_empty(), "expected non-empty jsonl report");
        let summary = lines[0];
        let import_edge_rows = lines
            .iter()
            .filter(|line| line.contains("\"kind\":\"import_edge\""))
            .count();
        let binding_rows = lines
            .iter()
            .filter(|line| line.contains("\"kind\":\"binding\""))
            .count();

        assert_eq!(extract_json_usize(summary, "import_edge_count"), Some(import_edge_rows));
        assert_eq!(extract_json_usize(summary, "binding_events"), Some(binding_rows));
        assert_eq!(extract_json_usize(summary, "runtime_import_directives"), Some(2));
        assert_eq!(extract_json_usize(summary, "runtime_import_injected_lines"), Some(5));
        assert_eq!(extract_json_bool(summary, "runtime_import_consistent"), Some(true));
        assert!(summary.contains("\"surface_policy\":\"deterministic\""));
        assert!(
            summary.contains("\"dispatch_contracts\":{\"deterministic_reduction\":true,\"memoization_safe\":true,\"specialization_safe\":true,\"core_ground_eval_safe\":true}")
        );
    }

    #[test]
    fn json_report_includes_dispatch_contracts() {
        let report = run_metta_file_report_json(
            "suite.metta",
            0,
            0,
            0,
            &[],
            &ImportExpansionMeta::default(),
            &[],
            RuntimeImportStats::default(),
            "default",
            RuntimeDispatchContracts {
                deterministic_reduction: false,
                memoization_safe: true,
                specialization_safe: true,
                core_ground_eval_safe: true,
            },
            None,
        );
        assert!(report.contains("\"surface_policy\":\"default\""));
        assert!(
            report.contains("\"dispatch_contracts\":{\"deterministic_reduction\":false,\"memoization_safe\":true,\"specialization_safe\":true,\"core_ground_eval_safe\":true}")
        );
    }

    #[test]
    fn json_report_includes_lookup_relation_metadata_on_relation_timings() {
        let mut metadata = HashMap::new();
        metadata.insert(
            "eqQueryResult".to_string(),
            LookupRelationMetadata {
                logical_relation_id: "he.eq_query.result".to_string(),
                scope_signature: "b0+b1+f2".to_string(),
                usage_kind: Some("enumerate".to_string()),
            },
        );

        let core = CoreEvalDiagnostics {
            mode: "ascent".to_string(),
            elapsed_ms: 1.0,
            term_count: 1,
            rewrite_count: 0,
            normal_form_count: 1,
            root_out_degree: 0,
            max_out_degree: 0,
            avg_out_degree: 0.0,
            p95_out_degree: 0,
            reachable_term_count: 1,
            reachable_rewrite_count: 0,
            relation_cardinalities: vec![("eqQueryResult".to_string(), 2)],
            relation_extract_total_ms: 0.5,
            relation_timings_ms: vec![("eqQueryResult".to_string(), 0.5)],
            core_phase_total_ms: 0.0,
            core_phase_timings_ms: vec![],
        };
        let entries = vec![RunMettaFileEntry {
            line: 1,
            input: "!(double 5)".to_string(),
            status: "pass",
            error: None,
            surface_results: None,
            expected_surface: None,
            elapsed_ms: Some(1.0),
            source_file: Some("suite.metta".to_string()),
            source_line: Some(1),
            binding_name: None,
            binding_value: None,
            surface_diagnostics: None,
            core_diagnostics: Some(core),
        }];

        let report = run_metta_file_report_json(
            "suite.metta",
            1,
            0,
            0,
            &entries,
            &ImportExpansionMeta::default(),
            &[],
            RuntimeImportStats::default(),
            "default",
            RuntimeDispatchContracts {
                deterministic_reduction: true,
                memoization_safe: true,
                specialization_safe: true,
                core_ground_eval_safe: true,
            },
            Some(&metadata),
        );
        assert!(report.contains("\"logical_relation_id\":\"he.eq_query.result\""));
        assert!(report.contains("\"scope_signature\":\"b0+b1+f2\""));
        assert!(report.contains("\"usage_kind\":\"enumerate\""));
    }

    #[test]
    fn cycle_detection_is_scoped_by_file_and_space() {
        let mut seen = HashSet::new();
        let mut meta = ImportExpansionMeta::default();
        let rel = Path::new("repl/src/examples/mettafullstate_surface_import_lib.metta");
        let local = Path::new("src/examples/mettafullstate_surface_import_lib.metta");
        let import_path = if rel.exists() { rel } else { local };
        let source = import_path
            .parent()
            .expect("import fixture parent")
            .join("mettafullstate_surface_import_main.metta");
        let source_display = source.display().to_string();
        let import_token = import_path
            .file_name()
            .expect("import fixture filename")
            .to_string_lossy()
            .to_string();

        let first = expand_import_directive_from_source(
            &source_display,
            1,
            "&tmpA",
            &import_token,
            DEFAULT_BATCH_SPACE_IDENT,
            &mut seen,
            &mut meta,
            &HashMap::new(),
        )
        .expect("first import");
        let second = expand_import_directive_from_source(
            &source_display,
            2,
            "&tmpB",
            &import_token,
            DEFAULT_BATCH_SPACE_IDENT,
            &mut seen,
            &mut meta,
            &HashMap::new(),
        )
        .expect("second import");

        assert!(!first.is_empty(), "first import should expand");
        assert!(!second.is_empty(), "second import in different space should expand");
        assert_eq!(meta.skipped_cycles, 0, "different-space imports should not be cycles");
        assert!(
            meta.import_edges.iter().all(|edge| !edge.skipped_cycle),
            "different-space repeated imports should not set skipped_cycle"
        );
    }

    #[test]
    fn runtime_import_stats_consistency_flags_expected_cases() {
        assert!(runtime_import_stats_consistent(RuntimeImportStats {
            directives_executed: 0,
            injected_lines: 0,
        }));
        assert!(runtime_import_stats_consistent(RuntimeImportStats {
            directives_executed: 2,
            injected_lines: 3,
        }));
        assert!(!runtime_import_stats_consistent(RuntimeImportStats {
            directives_executed: 1,
            injected_lines: 0,
        }));
    }

    #[test]
    fn jsonl_summary_marks_runtime_import_consistency_false_when_invalid() {
        let report = run_metta_file_report_jsonl(
            "suite.metta",
            0,
            0,
            0,
            &[],
            &ImportExpansionMeta::default(),
            &[],
            RuntimeImportStats {
                directives_executed: 1,
                injected_lines: 0,
            },
            "default",
            RuntimeDispatchContracts {
                deterministic_reduction: false,
                memoization_safe: false,
                specialization_safe: false,
                core_ground_eval_safe: false,
            },
            None,
        );
        let summary = report.lines().next().expect("summary line");
        assert_eq!(extract_json_bool(summary, "runtime_import_consistent"), Some(false));
    }
}
