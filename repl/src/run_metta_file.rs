use anyhow::Result;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::lookup_plan::LookupRelationMetadata;
use crate::metta_surface::{SExpr, SurfaceStmt};
use mettail_runtime::{
    CoreEvalDiagnostics, RewriteEvalDiagnostics as SurfaceEvalDiagnostics, RuntimeDispatchContracts,
};

pub const DEFAULT_BATCH_SPACE_IDENT: &str = "&self";

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

#[derive(Debug, Clone)]
pub struct ExpandedMettaLine {
    pub text: String,
    pub source_file: String,
    pub source_line: usize,
    pub default_space: String,
}

#[derive(Debug, Clone)]
pub struct ImportEdge {
    pub source_file: String,
    pub source_line: usize,
    pub import_path: String,
    pub source_space: String,
    pub effective_space: String,
    pub target_file: String,
    pub skipped_cycle: bool,
    pub cycle_chain: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchCaptureAssignment {
    pub name: String,
    pub rhs: String,
    pub index: usize,
}

#[derive(Debug, Clone, Default)]
pub struct ImportExpansionMeta {
    pub directives_seen: usize,
    pub imported_files: HashSet<String>,
    pub target_spaces: HashSet<String>,
    pub non_self_directives: usize,
    pub skipped_cycles: usize,
    pub expanded_lines: usize,
    pub import_edges: Vec<ImportEdge>,
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

fn parse_expected_surface_directive(comment: &str) -> Result<Option<Vec<String>>> {
    let trimmed = comment.trim();
    if trimmed.is_empty() {
        return Ok(None);
    }

    let payload = if let Some(rest) = trimmed.strip_prefix("=>") {
        Some(rest.trim())
    } else if let Some((head, tail)) = trimmed.split_once(':') {
        if head.trim().eq_ignore_ascii_case("expect") {
            Some(tail.trim())
        } else {
            None
        }
    } else {
        None
    };

    let Some(payload) = payload else {
        return Ok(None);
    };

    let parts: Vec<String> = payload
        .split('|')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(ToString::to_string)
        .collect();
    if parts.is_empty() {
        anyhow::bail!("empty expectation directive (use ';=> value' or '; expect: value')");
    }
    Ok(Some(parts))
}

fn strip_inline_comment_outside_string(raw: &str) -> &str {
    let mut in_string = false;
    let mut escaped = false;
    let mut chars = raw.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => return &raw[..idx],
            '/' => {
                if let Some((_, '/')) = chars.peek() {
                    return &raw[..idx];
                }
            },
            _ => {},
        }
    }
    raw
}

fn comment_payload_outside_string(raw: &str) -> Option<&str> {
    let mut in_string = false;
    let mut escaped = false;
    let mut chars = raw.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => return Some(&raw[idx + 1..]),
            '/' => {
                if let Some((_, '/')) = chars.peek() {
                    return Some(&raw[idx + 2..]);
                }
            },
            _ => {},
        }
    }
    None
}

fn line_has_expectation_comment(raw: &str) -> bool {
    let Some(payload) = comment_payload_outside_string(raw) else {
        return false;
    };
    parse_expected_surface_directive(payload)
        .ok()
        .flatten()
        .is_some()
}

fn paren_delta_outside_string(raw: &str) -> i32 {
    let mut delta = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    for ch in raw.chars() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => delta += 1,
            ')' => delta -= 1,
            _ => {},
        }
    }
    delta
}

fn split_top_level_forms(raw: &str) -> Vec<String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Vec::new();
    }
    if parse_batch_capture_assignment(trimmed).is_some() {
        return vec![trimmed.to_string()];
    }
    if trimmed.starts_with('!') {
        return vec![trimmed.to_string()];
    }
    if !trimmed.contains('(') && !trimmed.contains(')') {
        return vec![trimmed.to_string()];
    }

    let mut out = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    let mut depth = 0i32;
    let mut start: Option<usize> = None;
    let chars: Vec<(usize, char)> = raw.char_indices().collect();
    let mut i = 0usize;

    while i < chars.len() {
        let (idx, ch) = chars[i];
        if start.is_none() {
            if ch.is_whitespace() {
                i += 1;
                continue;
            }
            start = Some(idx);
        }

        if in_string {
            if escaped {
                escaped = false;
                i += 1;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            i += 1;
            continue;
        }

        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {},
        }

        let is_last = i + 1 == chars.len();
        let should_close = if depth > 0 || in_string {
            false
        } else if ch == ')' {
            true
        } else if ch.is_whitespace() {
            true
        } else {
            is_last
        };

        if should_close {
            let end = if ch.is_whitespace() {
                idx
            } else {
                idx + ch.len_utf8()
            };
            if let Some(st) = start {
                let chunk = raw[st..end].trim();
                if !chunk.is_empty() {
                    out.push(chunk.to_string());
                }
            }
            start = None;
        }
        i += 1;
    }

    if let Some(st) = start {
        let chunk = raw[st..].trim();
        if !chunk.is_empty() {
            out.push(chunk.to_string());
        }
    }

    out
}

pub(crate) fn coalesce_source_forms(
    content: &str,
    source_file: &str,
    default_space: &str,
) -> Result<Vec<ExpandedMettaLine>> {
    let mut out = Vec::new();
    let mut acc = String::new();
    let mut acc_start_line = 0usize;
    let mut depth = 0i32;

    for (raw_idx, raw_line) in content.lines().enumerate() {
        let source_line = raw_idx + 1;
        let trimmed_no_comment = strip_inline_comment_outside_string(raw_line).trim();
        let has_code = !trimmed_no_comment.is_empty();
        let keep_inline_comment = line_has_expectation_comment(raw_line);
        let line_for_acc = if keep_inline_comment {
            raw_line.trim_end().to_string()
        } else {
            strip_inline_comment_outside_string(raw_line)
                .trim_end()
                .to_string()
        };

        if acc.is_empty() {
            if !has_code {
                out.push(ExpandedMettaLine {
                    text: raw_line.to_string(),
                    source_file: source_file.to_string(),
                    source_line,
                    default_space: default_space.to_string(),
                });
                continue;
            }
            acc = line_for_acc;
            acc_start_line = source_line;
            depth = paren_delta_outside_string(trimmed_no_comment);
        } else if has_code {
            acc.push('\n');
            acc.push_str(&line_for_acc);
            depth += paren_delta_outside_string(trimmed_no_comment);
        }

        if !acc.is_empty() && depth <= 0 {
            let combined = std::mem::take(&mut acc);
            let has_expectation = line_has_expectation_comment(&combined);
            if has_expectation {
                out.push(ExpandedMettaLine {
                    text: combined,
                    source_file: source_file.to_string(),
                    source_line: acc_start_line,
                    default_space: default_space.to_string(),
                });
            } else {
                let forms = split_top_level_forms(&combined);
                if forms.len() <= 1 {
                    out.push(ExpandedMettaLine {
                        text: combined,
                        source_file: source_file.to_string(),
                        source_line: acc_start_line,
                        default_space: default_space.to_string(),
                    });
                } else {
                    for form in forms {
                        out.push(ExpandedMettaLine {
                            text: form,
                            source_file: source_file.to_string(),
                            source_line: acc_start_line,
                            default_space: default_space.to_string(),
                        });
                    }
                }
            }
            acc_start_line = 0;
            depth = 0;
        }
    }

    if !acc.is_empty() {
        anyhow::bail!(
            "unterminated multiline statement in '{}' starting at line {}",
            source_file,
            acc_start_line
        );
    }

    Ok(out)
}

pub fn split_run_metta_file_line(raw_line: &str) -> Result<Option<(String, Option<Vec<String>>)>> {
    let trimmed = raw_line.trim();
    if trimmed.is_empty() || trimmed.starts_with(';') || trimmed.starts_with("//") {
        return Ok(None);
    }

    let mut in_string = false;
    let mut escaped = false;
    let mut comment_at: Option<(usize, usize)> = None;
    let mut it = trimmed.char_indices().peekable();
    while let Some((idx, ch)) = it.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => {
                comment_at = Some((idx, 1));
                break;
            },
            '/' => {
                if let Some((_, '/')) = it.peek() {
                    comment_at = Some((idx, 2));
                    break;
                }
            },
            _ => {},
        }
    }

    let (cmd_part, expected_surface) = if let Some((idx, marker_len)) = comment_at {
        let cmd = trimmed[..idx].trim();
        if cmd.is_empty() {
            return Ok(None);
        }
        let comment = trimmed[idx + marker_len..].trim();
        let expected = parse_expected_surface_directive(comment)?;
        (cmd.to_string(), expected)
    } else {
        (trimmed.to_string(), None)
    };

    if cmd_part.is_empty() {
        return Ok(None);
    }
    Ok(Some((cmd_part, expected_surface)))
}

/// Hyperon compatibility mode accepts occasional prose/header lines in script files.
/// These are non-empty lines that are not MeTTa forms/commands and contain whitespace.
pub fn is_hyperon_compat_ignorable_prose_line(line: &str) -> bool {
    let trimmed = line.trim();
    if trimmed.is_empty()
        || trimmed.starts_with(';')
        || trimmed.starts_with("//")
        || trimmed.starts_with('!')
        || trimmed.starts_with('(')
        || trimmed.starts_with('$')
    {
        return false;
    }
    trimmed.chars().any(char::is_whitespace)
}

fn is_batch_binding_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_batch_binding_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn parse_batch_binding_lhs(lhs: &str) -> Option<(String, usize)> {
    let name_and_index = lhs.strip_prefix('$')?.trim();
    if name_and_index.is_empty() {
        return None;
    }
    if let Some((name_part, index_part_with_bracket)) = name_and_index.split_once('[') {
        let name = name_part.trim();
        if name.is_empty() {
            return None;
        }
        let mut chars = name.chars();
        let first = chars.next()?;
        if !is_batch_binding_ident_start(first) || !chars.all(is_batch_binding_ident_continue) {
            return None;
        }
        let index_part = index_part_with_bracket.trim();
        let index_str = index_part.strip_suffix(']')?.trim();
        if index_str.is_empty() || !index_str.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let index = index_str.parse::<usize>().ok()?;
        Some((name.to_string(), index))
    } else {
        let name = name_and_index.trim();
        let mut chars = name.chars();
        let first = chars.next()?;
        if !is_batch_binding_ident_start(first) || !chars.all(is_batch_binding_ident_continue) {
            return None;
        }
        Some((name.to_string(), 0))
    }
}

pub fn parse_batch_capture_assignment(line: &str) -> Option<BatchCaptureAssignment> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return None;
    }

    let mut in_string = false;
    let mut escaped = false;
    let mut eq_at: Option<usize> = None;
    for (idx, ch) in trimmed.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '=' => {
                eq_at = Some(idx);
                break;
            },
            _ => {},
        }
    }
    let eq_at = eq_at?;
    let left = trimmed[..eq_at].trim();
    let right = trimmed[eq_at + 1..].trim();
    if right.is_empty() {
        return None;
    }
    let (name, index) = parse_batch_binding_lhs(left)?;
    Some(BatchCaptureAssignment { name, rhs: right.to_string(), index })
}

pub fn substitute_batch_bindings(input: &str, bindings: &HashMap<String, String>) -> String {
    if bindings.is_empty() {
        return input.to_string();
    }
    let chars: Vec<char> = input.chars().collect();
    let mut out = String::with_capacity(input.len());
    let mut i = 0usize;
    let mut in_string = false;
    let mut escaped = false;

    while i < chars.len() {
        let ch = chars[i];
        if in_string {
            out.push(ch);
            if escaped {
                escaped = false;
            } else {
                match ch {
                    '\\' => escaped = true,
                    '"' => in_string = false,
                    _ => {},
                }
            }
            i += 1;
            continue;
        }

        if ch == '"' {
            in_string = true;
            out.push(ch);
            i += 1;
            continue;
        }

        if ch == '$' && i + 1 < chars.len() && is_batch_binding_ident_start(chars[i + 1]) {
            let mut j = i + 2;
            while j < chars.len() && is_batch_binding_ident_continue(chars[j]) {
                j += 1;
            }
            let name: String = chars[i + 1..j].iter().collect();
            if let Some(value) = bindings.get(&name) {
                out.push_str(value);
            } else {
                out.push('$');
                out.push_str(&name);
            }
            i = j;
            continue;
        }

        out.push(ch);
        i += 1;
    }

    out
}

fn parse_library_alias_token(token: &str) -> Option<String> {
    let trimmed = token.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return None;
    }
    let inner = trimmed[1..trimmed.len() - 1].trim();
    let mut parts = inner.split_whitespace();
    let head = parts.next()?;
    if head != "library" {
        return None;
    }
    let name = parts.next()?.trim();
    if name.is_empty() || parts.next().is_some() {
        return None;
    }
    Some(format!("library:{}", name))
}

fn unquote_import_path_token(token: &str) -> Option<String> {
    if let Some(alias) = parse_library_alias_token(token) {
        return Some(alias);
    }
    if token.len() < 2 || !token.starts_with('"') || !token.ends_with('"') {
        return Some(token.to_string());
    }
    let mut out = String::new();
    let mut chars = token[1..token.len() - 1].chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        let esc = chars.next()?;
        match esc {
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'u' => {
                if chars.next()? != '{' {
                    return None;
                }
                let mut hex = String::new();
                loop {
                    let c = chars.next()?;
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                }
                let code = u32::from_str_radix(&hex, 16).ok()?;
                out.push(char::from_u32(code)?);
            },
            other => out.push(other),
        }
    }
    Some(out)
}

fn tokenize_import_inner(inner: &str) -> Option<Vec<String>> {
    let mut tokens = Vec::new();
    let mut cur = String::new();
    let mut chars = inner.chars();
    let mut paren_depth = 0usize;
    while let Some(ch) = chars.next() {
        match ch {
            '"' => {
                if !cur.trim().is_empty() {
                    tokens.push(cur.clone());
                    cur.clear();
                }
                let mut s = String::from("\"");
                let mut escaped = false;
                let mut closed = false;
                for c in chars.by_ref() {
                    s.push(c);
                    if escaped {
                        escaped = false;
                        continue;
                    }
                    if c == '\\' {
                        escaped = true;
                        continue;
                    }
                    if c == '"' {
                        closed = true;
                        break;
                    }
                }
                if !closed {
                    return None;
                }
                tokens.push(s);
            },
            '(' => {
                paren_depth = paren_depth.saturating_add(1);
                cur.push(ch);
            },
            ')' => {
                if paren_depth == 0 {
                    return None;
                }
                paren_depth -= 1;
                cur.push(ch);
            },
            c if c.is_whitespace() && paren_depth == 0 => {
                if !cur.trim().is_empty() {
                    tokens.push(cur.clone());
                    cur.clear();
                }
            },
            _ => cur.push(ch),
        }
    }
    if paren_depth != 0 {
        return None;
    }
    if !cur.trim().is_empty() {
        tokens.push(cur);
    }
    Some(tokens)
}

pub fn parse_import_directive(line: &str) -> Option<(String, String)> {
    let trimmed = line.trim();
    let body = trimmed.strip_prefix('!').unwrap_or(trimmed).trim();
    let inner = body.strip_prefix('(')?.strip_suffix(')')?.trim();
    let toks = tokenize_import_inner(inner)?;
    if toks.is_empty() {
        return None;
    }
    if toks[0] != "import!" && toks[0] != "import" {
        return None;
    }
    match toks.as_slice() {
        [_op, path] => Some(("&self".to_string(), unquote_import_path_token(path)?)),
        [_op, space, path] if space.starts_with('&') => {
            Some(((*space).clone(), unquote_import_path_token(path)?))
        },
        _ => None,
    }
}

pub fn effective_import_target_space(space: &str, current_default_space: &str) -> String {
    if space == DEFAULT_BATCH_SPACE_IDENT {
        current_default_space.to_string()
    } else {
        space.to_string()
    }
}

fn cycle_chain_for_target(
    stack: &[(PathBuf, String)],
    target: &Path,
    target_space: &str,
) -> Vec<String> {
    let Some(idx) = stack
        .iter()
        .position(|(p, s)| p.as_path() == target && s == target_space)
    else {
        return Vec::new();
    };
    let mut chain: Vec<String> = stack[idx..]
        .iter()
        .map(|(p, _)| p.display().to_string())
        .collect();
    chain.push(target.display().to_string());
    chain
}

fn resolve_import_path_token(
    import_path: &str,
    library_aliases: &HashMap<String, String>,
) -> String {
    if let Some(lib_name) = import_path.strip_prefix("library:") {
        if let Some(path) = library_aliases.get(lib_name) {
            return path.clone();
        }
    }
    import_path.to_string()
}

fn resolve_import_file_path(
    base_dir: &Path,
    import_path: &str,
    library_aliases: &HashMap<String, String>,
) -> PathBuf {
    let import_path = resolve_import_path_token(import_path, library_aliases);
    if let Some(lib_name) = import_path.strip_prefix("library:") {
        // If no explicit alias map entry is provided, use a conservative default:
        // try local `lib/<name>.metta`, then sibling `<name>.metta`.
        let local_lib = base_dir.join("lib").join(format!("{lib_name}.metta"));
        if local_lib.exists() {
            return local_lib;
        }
        let local_plain = base_dir.join(format!("{lib_name}.metta"));
        if local_plain.exists() {
            return local_plain;
        }
        // Last-resort fallback keeps diagnostics readable.
        return base_dir.join(format!("{lib_name}.metta"));
    }

    if !Path::new(&import_path).is_absolute() {
        let cwd_candidate = PathBuf::from(&import_path);
        if cwd_candidate.exists() {
            return cwd_candidate;
        }
    }

    let candidate = if Path::new(&import_path).is_absolute() {
        PathBuf::from(&import_path)
    } else {
        base_dir.join(&import_path)
    };
    if candidate.exists() {
        return candidate;
    }
    if candidate.extension().is_none() {
        let with_metta = candidate.with_extension("metta");
        if with_metta.exists() {
            return with_metta;
        }
    }
    if !Path::new(&import_path).is_absolute() {
        if let Some(parent_dir) = base_dir.parent() {
            let parent_candidate = parent_dir.join(&import_path);
            if parent_candidate.exists() {
                return parent_candidate;
            }
            if parent_candidate.extension().is_none() {
                let with_metta = parent_candidate.with_extension("metta");
                if with_metta.exists() {
                    return with_metta;
                }
            }
        }
    }
    candidate
}

fn is_python_source_path(path: &Path) -> bool {
    path.extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
}

fn expand_metta_file_with_imports_inner(
    file_path: &Path,
    seen: &mut HashSet<PathBuf>,
    stack: &mut Vec<(PathBuf, String)>,
    depth: usize,
    meta: &mut ImportExpansionMeta,
    current_default_space: &str,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>> {
    if depth > 32 {
        anyhow::bail!("import depth exceeded while expanding '{}'", file_path.display());
    }
    let canonical = std::fs::canonicalize(file_path).unwrap_or_else(|_| file_path.to_path_buf());
    // Detect only true recursion cycles (target already in active stack), not
    // repeated imports across disjoint branches/spaces.
    if stack
        .iter()
        .any(|(p, s)| p == &canonical && s == current_default_space)
    {
        meta.skipped_cycles += 1;
        return Ok(Vec::new());
    }
    seen.insert(canonical.clone());
    stack.push((canonical.clone(), current_default_space.to_string()));
    meta.imported_files.insert(canonical.display().to_string());
    let content = std::fs::read_to_string(&canonical)
        .map_err(|e| anyhow::anyhow!("Failed to read '{}': {}", canonical.display(), e))?;
    let base_dir = canonical.parent().unwrap_or_else(|| Path::new("."));
    let mut expanded = Vec::new();

    let coalesced =
        coalesce_source_forms(&content, &canonical.display().to_string(), current_default_space)?;

    for coalesced_line in coalesced {
        let parsed = split_run_metta_file_line(&coalesced_line.text)?;
        if let Some((cmd, _)) = parsed {
            if let Some((space, import_path)) = parse_import_directive(&cmd) {
                meta.directives_seen += 1;
                meta.target_spaces.insert(space.clone());
                if space != "&self" {
                    meta.non_self_directives += 1;
                }
                let effective_space = effective_import_target_space(&space, current_default_space);
                let import_file = resolve_import_file_path(base_dir, &import_path, library_aliases);
                let canonical_target =
                    std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
                let is_python_import =
                    is_python_source_path(&canonical_target) || is_python_source_path(&import_file);
                let will_skip_cycle = stack
                    .iter()
                    .any(|(p, s)| p == &canonical_target && s == &effective_space);
                meta.import_edges.push(ImportEdge {
                    source_file: canonical.display().to_string(),
                    source_line: coalesced_line.source_line,
                    import_path: import_path.clone(),
                    source_space: space.clone(),
                    effective_space: effective_space.clone(),
                    target_file: canonical_target.display().to_string(),
                    skipped_cycle: will_skip_cycle,
                    cycle_chain: cycle_chain_for_target(stack, &canonical_target, &effective_space),
                });
                if is_python_import {
                    // PoC FFI bridge: accept Python imports as foreign modules.
                    // They are tracked in import metadata but intentionally not parsed
                    // as MeTTa source.
                    seen.insert(canonical_target.clone());
                    meta.imported_files
                        .insert(canonical_target.display().to_string());
                    continue;
                }
                let mut nested = expand_metta_file_with_imports_inner(
                    &import_file,
                    seen,
                    stack,
                    depth + 1,
                    meta,
                    &effective_space,
                    library_aliases,
                )?;
                expanded.append(&mut nested);
                continue;
            }
        }
        expanded.push(coalesced_line);
    }

    stack.pop();
    Ok(expanded)
}

pub fn expand_metta_file_with_imports(
    file_path: &Path,
    seen: &mut HashSet<PathBuf>,
    depth: usize,
    meta: &mut ImportExpansionMeta,
    current_default_space: &str,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>> {
    let mut stack: Vec<(PathBuf, String)> = Vec::new();
    expand_metta_file_with_imports_inner(
        file_path,
        seen,
        &mut stack,
        depth,
        meta,
        current_default_space,
        library_aliases,
    )
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
    meta.directives_seen += 1;
    meta.target_spaces.insert(source_space.to_string());
    if source_space != DEFAULT_BATCH_SPACE_IDENT {
        meta.non_self_directives += 1;
    }

    let source_path = Path::new(source_file);
    let base_dir = source_path.parent().unwrap_or_else(|| Path::new("."));
    let import_file = resolve_import_file_path(base_dir, import_path, library_aliases);
    let canonical_target =
        std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
    let is_python_import =
        is_python_source_path(&canonical_target) || is_python_source_path(&import_file);
    let will_skip_cycle = false;
    let cycle_chain = Vec::new();
    let effective_space = effective_import_target_space(source_space, current_default_space);
    meta.import_edges.push(ImportEdge {
        source_file: source_file.to_string(),
        source_line,
        import_path: import_path.to_string(),
        source_space: source_space.to_string(),
        effective_space: effective_space.clone(),
        target_file: canonical_target.display().to_string(),
        skipped_cycle: will_skip_cycle,
        cycle_chain,
    });
    if is_python_import {
        seen.insert(canonical_target.clone());
        meta.imported_files
            .insert(canonical_target.display().to_string());
        return Ok(Vec::new());
    }

    let mut nested = expand_metta_file_with_imports(
        &import_file,
        seen,
        0,
        meta,
        &effective_space,
        library_aliases,
    )?;
    meta.expanded_lines += nested.len();
    Ok(std::mem::take(&mut nested))
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
    fn resolve_import_file_path_uses_library_alias_map() {
        let base = Path::new("/home/zar/claude/hyperon/PeTTa/examples");
        let mut aliases = HashMap::new();
        aliases.insert(
            "lib_pln".to_string(),
            "repl/src/examples/petta_adapted/lib/lib_pln.metta".to_string(),
        );
        let resolved = resolve_import_file_path(base, "library:lib_pln", &aliases);
        assert!(
            resolved.ends_with("repl/src/examples/petta_adapted/lib/lib_pln.metta"),
            "library alias should map to configured path"
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
        let rel = Path::new("repl/src/examples/petta_adapted/python_import.metta");
        let local = Path::new("src/examples/petta_adapted/python_import.metta");
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
