/// MORK backend for MeTTa evaluation.
///
/// Translates MeTTa equations (SExpr pairs) and a query SExpr into a MORK MM2 program,
/// runs it to fixpoint, and returns the normal-form results.
///
/// ## Encoding
///
/// For each equation `(= lhs rhs)`:
///
/// **Base case** (no known-function calls in RHS):
/// If multiple base equations share the same `lhs`, they are grouped into one
/// MM2 rule that emits all matching RHS results in one transition.
/// ```mm2
/// (exec (priority name)
///   (, (metta-query $qid lhs))
///   (O (+ (metta-result $qid rhs1))
///      ...
///      (+ (metta-result $qid rhsN))
///      (- (metta-query $qid lhs))))
/// ```
///
/// **Recursive case** (RHS contains N calls to known functions at positions p0..pN-1):
///
/// Uses parallel unfold/fold: all sub-queries spawned simultaneously, fold waits for ALL.
///
/// ```mm2
/// (exec (priority unfold-name)
///   (, (metta-query $qid lhs))
///   (O (+ (metta-query (sub-0 $qid) calls[0]))
///      ...
///      (+ (metta-query (sub-N-1 $qid) calls[N-1]))
///      (+ (wait-name $qid ctx...))
///      (- (metta-query $qid lhs))))
///
/// (exec (priority fold-name)
///   (, (wait-name $qid ctx...)
///      (metta-result (sub-0 $qid) $sr0)
///      ...
///      (metta-result (sub-N-1 $qid) $srN-1))
///   (O (+ (metta-result $qid assembled-rhs))
///      (- (wait-name $qid ctx...))
///      (- (metta-result (sub-0 $qid) $sr0))
///      ...))
/// ```
///
/// The query is wrapped as `(metta-query q0 expr)`.
/// Results are read back from `(metta-result q0 ...)` facts.

#[cfg(feature = "mork-backend")]
pub mod mork_eval {
    use mettail_runtime::MorkExecutionLimits;
    use mork::space::Space;
    use std::collections::HashSet;

    use super::SExpr;

    /// Raw MM2 execution result from the MORK kernel.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct MorkProgramRun {
        /// Number of transitions performed by `Space::metta_calculus`.
        pub steps: usize,
        /// Full post-run atomspace dump in MM2 S-expression form.
        pub dump: String,
    }

    /// Convert a MeTTa SExpr to a MORK MM2 S-expression string.
    /// Variables ($x) and symbols pass through unchanged.
    pub fn sexpr_to_mm2(e: &SExpr) -> String {
        match e {
            SExpr::Atom(s) => s.clone(),
            SExpr::List(items) => {
                if items.is_empty() {
                    "Empty".to_string()
                } else {
                    let parts: Vec<_> = items.iter().map(sexpr_to_mm2).collect();
                    format!("({})", parts.join(" "))
                }
            },
        }
    }

    /// Get the head symbol of an SExpr if it's a function application.
    fn head_symbol(e: &SExpr) -> Option<&str> {
        match e {
            SExpr::List(items) if !items.is_empty() => {
                if let SExpr::Atom(s) = &items[0] {
                    Some(s.as_str())
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    /// Collect all head symbols that have equations.
    pub fn function_heads(eqs: &[(SExpr, SExpr)]) -> HashSet<String> {
        let mut heads = HashSet::new();
        for (lhs, _) in eqs {
            if let Some(h) = head_symbol(lhs) {
                heads.insert(h.to_string());
            }
        }
        heads
    }

    /// Collect ALL sub-expressions in `rhs` (including top level) that are calls to
    /// known functions, in left-to-right order. Stops descending into a call once found
    /// (calls are treated as atomic units — their arguments are not separately reducible).
    ///
    /// Returns a list of `(sub_call_expr, path_from_rhs)` pairs.
    fn find_all_reducible_calls<'a>(
        rhs: &'a SExpr,
        known_heads: &HashSet<String>,
    ) -> Vec<(&'a SExpr, Vec<usize>)> {
        let mut calls = Vec::new();
        collect_reducible_calls(rhs, known_heads, vec![], &mut calls);
        calls
    }

    fn collect_reducible_calls<'a>(
        expr: &'a SExpr,
        known_heads: &HashSet<String>,
        path: Vec<usize>,
        out: &mut Vec<(&'a SExpr, Vec<usize>)>,
    ) {
        // If this expression itself is a call to a known function, record it and stop.
        // This covers both the top-level case (= (f $x) (g $x)) and nested cases.
        if let Some(h) = head_symbol(expr) {
            if known_heads.contains(h) {
                out.push((expr, path));
                return;
            }
        }
        // Otherwise recurse into children to find reducible sub-calls.
        if let SExpr::List(items) = expr {
            for (i, item) in items.iter().enumerate() {
                let mut child_path = path.clone();
                child_path.push(i);
                collect_reducible_calls(item, known_heads, child_path, out);
            }
        }
    }

    /// Replace the sub-expression at `path` in `expr` with `replacement`.
    fn replace_at_path(expr: &SExpr, path: &[usize], replacement: &SExpr) -> SExpr {
        if path.is_empty() {
            return replacement.clone();
        }
        match expr {
            SExpr::List(items) => {
                let mut new_items = items.clone();
                if path[0] < new_items.len() {
                    new_items[path[0]] = replace_at_path(&items[path[0]], &path[1..], replacement);
                }
                SExpr::List(new_items)
            },
            _ => expr.clone(),
        }
    }

    /// Collect all free variables (starting with $) in an SExpr.
    fn free_vars(e: &SExpr) -> Vec<String> {
        let mut vars = Vec::new();
        collect_vars(e, &mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_vars(e: &SExpr, vars: &mut Vec<String>) {
        match e {
            SExpr::Atom(s) if s.starts_with('$') => vars.push(s.clone()),
            SExpr::List(items) => items.iter().for_each(|i| collect_vars(i, vars)),
            _ => {},
        }
    }

    /// Build the complete MM2 program from equations and a query.
    ///
    /// Returns the MM2 source as bytes for `Space::add_all_sexpr`.
    pub fn build_mork_program_with_limits(
        eqs: &[(SExpr, SExpr)],
        query: &SExpr,
        limits: MorkExecutionLimits,
    ) -> Vec<u8> {
        let known_heads = function_heads(eqs);
        let depth = limits.rule_copies.max(1);

        // For each recursive equation, precompute the sub-call chain info.
        struct RecursiveEq {
            lhs_mm2: String,
            // MM2 strings for each sub-call expression (in order)
            sub_calls_mm2: Vec<String>,
            // Names of sub-result variables: $sr0, $sr1, ...
            // (length = sub_calls_mm2.len())
            // Wait token: (wait-{ridx} $qid {wait_vars_list})
            wait_name: String,
            wait_var_list: String, // space-separated lhs vars needed in assembled RHS
            // Final assembled RHS (all sub-calls replaced by $sr0, $sr1, ...)
            assembled_mm2: String,
            rule_idx: usize,
        }
        struct BaseEq {
            lhs_mm2: String,
            rhs_mm2: String,
        }

        let mut recursive_eqs: Vec<RecursiveEq> = Vec::new();
        let mut base_eqs: Vec<BaseEq> = Vec::new();

        for (rule_idx, (lhs, rhs)) in eqs.iter().enumerate() {
            let lhs_mm2 = sexpr_to_mm2(lhs);
            let lhs_vars = free_vars(lhs);
            let calls = find_all_reducible_calls(rhs, &known_heads);

            if calls.is_empty() {
                base_eqs.push(BaseEq { lhs_mm2, rhs_mm2: sexpr_to_mm2(rhs) });
            } else {
                let sub_calls_mm2: Vec<String> =
                    calls.iter().map(|(e, _)| sexpr_to_mm2(e)).collect();

                // Build assembled RHS: replace each sub-call with $sr{i}.
                // Replace calls in order; paths remain valid because substitution
                // at one position does not shift indices at sibling positions.
                let mut assembled_rhs = rhs.clone();
                for (i, (_, path)) in calls.iter().enumerate() {
                    let var = SExpr::Atom(format!("$sr{i}"));
                    assembled_rhs = replace_at_path(&assembled_rhs, path, &var);
                }
                let assembled_mm2 = sexpr_to_mm2(&assembled_rhs);

                // Wait token carries lhs vars that appear in the assembled RHS or sub-calls.
                let wait_vars: Vec<_> = lhs_vars
                    .iter()
                    .filter(|v| {
                        assembled_mm2.contains(v.as_str())
                            || sub_calls_mm2.iter().any(|s| s.contains(v.as_str()))
                    })
                    .cloned()
                    .collect();
                let wait_var_list = if wait_vars.is_empty() {
                    String::new()
                } else {
                    format!(" {}", wait_vars.join(" "))
                };

                let wait_name = format!("wait-{rule_idx}");
                recursive_eqs.push(RecursiveEq {
                    lhs_mm2,
                    sub_calls_mm2,
                    wait_name,
                    wait_var_list,
                    assembled_mm2,
                    rule_idx,
                });
            }
        }

        let mut rules = Vec::new();

        // Group base equations by identical LHS so overlapping base equations emit all
        // RHS results in one transition.
        let mut grouped_base_eqs: Vec<(String, Vec<String>)> = Vec::new();
        for eq in &base_eqs {
            if let Some((_, rhs_group)) = grouped_base_eqs
                .iter_mut()
                .find(|(lhs_group, _)| lhs_group == &eq.lhs_mm2)
            {
                rhs_group.push(eq.rhs_mm2.clone());
            } else {
                grouped_base_eqs.push((eq.lhs_mm2.clone(), vec![eq.rhs_mm2.clone()]));
            }
        }

        // Phase 1: Unfold rules (priorities 0..depth)
        // Fires first: spawns ALL sub-queries in parallel before base/fold rules run.
        for copy in 0..depth {
            for eq in &recursive_eqs {
                let priority = copy;
                let name = format!("unfold-{}-{copy}", eq.rule_idx);
                let lhs = &eq.lhs_mm2;
                let wait = &eq.wait_name;
                let wvl = &eq.wait_var_list;
                let ridx = eq.rule_idx;

                // Spawn one sub-query per reducible call.
                let spawn_lines: Vec<String> = eq
                    .sub_calls_mm2
                    .iter()
                    .enumerate()
                    .map(|(k, sub)| format!("     (+ (metta-query (sub-{ridx}-{k} $qid) {sub}))"))
                    .collect();
                let spawns = spawn_lines.join("\n");

                rules.push(format!(
                    "(exec ({priority} {name})\n  (, (metta-query $qid {lhs}))\n  (O\n{spawns}\n     (+ ({wait} $qid{wvl}))\n     (- (metta-query $qid {lhs}))))"
                ));
            }
        }

        // Phase 2: Base case rules (priorities depth..2*depth)
        // Fires after unfold: resolves base-case sub-queries.
        for copy in 0..depth {
            for (bidx, (lhs, rhs_group)) in grouped_base_eqs.iter().enumerate() {
                let priority = depth + copy;
                let name = format!("base-{bidx}-{copy}");
                let add_results = rhs_group
                    .iter()
                    .map(|rhs| format!("     (+ (metta-result $qid {rhs}))"))
                    .collect::<Vec<_>>()
                    .join("\n");
                rules.push(format!(
                    "(exec ({priority} {name})\n  (, (metta-query $qid {lhs}))\n  (O\n{add_results}\n     (- (metta-query $qid {lhs}))))"
                ));
            }
        }

        // Phase 3: Fold rules (priorities 2*depth..3*depth)
        // Fires after base: waits for ALL sub-results, then assembles the final result.
        for copy in 0..depth {
            for eq in &recursive_eqs {
                let priority = 2 * depth + copy;
                let name = format!("fold-{}-{copy}", eq.rule_idx);
                let wait = &eq.wait_name;
                let wvl = &eq.wait_var_list;
                let asm = &eq.assembled_mm2;
                let ridx = eq.rule_idx;
                let n = eq.sub_calls_mm2.len();
                let wait_match = format!("({wait} $qid{wvl})");

                // Match ALL sub-results simultaneously.
                let sub_result_matches: Vec<String> = (0..n)
                    .map(|k| format!("     (metta-result (sub-{ridx}-{k} $qid) $sr{k})"))
                    .collect();
                let match_part = sub_result_matches.join("\n");

                let sub_result_removes: Vec<String> = (0..n)
                    .map(|k| format!("     (- (metta-result (sub-{ridx}-{k} $qid) $sr{k}))"))
                    .collect();
                let remove_part = sub_result_removes.join("\n");

                rules.push(format!(
                    "(exec ({priority} {name})\n  (, {wait_match}\n{match_part})\n  (O (+ (metta-result $qid {asm}))\n     (- {wait_match})\n{remove_part}))"
                ));
            }
        }

        // Query fact
        let query_mm2 = sexpr_to_mm2(query);
        let query_fact = format!("(metta-query q0 {query_mm2})");
        let program = format!("{}\n{}\n", rules.join("\n"), query_fact);
        program.into_bytes()
    }

    /// Build the complete MM2 program from equations and a query.
    ///
    /// Uses default MORK execution limits from `mettail-runtime`.
    pub fn build_mork_program(eqs: &[(SExpr, SExpr)], query: &SExpr) -> Vec<u8> {
        build_mork_program_with_limits(eqs, query, MorkExecutionLimits::default())
    }

    /// Parse a MORK dump line that looks like `(metta-result q0 EXPR)`.
    /// Returns the EXPR part as a string if the line matches the top-level query id "q0".
    fn parse_mork_result_line(line: &str) -> Option<String> {
        let line = line.trim();
        if !line.starts_with("(metta-result q0 ") || !line.ends_with(')') {
            return None;
        }
        let inner = &line["(metta-result q0 ".len()..line.len() - 1];
        Some(inner.to_string())
    }

    /// Parse a simple MM2 S-expression string back into an SExpr.
    /// Only handles atoms and nested lists.
    pub fn parse_mm2_to_sexpr(s: &str) -> SExpr {
        let s = s.trim();
        if s.starts_with('(') && s.ends_with(')') {
            let inner = &s[1..s.len() - 1];
            let items = split_sexpr_args(inner);
            SExpr::List(items.into_iter().map(|i| parse_mm2_to_sexpr(i)).collect())
        } else {
            SExpr::Atom(s.to_string())
        }
    }

    /// Split a flat string of S-expression arguments (handling nested parens).
    fn split_sexpr_args(s: &str) -> Vec<&str> {
        let mut args = Vec::new();
        let mut depth = 0usize;
        let mut start = 0usize;
        let chars: Vec<_> = s.char_indices().collect();
        for (i, c) in &chars {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                ' ' | '\t' | '\n' if depth == 0 => {
                    let part = &s[start..*i];
                    if !part.is_empty() {
                        args.push(part);
                    }
                    start = i + 1;
                },
                _ => {},
            }
        }
        let part = &s[start..];
        if !part.trim().is_empty() {
            args.push(part.trim());
        }
        args
    }

    /// Run MORK on the given equations and query, returning all normal-form results.
    ///
    /// Results are deduplicated. Returns `Ok(Vec<SExpr>)` or `Err(String)` on failure.
    pub fn run_mork_query_with_limits(
        eqs: &[(SExpr, SExpr)],
        query: &SExpr,
        limits: MorkExecutionLimits,
    ) -> Result<Vec<SExpr>, String> {
        let program = build_mork_program_with_limits(eqs, query, limits);
        let run = run_mm2_program_with_limits(&program, limits)?;

        let mut results = Vec::new();
        for line in run.dump.lines() {
            if let Some(result_str) = parse_mork_result_line(line) {
                let r = parse_mm2_to_sexpr(&result_str);
                // Preserve duplicates: HE spec uses list/multiset semantics.
                results.push(r);
            }
        }

        Ok(results)
    }

    /// Run MORK on the given equations and query using default execution limits.
    ///
    /// Results are deduplicated. Returns `Ok(Vec<SExpr>)` or `Err(String)` on failure.
    pub fn run_mork_query(eqs: &[(SExpr, SExpr)], query: &SExpr) -> Result<Vec<SExpr>, String> {
        run_mork_query_with_limits(eqs, query, MorkExecutionLimits::default())
    }

    /// Run a raw MM2 program in MORK and return transitions + final dump.
    pub fn run_mm2_program_with_limits(
        program: &[u8],
        limits: MorkExecutionLimits,
    ) -> Result<MorkProgramRun, String> {
        let mut space = Space::new();
        space
            .add_all_sexpr(program)
            .map_err(|e| format!("MORK load error: {e:?}"))?;

        let steps = space.metta_calculus(limits.max_steps);

        let mut out_buf = Vec::new();
        space
            .dump_all_sexpr(&mut out_buf)
            .map_err(|e| format!("MORK dump error: {e:?}"))?;
        let dump = String::from_utf8_lossy(&out_buf).to_string();

        Ok(MorkProgramRun { steps, dump })
    }

    /// Run a raw MM2 program in MORK with default execution limits.
    pub fn run_mm2_program(program: &[u8]) -> Result<MorkProgramRun, String> {
        run_mm2_program_with_limits(program, MorkExecutionLimits::default())
    }
}

/// Minimal SExpr compatible with metta_surface::SExpr for standalone testing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn atom(s: impl Into<String>) -> Self {
        SExpr::Atom(s.into())
    }
    pub fn list(items: Vec<SExpr>) -> Self {
        SExpr::List(items)
    }
}
