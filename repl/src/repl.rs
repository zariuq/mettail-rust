use crate::examples::{Example, ExampleCategory};
use crate::lookup_plan::{try_load_lookup_plan, validate_he_mork_backend_contract};
use crate::metta_surface::{
    extract_state_out_atom, looks_like_surface_metta, MeTTaSurfaceSession, SurfaceOutcome,
    SurfaceProfile, SurfaceStmt, SurfaceSyntaxPolicy,
};
use crate::pretty::format_term_pretty;
use crate::registry::LanguageRegistry;
use crate::state::ReplState;
use anyhow::Result;
use colored::Colorize;
use mettail_query::run_query as query_run_query;
use mettail_runtime::{
    aggregate_core_eval_diagnostics, build_core_eval_diagnostics,
    resolve_core_ground_eval_enabled_with_contracts, resolve_runtime_dispatch_contracts,
    AscentResults, CoreEvalDiagnostics, Language, OracleQuery,
    RewriteEvalDiagnostics as SurfaceEvalDiagnostics, RuntimeBackend, RuntimeExecutionPolicy,
    RuntimeOptimizationHints, TermInfo,
};
use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result as RustyResult};
use std::any::Any;
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;
use std::time::Instant;

/// Replace whole-word occurrences of env-bound identifiers in the input with their display form.
/// This allows `x && true` to work when `x = true`, even though the grammar requires `bool:x` for
/// Bool variables (only Int gets bare Ident to avoid reduce-reduce conflicts).
fn pre_substitute_env(input: &str, language: &dyn Language, env: &dyn Any) -> String {
    let bindings = language.list_env(env);
    if bindings.is_empty() {
        return input.to_string();
    }
    // Sort by name length descending so "foobar" is replaced before "foo"
    let mut bindings: Vec<_> = bindings.into_iter().map(|(n, d, _)| (n, d)).collect();
    bindings.sort_by_key(|b| std::cmp::Reverse(b.0.len()));

    let mut result = input.to_string();
    for (name, display) in bindings {
        result = replace_whole_word(&result, &name, &display);
    }
    result
}

/// Replace whole-word occurrences of `needle` with `replacement`.
/// Word boundary: preceded/followed by non-identifier char or start/end.
fn replace_whole_word(haystack: &str, needle: &str, replacement: &str) -> String {
    if needle.is_empty() {
        return haystack.to_string();
    }
    let mut result = String::with_capacity(haystack.len());
    let mut i = 0;
    let haystack_bytes = haystack.as_bytes();
    let needle_bytes = needle.as_bytes();
    let n_len = needle_bytes.len();

    while i <= haystack.len().saturating_sub(n_len) {
        if haystack[i..].starts_with(needle) {
            let at_start = i == 0;
            let at_end = i + n_len == haystack.len();
            let prev_ok = at_start || !is_identifier_char(haystack_bytes[i - 1]);
            let next_ok = at_end || !is_identifier_char(haystack_bytes[i + n_len]);
            if prev_ok && next_ok {
                result.push_str(replacement);
                i += n_len;
                continue;
            }
        }
        result.push(char::from(haystack_bytes[i]));
        i += 1;
    }
    result.push_str(&haystack[i..]);
    result
}

fn is_identifier_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

use crate::run_metta_file::{
    expand_import_directive_from_source, expand_metta_file_with_imports, expected_surface_mismatch,
    is_hyperon_compat_ignorable_prose_line, parse_batch_capture_assignment, parse_import_directive,
    retarget_surface_stmt, run_metta_file_report_json, run_metta_file_report_jsonl,
    split_run_metta_file_line, substitute_batch_bindings, BatchBindingEvent, ImportExpansionMeta,
    RunMettaFileEntry, RunReportMode, RuntimeImportStats, DEFAULT_BATCH_SPACE_IDENT,
};

/// The main REPL
pub struct Repl {
    state: ReplState,
    registry: LanguageRegistry,
    editor: DefaultEditor,
    metta_surface_session: Option<MeTTaSurfaceSession>,
    last_surface_results: Option<Vec<String>>,
    last_core_diagnostics: Option<CoreEvalDiagnostics>,
    batch_quiet: bool,
    suppress_output: bool,
    execution_policy_override: RuntimeExecutionPolicy,
}

impl Repl {
    fn core_ground_eval_policy_enabled() -> bool {
        std::env::var_os("METTAIL_CORE_GROUND_EVAL").is_some()
    }

    fn current_runtime_optimization_hints(&self) -> RuntimeOptimizationHints {
        let Some(language_name) = self.state.language_name() else {
            return RuntimeOptimizationHints::default();
        };
        let Ok(language) = self.registry.get(language_name) else {
            return RuntimeOptimizationHints::default();
        };
        language.metadata().runtime_optimization_hints()
    }

    fn effective_core_ground_eval_enabled(&self) -> bool {
        let hints = self.current_runtime_optimization_hints();
        let contracts = resolve_runtime_dispatch_contracts(hints);
        resolve_core_ground_eval_enabled_with_contracts(
            Self::core_ground_eval_policy_enabled(),
            hints,
            contracts,
        )
    }

    /// Create a new REPL
    pub fn new(registry: LanguageRegistry) -> RustyResult<Self> {
        let editor = DefaultEditor::new()?;
        Ok(Self {
            state: ReplState::new(),
            registry,
            editor,
            metta_surface_session: None,
            last_surface_results: None,
            last_core_diagnostics: None,
            batch_quiet: false,
            suppress_output: false,
            execution_policy_override: RuntimeExecutionPolicy::default(),
        })
    }

    pub fn name_str(&self) -> Option<&str> {
        self.state.language_name()
    }

    fn supports_surface_metta_runner(&self) -> bool {
        let Some(language_name) = self.state.language_name() else {
            return false;
        };
        let Ok(language) = self.registry.get(language_name) else {
            return false;
        };
        language.metadata().supports_surface_metta_runner()
    }

    fn detect_surface_profile(&self) -> SurfaceProfile {
        if let Some(name) = self.state.language_name() {
            if name.eq_ignore_ascii_case("mettahe") {
                return SurfaceProfile::HE;
            }
        }
        SurfaceProfile::Legacy
    }

    fn required_lookup_plan_dialect(&self) -> Option<&'static str> {
        let language_name = self.state.language_name()?;
        if language_name.eq_ignore_ascii_case("mettahe") {
            return Some("he");
        }
        if language_name.to_ascii_lowercase().contains("petta") {
            return Some("petta");
        }
        None
    }

    fn ensure_lookup_plan_contract_for_active_language(&self) -> Result<()> {
        let Some(dialect_key) = self.required_lookup_plan_dialect() else {
            return Ok(());
        };
        match try_load_lookup_plan(dialect_key) {
            Ok(Some(_)) => Ok(()),
            Ok(None) => anyhow::bail!(
                "lookup-plan artifacts are required for language '{}': missing {}.lookup_plan.json/checksum",
                self.state.language_name().unwrap_or("<unknown>"),
                dialect_key
            ),
            Err(e) => anyhow::bail!(
                "failed to load lookup-plan artifacts for language '{}': {}",
                self.state.language_name().unwrap_or("<unknown>"),
                e
            ),
        }
    }

    fn ensure_core_backend_contract_for_active_language(
        &self,
        backend: RuntimeBackend,
    ) -> Result<()> {
        let Some(language_name) = self.state.language_name() else {
            return Ok(());
        };

        if !language_name.eq_ignore_ascii_case("mettahe") {
            return Ok(());
        }
        if !matches!(backend, RuntimeBackend::Mork) {
            return Ok(());
        }

        let loaded = try_load_lookup_plan("he")?.ok_or_else(|| {
            anyhow::anyhow!(
                "HE MORK backend requires Lean lookup-plan artifacts: missing he.lookup_plan.json/checksum"
            )
        })?;
        validate_he_mork_backend_contract(&loaded.artifact).map_err(|e| {
            anyhow::anyhow!("HE MORK backend contract check failed against Lean artifact: {e}")
        })
    }

    fn ensure_metta_surface_session(&mut self) -> &mut MeTTaSurfaceSession {
        if self.metta_surface_session.is_none() {
            let profile = self.detect_surface_profile();
            let mut session = MeTTaSurfaceSession::with_profile(profile);
            session.set_core_ground_eval_enabled(self.effective_core_ground_eval_enabled());
            self.metta_surface_session = Some(session);
        }
        self.metta_surface_session
            .as_mut()
            .expect("session must exist")
    }

    fn reachable_normal_forms<'a>(
        results: &'a AscentResults,
        start_id: u64,
    ) -> Vec<&'a mettail_runtime::TermInfo> {
        let term_by_id = |id: u64| results.all_terms.iter().find(|t| t.term_id == id);
        let Some(start) = term_by_id(start_id) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut visited: HashSet<u64> = HashSet::new();
        let mut queue: VecDeque<u64> = VecDeque::from([start.term_id]);
        visited.insert(start.term_id);

        while let Some(id) = queue.pop_front() {
            if let Some(info) = term_by_id(id) {
                if info.is_normal_form {
                    out.push(info);
                    continue;
                }
                for rw in results.rewrites_from(id) {
                    if visited.insert(rw.to_id) {
                        queue.push_back(rw.to_id);
                    }
                }
            }
        }
        out
    }

    fn decode_metta_surface_reachable_results(
        &self,
        results: &AscentResults,
        start_id: u64,
    ) -> Vec<String> {
        let Some(session) = self.metta_surface_session.as_ref() else {
            return Vec::new();
        };
        let mut seen = HashSet::new();
        let mut decoded = Vec::new();
        for nf in Self::reachable_normal_forms(results, start_id) {
            if let Some(out_atom) = extract_state_out_atom(&nf.display) {
                let surface = session.decode_atom_to_surface(&out_atom);
                if seen.insert(surface.clone()) {
                    decoded.push(surface);
                }
            }
        }
        decoded.sort();
        decoded
    }

    fn latest_surface_eval_diagnostics(&self) -> Option<SurfaceEvalDiagnostics> {
        self.metta_surface_session
            .as_ref()
            .and_then(|session| session.last_surface_diagnostics())
    }

    fn print_metta_surface_results(&self, decoded: &[String]) {
        if self.suppress_output {
            return;
        }
        if decoded.is_empty() {
            return;
        }
        println!();
        if decoded.len() == 1 {
            println!("{} {}", "Surface result:".bold(), decoded[0].green());
            println!();
            return;
        }
        println!(
            "{} {}",
            "Surface results:".bold(),
            format!("{} reachable outputs", decoded.len()).dimmed()
        );
        for (idx, item) in decoded.iter().enumerate() {
            println!("  {} {}", format!("[{}]", idx).dimmed(), item.green());
        }
        println!();
    }

    /// Load a language by name (for programmatic use)
    pub fn load_language(&mut self, name: &str) -> Result<()> {
        self.cmd_lang(&[name])
    }

    /// Execute a single command line non-interactively.
    pub fn run_command(&mut self, line: &str) -> Result<()> {
        self.handle_command(line)
    }

    /// Suppress noisy output for non-interactive batch automation.
    pub fn set_batch_quiet(&mut self, quiet: bool) {
        self.batch_quiet = quiet;
    }

    /// Run the REPL
    pub fn run(&mut self) -> Result<()> {
        self.print_banner();

        loop {
            let prompt = self.make_prompt();
            match self.editor.readline(&prompt) {
                Ok(line) => {
                    self.editor.add_history_entry(&line)?;

                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }

                    if let Err(e) = self.handle_command(line) {
                        let error_str = format!("{}", e);
                        let display =
                            crate::pretty::format_parse_error_with_context(line, &error_str);
                        eprintln!("{} {}", "Error:".red().bold(), display);
                    }
                },
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    continue;
                },
                Err(ReadlineError::Eof) => {
                    println!("exit");
                    break;
                },
                Err(err) => {
                    eprintln!("{} {:?}", "Error:".red().bold(), err);
                    break;
                },
            }
        }

        Ok(())
    }

    fn print_banner(&self) {
        println!("{}", "╔════════════════════════════════════════════════════════════╗".cyan());
        println!("{}", "║                   MeTTaIL Term Explorer                    ║".cyan());
        println!("{}", "║                      Version 0.1.0                         ║".cyan());
        println!("{}", "╚════════════════════════════════════════════════════════════╝".cyan());
        println!();
        println!("Type {} for available commands.", "'help'".green());
        println!();
    }

    fn make_prompt(&self) -> String {
        if let Some(language_name) = self.state.language_name() {
            format!("{}> ", language_name.green())
        } else {
            "mettail> ".to_string()
        }
    }

    fn handle_command(&mut self, line: &str) -> Result<()> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return Ok(());
        }

        // Check for assignment syntax: name = term
        if let Some((name, term_str)) = Self::parse_assignment(line) {
            return self.cmd_assign(&name, &term_str);
        }

        // Query: single rule in Ascent form, e.g. query(result) <-- path(term, result), !rw_proc(result, _).
        if line.contains(" <-- ") {
            return self.cmd_query(line);
        }

        if self.supports_surface_metta_runner() && looks_like_surface_metta(line) {
            return self.exec_or_step_term(line, /* step_mode: */ false);
        }

        match parts[0] {
            "help" => self.cmd_help(),
            "lang" => self.cmd_lang(&parts[1..]),
            "load-env" => self.cmd_load_env(&parts[1..]),
            "run-metta-file" => self.cmd_run_metta_file(&parts[1..]),
            "run-mm2-file" => self.cmd_run_mm2_file(&parts[1..]),
            "oracles" => self.cmd_oracles(),
            "oracle-query" => self.cmd_oracle_query(&parts[1..]),
            "languages" => self.cmd_list_languages(),
            "info" => self.cmd_info(),
            "env" => self.cmd_env(),
            "save" => self.cmd_save(&parts[1..]),
            "clear" => self.cmd_clear(&parts[1..]),
            "clear-all" => self.cmd_clear_all(),
            "term" => self.cmd_term(),
            "type" => self.cmd_type(),
            "typeof" => self.cmd_typeof(&parts[1..]),
            "types" => self.cmd_types(),
            "rewrites" => self.cmd_rewrites(),
            "rewrites-all" => self.cmd_rewrites_all(),
            "equations" => self.cmd_equations(),
            "normal-forms" => self.cmd_normal_forms(),
            "relations" => self.cmd_relations(),
            "relation" => self.cmd_relation(&parts[1..]),
            "apply" => self.cmd_apply(&parts[1..]),
            "goto" => self.cmd_goto(&parts[1..]),
            "example" => self.cmd_example(&parts[1..]),
            "list-examples" => self.cmd_list_examples(self.state.language_name().unwrap()),
            "quit" | "exit" => {
                println!("Goodbye!");
                std::process::exit(0);
                #[allow(unreachable_code)]
                Ok::<(), anyhow::Error>(())
            },
            "exec" => self.cmd_exec_term(line.strip_prefix("exec").unwrap()),
            "step" => self.cmd_step_term(line.strip_prefix("step").unwrap()),
            _ => {
                anyhow::bail!(
                    "Unknown command: '{}'. Type 'help' for available commands.",
                    parts[0]
                )
            },
        }
    }

    /// Parse assignment syntax: name = term
    /// Returns (name, term_string) if it's an assignment, None otherwise
    fn parse_assignment(line: &str) -> Option<(String, String)> {
        // Look for = that's not inside parentheses or brackets
        let mut paren_depth = 0;
        let mut bracket_depth = 0;

        for (i, ch) in line.char_indices() {
            match ch {
                '(' | '{' => paren_depth += 1,
                ')' | '}' => paren_depth -= 1,
                '[' => bracket_depth += 1,
                ']' => bracket_depth -= 1,
                '=' if paren_depth == 0 && bracket_depth == 0 => {
                    let name = line[..i].trim();
                    let term_str = line[i + 1..].trim();

                    // Validate name is a valid identifier (alphanumeric + underscore, starts with letter)
                    if !name.is_empty()
                        && name
                            .chars()
                            .next()
                            .map(|c| c.is_alphabetic())
                            .unwrap_or(false)
                        && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                        && !term_str.is_empty()
                    {
                        return Some((name.to_string(), term_str.to_string()));
                    }
                },
                _ => {},
            }
        }
        None
    }

    fn cmd_help(&self) -> Result<()> {
        println!();
        println!("{}", "Available commands:".bold());
        println!();
        println!("{}", "  Language Management:".yellow());
        println!("    {}        Show available languages", "languages".green());
        println!("    {}  Open language", "lang <name>".green());
        println!("    {}              Show language information", "{lang_name}> info".green());
        println!();
        println!("{}", "  Term Input:".yellow());
        println!(
            "    {}    Execute a program (direct evaluation → result)",
            "exec <term>".green()
        );
        println!(
            "    {}    Step-by-step: show initial term, use {} to reduce",
            "step <term>".green(),
            "apply 0".cyan()
        );
        println!(
            "    {}      MeTTa surface (surface-capable language): {}, {}, {}",
            "surface".green(),
            "!(expr)".cyan(),
            "(= lhs rhs)".cyan(),
            "(: atom type)".cyan()
        );
        println!(
            "    {}      Space ops: {}, {}, {}",
            "surface".green(),
            "(add-atom! [&space] (= ...|: ...))".cyan(),
            "(new-space[!] [&space])".cyan(),
            "!(in-space &space expr)".cyan()
        );
        println!(
            "    {}      Handle alloc: {}",
            "surface".green(),
            "!(new-space!)  -> returns fresh &spaceN".cyan()
        );
        println!(
            "    {}      Space aliases: {}, {}",
            "surface".green(),
            "!(match &space a b)".cyan(),
            "!(type-check &space x T), !(cast &space x T)".cyan()
        );
        println!(
            "    {}      File import (run-metta-file): {}",
            "surface".green(),
            "!(import! &self|&tmp \"other.metta\")".cyan()
        );
        println!("    {}    Load example program", "example <name>".green());
        println!("    {}    List available examples", "list-examples".green());
        println!();
        println!("{}", "  Environment:".yellow());
        println!("    {} Define a named term", "<name> = <term>".green());
        println!("    {}      Save current term to environment", "save <name>".green());
        println!("    {}               Show all environment bindings", "env".green());
        println!("    {}    Remove a binding", "clear <name>".green());
        println!("    {}         Clear all bindings", "clear-all".green());
        println!("    {} Load declarations from file", "load-env <file>".green());
        println!(
            "    {} Execute a surface .metta file (surface-capable language)",
            "run-metta-file <file> [--report=json|jsonl] [--report-file <path>] [--surface-fuel <n>] [--core-fuel <n>] [--surface-first-branch] [--surface-exact-priority] [--surface-memo|--surface-no-memo] [--surface-deterministic] [--mork-backend] [--mork-rule-copies <n>] [--mork-max-steps <n>]".green()
        );
        println!(
            "    {} Execute raw MM2 file in MORK (feature-gated)",
            "run-mm2-file <file> [--mork-max-steps <n>]".green()
        );
        println!(
            "    {} Expectations in file comments: {}, {}",
            "surface assertions".green(),
            "!foo ;=> true".cyan(),
            "!(f x) // expect: a|b".cyan()
        );
        println!(
            "    {} Batch bindings in file: {}",
            "surface batch".green(),
            "$tmp = !(new-space!), $vals[1] = !(choose ...)".cyan()
        );
        println!();
        println!("{}", "  Type Inspection:".yellow());
        println!("    {}              Show type of current term", "type".green());
        println!("    {}             Show all variable types", "types".green());
        println!("    {}  Show type of specific variable", "typeof <var>".green());
        println!();
        println!("{}", "  Navigation:".yellow());
        println!("    {}           List rewrites from current term", "rewrites".green());
        println!("    {}         List all rewrites", "rewrites-all".green());
        println!("    {}        Show normal forms", "normal-forms".green());
        println!(
            "    {} Apply one rewrite from current term (use after {})",
            "apply <N>".green(),
            "step".cyan()
        );
        println!("    {}              Go to normal form N", "goto <N>".green());
        println!();
        println!("{}", "  Relations:".yellow());
        println!("    {}         List all computed relations", "relations".green());
        println!("    {} Show tuples in a relation", "relation <name>".green());
        println!();
        println!("{}", "  Query:".yellow());
        println!(
            "    {}  Run a Datalog rule over step results (e.g. {}).",
            "head(args) <-- body.".green(),
            "query(result) <-- path(current_term, result), !rw_proc(result, _)".dimmed()
        );
        println!();
        println!("{}", "  Oracles:".yellow());
        println!("    {}       List oracle endpoints exposed by the language", "oracles".green());
        println!(
            "    {}  Invoke an oracle operation",
            "oracle-query <oracle> <operation> [args...]".green()
        );
        println!();
        println!("{}", "  General:".yellow());
        println!("    {}              Show this help", "help".green());
        println!("    {}        Exit REPL", "quit, exit".green());
        println!();
        println!("{}", "  CLI Batch Examples:".yellow());
        println!(
            "    {}",
            "mettail --lang mettahe --run-metta-file ../hyperon-experimental/python/tests/scripts/b4_nondeterm.metta --report jsonl --report-file .artifacts/ci/he.jsonl".green()
        );
        println!(
            "    {}",
            "mettail --lang mettahe --quiet-batch -c \"(= (id $x) $x)\" -c \"!(id 5)\"".green()
        );
        println!();
        Ok(())
    }

    fn cmd_lang(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: lang <language-name>");
        }

        let language_name = args[0];

        if !self.registry.contains(language_name) {
            anyhow::bail!(
                "Language '{}' not found. Use 'list-languages' to see available languages.",
                language_name
            );
        }

        if !self.batch_quiet {
            println!("Loading language: {}", language_name.green());
        }

        // Get the theory from the registry (for display info)
        let language = self.registry.get(language_name)?;

        // Print theory info
        // println!("  ✓ {} categories", theory.categories().len());
        // println!("  ✓ {} constructors", theory.constructor_count());
        // println!("  ✓ {} equations", theory.equation_count());
        // println!("  ✓ {} rewrite rules", theory.rewrite_count());
        let runtime_hints = language.metadata().runtime_optimization_hints();
        let contracts = resolve_runtime_dispatch_contracts(runtime_hints);
        let hinted_core_ground_eval = resolve_core_ground_eval_enabled_with_contracts(
            Self::core_ground_eval_policy_enabled(),
            runtime_hints,
            contracts,
        );

        // Store the theory name in state
        self.state.load_language(language.name());
        if language.metadata().supports_surface_metta_runner() {
            let profile = self.detect_surface_profile();
            let mut session = MeTTaSurfaceSession::with_profile(profile);
            session.set_core_ground_eval_enabled(hinted_core_ground_eval);
            self.metta_surface_session = Some(session);
        } else {
            self.metta_surface_session = None;
        }

        // Try to auto-load environment from repl/src/examples/{theory_name}.txt
        let env_file = format!("repl/src/examples/{}.txt", language_name);
        if std::path::Path::new(&env_file).exists() {
            match self.load_env_from_file(&env_file) {
                Ok(count) if count > 0 => {
                    if !self.batch_quiet {
                        println!("  [{} definitions from {}]", count, env_file);
                    }
                },
                Ok(_) => {}, // Empty file, no message
                Err(e) => {
                    if !self.batch_quiet {
                        println!("  {} Failed to load {}: {}", "⚠".yellow(), env_file, e);
                    }
                },
            }
        }
        if !self.batch_quiet {
            println!();
            println!("{} Language loaded successfully!", "✓".green());
            println!("  {}  direct evaluation (result)", "'exec <term>'".cyan());
            println!(
                "  {}  step-by-step, then {} to reduce",
                "'step <term>'".cyan(),
                "apply 0".cyan()
            );
            println!();
        }

        Ok(())
    }

    fn cmd_list_languages(&self) -> Result<()> {
        println!();
        println!("{}", "Available languages:".bold());
        println!();

        let languages = self.registry.list();
        if languages.is_empty() {
            println!("  {}", "No languages available.".yellow());
            println!("  {}", "Build mettail-examples first with: cargo build".dimmed());
        } else {
            for language in languages {
                println!("  - {}", language.green());
            }
        }

        println!();
        Ok(())
    }

    fn cmd_info(&self) -> Result<()> {
        if let Some(language_name) = self.state.language_name() {
            let language = self.registry.get(language_name)?;
            let meta = language.metadata();

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!("{:^70}", format!("{} Language", meta.name()).bold());
            println!("{}", "═".repeat(70).cyan());

            // Types
            println!();
            println!("{}", "TYPES".yellow().bold());
            for ty in meta.types() {
                let primary = if ty.is_primary { " (primary)" } else { "" };
                let native = ty
                    .native_type
                    .map(|t| format!(" = {}", t))
                    .unwrap_or_default();
                println!("  {}{}{}", ty.name.cyan(), native.dimmed(), primary.dimmed());
            }

            // Terms grouped by type - format: [Label] syntax:Type -| context
            println!();
            println!("{} ({})", "TERMS".yellow().bold(), meta.terms().len());
            for ty in meta.types() {
                let terms: Vec<_> = meta
                    .terms()
                    .iter()
                    .filter(|t| t.type_name == ty.name)
                    .collect();
                if !terms.is_empty() {
                    println!("  {}:", ty.name);
                    for term in terms {
                        let label = format!("[{}]", term.name).cyan();

                        // Build type context from fields
                        let ctx: Vec<String> = term
                            .fields
                            .iter()
                            .map(|f| format!("{}:{}", f.name, f.ty))
                            .collect();

                        let judgement = if ctx.is_empty() {
                            format!("{}:{}", term.syntax, term.type_name)
                        } else {
                            format!(
                                "{}:{} {} {}",
                                term.syntax,
                                term.type_name,
                                "-|".dimmed(),
                                ctx.join(", ")
                            )
                        };

                        println!("    {} {}", label, judgement.green());
                    }
                }
            }

            // Equations - format: [conditions] lhs = rhs
            println!();
            println!("{} ({})", "EQUATIONS".yellow().bold(), meta.equations().len());
            for eq in meta.equations() {
                let cond_str = if eq.conditions.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", eq.conditions.join(", "), "|-".dimmed())
                };
                println!("  {}{} = {}", cond_str, eq.lhs.green(), eq.rhs.green());
            }

            // Rewrites - format: [premise] lhs ~> rhs
            println!();
            println!("{} ({})", "REWRITES".yellow().bold(), meta.rewrites().len());
            for rw in meta.rewrites() {
                let mut parts = Vec::new();

                // Add freshness conditions
                if !rw.conditions.is_empty() {
                    parts.push(rw.conditions.join(", "));
                }

                // Add premise (congruence rule)
                if let Some((s, t)) = rw.premise {
                    parts.push(format!("{} ~> {}", s, t));
                }

                let prefix = if parts.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", parts.join(", "), "|-".dimmed())
                };

                // Add optional name
                let name_str = rw
                    .name
                    .map(|n| format!("[{}] ", n).cyan().to_string())
                    .unwrap_or_default();

                println!("  {}{}{} ~> {}", name_str, prefix, rw.lhs.green(), rw.rhs.green());
            }

            // Logic - custom relations and rules
            let logic_relations = meta.logic_relations();
            let logic_rules = meta.logic_rules();
            if !logic_relations.is_empty() || !logic_rules.is_empty() {
                println!();
                println!("{}", "LOGIC".yellow().bold());

                // Relations
                if !logic_relations.is_empty() {
                    println!("  {}:", "Relations".dimmed());
                    for rel in logic_relations {
                        let signature = format!("{}({})", rel.name, rel.param_types.join(", "));
                        println!("    {}", signature.cyan());
                    }
                }

                // Rules
                if !logic_rules.is_empty() {
                    println!("  {}:", "Rules".dimmed());
                    for rule in logic_rules {
                        println!("    {}", rule.rule.green());
                    }
                }
            }

            let oracles = language.list_oracles();
            if !oracles.is_empty() {
                println!();
                println!("{}", "ORACLES".yellow().bold());
                for oracle in &oracles {
                    let ops = if oracle.operations.is_empty() {
                        "(no operations declared)".dimmed().to_string()
                    } else {
                        oracle.operations.join(", ").green().to_string()
                    };
                    println!("  {} -> {}", oracle.name.cyan(), ops);
                    if let Some(docs) = &oracle.docs {
                        println!("    {}", docs.dimmed());
                    }
                }
            }

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!();
        } else {
            println!("{} No language loaded. Use 'lang <name>' first.", "Info:".yellow());
        }
        Ok(())
    }

    // === Environment Commands ===

    fn cmd_assign(&mut self, name: &str, term_str: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Parse the term WITHOUT clearing var cache
        // This allows shared variables across env definitions (e.g., same `n` in multiple terms)
        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        // Ensure environment exists
        let env = self.state.ensure_environment(|| language.create_env());

        // Add to environment
        language
            .add_to_env(env, name, term.as_ref())
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!("{} {} added to environment", "✓".green(), name.cyan());
        Ok(())
    }

    fn cmd_env(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Environment:".bold());

        if let Some(env) = self.state.environment() {
            if language.is_env_empty(env) {
                println!("  {}", "(empty)".dimmed());
            } else {
                let bindings = language.list_env(env);
                let mut last_comment: Option<&str> = None;

                for (name, value, comment) in &bindings {
                    // Print section comment if it's different from the last one
                    if let Some(c) = comment {
                        if last_comment != Some(c.as_str()) {
                            println!();
                            println!("  {}", format!("// {}", c).dimmed());
                            last_comment = Some(c.as_str());
                        }
                    } else if last_comment.is_some() {
                        // No comment on this item, reset section tracking
                        last_comment = None;
                    }
                    println!("  {} = {}", name.cyan(), value.green());
                }
            }
        } else {
            println!("  {}", "(empty)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_clear(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: clear <name>");
        }

        let name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            if language
                .remove_from_env(env, name)
                .map_err(|e| anyhow::anyhow!("{}", e))?
            {
                println!("{} {} removed from environment", "✓".green(), name.cyan());
            } else {
                println!("{} {} not found in environment", "⚠".yellow(), name);
            }
        } else {
            println!("{} Environment is empty", "⚠".yellow());
        }

        Ok(())
    }

    fn cmd_clear_all(&mut self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            language.clear_env(env);
            println!("{} Environment cleared", "✓".green());
        } else {
            println!("{} Environment is already empty", "⚠".yellow());
        }

        Ok(())
    }

    /// Save the current term to the environment with a given name
    fn cmd_save(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: save <name>");
        }

        let name = args[0];

        // Validate name is a valid identifier
        if !name
            .chars()
            .next()
            .map(|c| c.is_alphabetic())
            .unwrap_or(false)
            || !name.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            anyhow::bail!("Invalid identifier: '{}'", name);
        }

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        // Clone the current term to release the borrow on self.state
        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'term: <expr>' first."))?
            .clone_box();

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Add the current term to the environment
        if let Some(env) = self.state.environment_mut() {
            language
                .add_to_env(env, name, current_term.as_ref())
                .map_err(|e| anyhow::anyhow!("{}", e))?;
            println!("{} {} added to environment", "✓".green(), name.cyan());
        }

        Ok(())
    }

    /// Load term declarations from a file
    fn cmd_load_env(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: load-env <file>");
        }

        let file_path = args[0];

        match self.load_env_from_file(file_path) {
            Ok(count) => {
                if count > 0 {
                    println!(
                        "{} Loaded {} declaration(s) from '{}'",
                        "✓".green(),
                        count,
                        file_path
                    );
                } else {
                    println!("{} No declarations found in '{}'", "ℹ".blue(), file_path);
                }
                Ok(())
            },
            Err(e) => Err(e),
        }
    }

    fn cmd_run_metta_file(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!(
                "Usage: run-metta-file <file> [--report=text|json|jsonl] [--report-file <path>] [--surface-fuel <n>] [--core-fuel <n>] [--surface-first-branch] [--surface-exact-priority] [--surface-memo|--surface-no-memo] [--surface-deterministic] [--mork-backend] [--mork-rule-copies <n>] [--mork-max-steps <n>]"
            );
        }
        if !self.supports_surface_metta_runner() {
            anyhow::bail!(
                "run-metta-file is only available for languages that support surface .metta execution."
            );
        }
        self.ensure_lookup_plan_contract_for_active_language()?;
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;
        let language = self.registry.get(language_name)?;
        let library_aliases: HashMap<String, String> = language
            .metadata()
            .library_aliases()
            .iter()
            .map(|a| (a.name.to_string(), a.path.to_string()))
            .collect();

        let mut report_mode = RunReportMode::Text;
        let mut report_file: Option<String> = None;
        let mut surface_fuel: Option<usize> = None;
        let mut core_fuel: Option<usize> = None;
        let mut surface_first_branch_only = false;
        let mut surface_first_branch_only_explicit = false;
        let mut surface_exact_priority = false;
        let mut surface_exact_priority_explicit = false;
        let mut surface_recursive_memo: Option<bool> = None;
        let mut surface_deterministic = false;
        #[cfg(feature = "mork-backend")]
        let mut mork_backend = false;
        #[cfg(not(feature = "mork-backend"))]
        let mork_backend = false;
        let mut mork_rule_copies: Option<usize> = None;
        let mut mork_max_steps: Option<usize> = None;
        let mut file_path: Option<&str> = None;
        let mut i = 0usize;
        while i < args.len() {
            let arg = args[i];
            if let Some(mode) = arg.strip_prefix("--report=") {
                report_mode = match mode {
                    "text" => RunReportMode::Text,
                    "json" => RunReportMode::Json,
                    "jsonl" => RunReportMode::Jsonl,
                    _ => {
                        anyhow::bail!("unsupported report mode '{mode}', expected text|json|jsonl")
                    },
                };
                i += 1;
                continue;
            }
            if arg == "--report-file" {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("missing path after --report-file");
                }
                report_file = Some(args[i].to_string());
                i += 1;
                continue;
            }
            if let Some(path) = arg.strip_prefix("--report-file=") {
                if path.is_empty() {
                    anyhow::bail!("empty path in --report-file option");
                }
                report_file = Some(path.to_string());
                i += 1;
                continue;
            }
            if arg == "--surface-fuel" {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("missing integer after --surface-fuel");
                }
                surface_fuel =
                    Some(args[i].parse::<usize>().map_err(|_| {
                        anyhow::anyhow!("invalid --surface-fuel value '{}'", args[i])
                    })?);
                i += 1;
                continue;
            }
            if let Some(raw) = arg.strip_prefix("--surface-fuel=") {
                if raw.is_empty() {
                    anyhow::bail!("empty value in --surface-fuel option");
                }
                surface_fuel = Some(
                    raw.parse::<usize>()
                        .map_err(|_| anyhow::anyhow!("invalid --surface-fuel value '{}'", raw))?,
                );
                i += 1;
                continue;
            }
            if arg == "--core-fuel" {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("missing integer after --core-fuel");
                }
                core_fuel = Some(
                    args[i]
                        .parse::<usize>()
                        .map_err(|_| anyhow::anyhow!("invalid --core-fuel value '{}'", args[i]))?,
                );
                i += 1;
                continue;
            }
            if let Some(raw) = arg.strip_prefix("--core-fuel=") {
                if raw.is_empty() {
                    anyhow::bail!("empty value in --core-fuel option");
                }
                core_fuel = Some(
                    raw.parse::<usize>()
                        .map_err(|_| anyhow::anyhow!("invalid --core-fuel value '{}'", raw))?,
                );
                i += 1;
                continue;
            }
            if arg == "--surface-first-branch" {
                surface_first_branch_only = true;
                surface_first_branch_only_explicit = true;
                i += 1;
                continue;
            }
            if arg == "--surface-exact-priority" {
                surface_exact_priority = true;
                surface_exact_priority_explicit = true;
                i += 1;
                continue;
            }
            if arg == "--surface-memo" {
                surface_recursive_memo = Some(true);
                i += 1;
                continue;
            }
            if arg == "--surface-no-memo" {
                surface_recursive_memo = Some(false);
                i += 1;
                continue;
            }
            if arg == "--surface-deterministic" {
                surface_deterministic = true;
                i += 1;
                continue;
            }
            if arg == "--mork-backend" {
                #[cfg(feature = "mork-backend")]
                {
                    mork_backend = true;
                    i += 1;
                    continue;
                }
                #[cfg(not(feature = "mork-backend"))]
                {
                    anyhow::bail!("--mork-backend requires the 'mork-backend' feature flag");
                }
            }
            if arg == "--mork-rule-copies" {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("missing integer after --mork-rule-copies");
                }
                mork_rule_copies = Some(args[i].parse::<usize>().map_err(|_| {
                    anyhow::anyhow!("invalid --mork-rule-copies value '{}'", args[i])
                })?);
                i += 1;
                continue;
            }
            if let Some(raw) = arg.strip_prefix("--mork-rule-copies=") {
                if raw.is_empty() {
                    anyhow::bail!("empty value in --mork-rule-copies option");
                }
                mork_rule_copies =
                    Some(raw.parse::<usize>().map_err(|_| {
                        anyhow::anyhow!("invalid --mork-rule-copies value '{}'", raw)
                    })?);
                i += 1;
                continue;
            }
            if arg == "--mork-max-steps" {
                i += 1;
                if i >= args.len() {
                    anyhow::bail!("missing integer after --mork-max-steps");
                }
                mork_max_steps = Some(args[i].parse::<usize>().map_err(|_| {
                    anyhow::anyhow!("invalid --mork-max-steps value '{}'", args[i])
                })?);
                i += 1;
                continue;
            }
            if let Some(raw) = arg.strip_prefix("--mork-max-steps=") {
                if raw.is_empty() {
                    anyhow::bail!("empty value in --mork-max-steps option");
                }
                mork_max_steps =
                    Some(raw.parse::<usize>().map_err(|_| {
                        anyhow::anyhow!("invalid --mork-max-steps value '{}'", raw)
                    })?);
                i += 1;
                continue;
            }
            if file_path.is_none() {
                file_path = Some(arg);
                i += 1;
                continue;
            }
            anyhow::bail!(
                "unexpected argument '{arg}', usage: run-metta-file <file> [--report=text|json|jsonl] [--report-file <path>] [--surface-fuel <n>] [--core-fuel <n>] [--surface-first-branch] [--surface-exact-priority] [--surface-memo|--surface-no-memo] [--surface-deterministic] [--mork-backend] [--mork-rule-copies <n>] [--mork-max-steps <n>]"
            );
        }
        if surface_deterministic {
            surface_first_branch_only = true;
            surface_exact_priority = true;
        }
        if report_file.is_some() && report_mode == RunReportMode::Text {
            anyhow::bail!("--report-file requires --report=json or --report=jsonl");
        }
        let file_path = file_path.ok_or_else(|| anyhow::anyhow!("missing file path"))?;

        let mut import_seen = HashSet::new();
        let mut import_meta = ImportExpansionMeta::default();
        let initial_expanded_lines = expand_metta_file_with_imports(
            Path::new(file_path),
            &mut import_seen,
            0,
            &mut import_meta,
            DEFAULT_BATCH_SPACE_IDENT,
            &library_aliases,
        )?;
        import_meta.expanded_lines = initial_expanded_lines.len();
        let mut pending_lines: VecDeque<_> = initial_expanded_lines.into_iter().collect();

        let mut skipped = 0usize;
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut failures = Vec::new();
        let mut entries = Vec::new();
        let mut batch_bindings: HashMap<String, String> = HashMap::new();
        let mut binding_events: Vec<BatchBindingEvent> = Vec::new();
        let mut runtime_import_directives = 0usize;
        let mut runtime_import_injected_lines = 0usize;
        let quiet_run = self.batch_quiet && report_mode != RunReportMode::Text;
        let prev_execution_policy_override = self.execution_policy_override;
        let surface_first_branch_override = if surface_deterministic {
            Some(true)
        } else if surface_first_branch_only_explicit {
            Some(surface_first_branch_only)
        } else {
            None
        };
        let surface_exact_priority_override = if surface_deterministic {
            Some(true)
        } else if surface_exact_priority_explicit {
            Some(surface_exact_priority)
        } else {
            None
        };
        let surface_recursive_memo_override = if surface_deterministic {
            Some(true)
        } else {
            surface_recursive_memo
        };
        let run_execution_policy = RuntimeExecutionPolicy {
            surface_fuel,
            core_fuel,
            surface_first_branch_only: surface_first_branch_override,
            surface_exact_priority: surface_exact_priority_override,
            surface_recursive_memo: surface_recursive_memo_override,
            surface_deterministic: if surface_deterministic {
                Some(true)
            } else {
                None
            },
            backend: Some(if mork_backend {
                RuntimeBackend::Mork
            } else {
                RuntimeBackend::Auto
            }),
            mork_rule_copies,
            mork_max_steps,
        };
        let requested_backend = run_execution_policy.backend.unwrap_or(RuntimeBackend::Auto);
        let resolved_backend = if matches!(requested_backend, RuntimeBackend::Auto)
            && language.name() == "MeTTaHE"
            && language.supports_backend(RuntimeBackend::Mork)
        {
            RuntimeBackend::Mork
        } else {
            requested_backend
        };
        self.ensure_core_backend_contract_for_active_language(resolved_backend)?;
        let runtime_hints = self.current_runtime_optimization_hints();
        let dispatch_contracts = resolve_runtime_dispatch_contracts(runtime_hints);
        let surface_policy = run_execution_policy.surface_policy_label(runtime_hints);
        self.execution_policy_override = run_execution_policy;

        if report_mode == RunReportMode::Text {
            println!();
            println!("{} {}", "Running MeTTa file:".bold(), file_path.cyan());
        }

        let surface_syntax_policy = if self.supports_surface_metta_runner() {
            Some(self.ensure_metta_surface_session().syntax_policy())
        } else {
            None
        };

        let mut logical_line_num = 0usize;
        while let Some(expanded_line) = pending_lines.pop_front() {
            logical_line_num += 1;
            let line_num = logical_line_num;
            let parsed_line = match split_run_metta_file_line(&expanded_line.text) {
                Ok(v) => v,
                Err(e) => {
                    self.execution_policy_override = prev_execution_policy_override;
                    return Err(anyhow::anyhow!(
                        "line {} malformed expectation/comment syntax: {}",
                        line_num,
                        e
                    ));
                },
            };
            let Some((line, expected_surface)) = parsed_line else {
                skipped += 1;
                continue;
            };
            let line_substituted = substitute_batch_bindings(&line, &batch_bindings);
            let capture_binding = parse_batch_capture_assignment(&line_substituted);
            let run_line = if let Some(binding) = &capture_binding {
                binding.rhs.clone()
            } else {
                line_substituted.clone()
            };

            if capture_binding.is_none()
                && expected_surface.is_none()
                && surface_syntax_policy == Some(SurfaceSyntaxPolicy::HyperonCompat)
                && is_hyperon_compat_ignorable_prose_line(&run_line)
            {
                skipped += 1;
                continue;
            }

            if capture_binding.is_none() {
                if let Some((source_space, import_path)) = parse_import_directive(&run_line) {
                    runtime_import_directives = runtime_import_directives.saturating_add(1);
                    if report_mode == RunReportMode::Text {
                        println!();
                        println!(
                            "{} {} {}",
                            "[RUN]".cyan().bold(),
                            format!("line {}", line_num).dimmed(),
                            line_substituted.as_str()
                        );
                    }
                    let started = Instant::now();
                    match expand_import_directive_from_source(
                        &expanded_line.source_file,
                        expanded_line.source_line,
                        &source_space,
                        &import_path,
                        &expanded_line.default_space,
                        &mut import_seen,
                        &mut import_meta,
                        &library_aliases,
                    ) {
                        Ok(imported_lines) => {
                            runtime_import_injected_lines =
                                runtime_import_injected_lines.saturating_add(imported_lines.len());
                            for line in imported_lines.into_iter().rev() {
                                pending_lines.push_front(line);
                            }
                            let actual_for_assert: Vec<String> = Vec::new();
                            if let Some(expected) = expected_surface.clone() {
                                if let Some(mismatch) =
                                    expected_surface_mismatch(&expected, &actual_for_assert)
                                {
                                    failed += 1;
                                    entries.push(RunMettaFileEntry {
                                        line: line_num,
                                        input: line_substituted.clone(),
                                        status: "fail",
                                        error: Some(mismatch.clone()),
                                        surface_results: Some(actual_for_assert),
                                        expected_surface: Some(expected),
                                        elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                        source_file: Some(expanded_line.source_file.clone()),
                                        source_line: Some(expanded_line.source_line),
                                        binding_name: None,
                                        binding_value: None,
                                        surface_diagnostics: None,
                                        core_diagnostics: None,
                                    });
                                    if report_mode == RunReportMode::Text {
                                        println!(
                                            "{} {} {}",
                                            "[FAIL]".red().bold(),
                                            format!("line {}", line_num).dimmed(),
                                            mismatch
                                        );
                                    }
                                    failures.push(format!(
                                        "line {}: {} -- {}",
                                        line_num, line_substituted, mismatch
                                    ));
                                    continue;
                                }
                            }
                            passed += 1;
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "pass",
                                error: None,
                                surface_results: Some(Vec::new()),
                                expected_surface,
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: None,
                                binding_value: None,
                                surface_diagnostics: None,
                                core_diagnostics: None,
                            });
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {}",
                                    "[PASS]".green().bold(),
                                    format!("line {}", line_num).dimmed()
                                );
                            }
                            continue;
                        },
                        Err(err) => {
                            let err_msg = err.to_string();
                            failed += 1;
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "fail",
                                error: Some(err_msg.clone()),
                                surface_results: None,
                                expected_surface,
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: None,
                                binding_value: None,
                                surface_diagnostics: None,
                                core_diagnostics: None,
                            });
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {} {}",
                                    "[FAIL]".red().bold(),
                                    format!("line {}", line_num).dimmed(),
                                    err_msg
                                );
                            }
                            failures.push(format!(
                                "line {}: {} -- {}",
                                line_num, line_substituted, err
                            ));
                            continue;
                        },
                    }
                }
            }

            if report_mode == RunReportMode::Text {
                println!();
                println!(
                    "{} {} {}",
                    "[RUN]".cyan().bold(),
                    format!("line {}", line_num).dimmed(),
                    line_substituted.as_str()
                );
            }

            let started = Instant::now();
            let prev_suppress = self.suppress_output;
            if quiet_run {
                self.suppress_output = true;
            }
            let run_result = if self.supports_surface_metta_runner()
                && looks_like_surface_metta(&run_line)
            {
                let parsed = {
                    let session = self.ensure_metta_surface_session();
                    session.parse_line_for_session(&run_line)
                };
                match parsed {
                    Ok(Some(parsed_stmt)) => {
                        let stmt = retarget_surface_stmt(parsed_stmt, &expanded_line.default_space);
                        self.exec_surface_stmt(stmt, /* step_mode: */ false)
                    },
                    Ok(None) => Ok(()),
                    Err(e) => Err(anyhow::anyhow!(
                        "line {} invalid MeTTa surface statement after substitutions: {}",
                        line_num,
                        e
                    )),
                }
            } else {
                self.exec_or_step_term(&run_line, /* step_mode: */ false)
            };
            match run_result {
                Ok(()) => {
                    self.suppress_output = prev_suppress;
                    let surface_results = self.last_surface_results.clone();
                    let surface_diagnostics = self.latest_surface_eval_diagnostics();
                    let core_diagnostics = self.last_core_diagnostics.clone();
                    if let (Some(limit), Some(diag)) = (core_fuel, core_diagnostics.as_ref()) {
                        if diag.rewrite_count > limit {
                            failed += 1;
                            let msg = format!(
                                "core fuel exceeded: rewrite_count {} > {}",
                                diag.rewrite_count, limit
                            );
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "fail",
                                error: Some(msg.clone()),
                                surface_results: surface_results.clone(),
                                expected_surface: expected_surface.clone(),
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: capture_binding.as_ref().map(|b| b.name.clone()),
                                binding_value: None,
                                surface_diagnostics: surface_diagnostics.clone(),
                                core_diagnostics: core_diagnostics.clone(),
                            });
                            failures.push(format!(
                                "line {}: {} -- {}",
                                line_num, line_substituted, msg
                            ));
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {} {}",
                                    "[FAIL]".red().bold(),
                                    format!("line {}", line_num).dimmed(),
                                    msg
                                );
                            }
                            continue;
                        }
                    }
                    let actual_for_assert = surface_results.clone().unwrap_or_default();
                    if let Some(expected) = expected_surface.clone() {
                        if let Some(mismatch) =
                            expected_surface_mismatch(&expected, &actual_for_assert)
                        {
                            failed += 1;
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "fail",
                                error: Some(mismatch.clone()),
                                surface_results,
                                expected_surface: Some(expected),
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: capture_binding.as_ref().map(|b| b.name.clone()),
                                binding_value: None,
                                surface_diagnostics: surface_diagnostics.clone(),
                                core_diagnostics,
                            });
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {} {}",
                                    "[FAIL]".red().bold(),
                                    format!("line {}", line_num).dimmed(),
                                    mismatch
                                );
                            }
                            failures.push(format!(
                                "line {}: {} -- {}",
                                line_num, line_substituted, mismatch
                            ));
                            continue;
                        }
                    }
                    if let Some(binding) = &capture_binding {
                        if actual_for_assert.is_empty() {
                            failed += 1;
                            let msg = format!(
                                "batch binding ${} requires a surface result but got none",
                                binding.name
                            );
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "fail",
                                error: Some(msg.clone()),
                                surface_results: Some(actual_for_assert.clone()),
                                expected_surface: expected_surface.clone(),
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: Some(binding.name.clone()),
                                binding_value: None,
                                surface_diagnostics: surface_diagnostics.clone(),
                                core_diagnostics: core_diagnostics.clone(),
                            });
                            failures.push(format!(
                                "line {}: {} -- {}",
                                line_num, line_substituted, msg
                            ));
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {} {}",
                                    "[FAIL]".red().bold(),
                                    format!("line {}", line_num).dimmed(),
                                    msg
                                );
                            }
                            continue;
                        }
                        if binding.index >= actual_for_assert.len() {
                            failed += 1;
                            let msg = format!(
                                "batch binding ${}[{}] out of range for {} result(s)",
                                binding.name,
                                binding.index,
                                actual_for_assert.len()
                            );
                            entries.push(RunMettaFileEntry {
                                line: line_num,
                                input: line_substituted.clone(),
                                status: "fail",
                                error: Some(msg.clone()),
                                surface_results: Some(actual_for_assert.clone()),
                                expected_surface: expected_surface.clone(),
                                elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                                source_file: Some(expanded_line.source_file.clone()),
                                source_line: Some(expanded_line.source_line),
                                binding_name: Some(binding.name.clone()),
                                binding_value: None,
                                surface_diagnostics: surface_diagnostics.clone(),
                                core_diagnostics: core_diagnostics.clone(),
                            });
                            failures.push(format!(
                                "line {}: {} -- {}",
                                line_num, line_substituted, msg
                            ));
                            if report_mode == RunReportMode::Text {
                                println!(
                                    "{} {} {}",
                                    "[FAIL]".red().bold(),
                                    format!("line {}", line_num).dimmed(),
                                    msg
                                );
                            }
                            continue;
                        }
                        let selected = actual_for_assert[binding.index].clone();
                        batch_bindings.insert(binding.name.clone(), selected.clone());
                        binding_events.push(BatchBindingEvent {
                            name: binding.name.clone(),
                            value: selected.clone(),
                            expanded_line: line_num,
                            source_file: expanded_line.source_file.clone(),
                            source_line: expanded_line.source_line,
                        });
                        if report_mode == RunReportMode::Text {
                            println!(
                                "{} ${} = {}",
                                "[BIND]".blue().bold(),
                                binding.name,
                                selected.cyan()
                            );
                        }
                    }
                    let bound_value = capture_binding
                        .as_ref()
                        .and_then(|b| batch_bindings.get(&b.name).cloned());

                    // Check for language-level assertion errors in surface results.
                    // C_AError atoms indicate assertEqual/assertEqualToResult failures.
                    let has_assertion_error = surface_results.as_ref().is_some_and(|results| {
                        results
                            .iter()
                            .any(|r| r.contains("C_AError(") || r.contains("AError("))
                    });

                    if has_assertion_error {
                        failed += 1;
                        let err_msg = format!(
                            "assertion error: {}",
                            surface_results
                                .as_ref()
                                .map(|r| r.join("; "))
                                .unwrap_or_default()
                        );
                        entries.push(RunMettaFileEntry {
                            line: line_num,
                            input: line_substituted.clone(),
                            status: "fail",
                            error: Some(err_msg.clone()),
                            surface_results,
                            expected_surface,
                            elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                            source_file: Some(expanded_line.source_file.clone()),
                            source_line: Some(expanded_line.source_line),
                            binding_name: capture_binding.as_ref().map(|b| b.name.clone()),
                            binding_value: None,
                            surface_diagnostics,
                            core_diagnostics,
                        });
                        failures.push(format!(
                            "line {}: {} -- {}",
                            line_num, line_substituted, err_msg
                        ));
                        if report_mode == RunReportMode::Text {
                            println!(
                                "{} {} {}",
                                "[FAIL]".red().bold(),
                                format!("line {}", line_num).dimmed(),
                                err_msg
                            );
                        }
                    } else {
                        passed += 1;
                        entries.push(RunMettaFileEntry {
                            line: line_num,
                            input: line_substituted.clone(),
                            status: "pass",
                            error: None,
                            surface_results,
                            expected_surface,
                            elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                            source_file: Some(expanded_line.source_file.clone()),
                            source_line: Some(expanded_line.source_line),
                            binding_name: capture_binding.as_ref().map(|b| b.name.clone()),
                            binding_value: bound_value,
                            surface_diagnostics,
                            core_diagnostics,
                        });
                        if report_mode == RunReportMode::Text {
                            println!(
                                "{} {}",
                                "[PASS]".green().bold(),
                                format!("line {}", line_num).dimmed()
                            );
                        }
                    }
                },
                Err(err) => {
                    self.suppress_output = prev_suppress;
                    failed += 1;
                    let err_msg = err.to_string();
                    let surface_diagnostics = self.latest_surface_eval_diagnostics();
                    entries.push(RunMettaFileEntry {
                        line: line_num,
                        input: line_substituted.clone(),
                        status: "fail",
                        error: Some(err_msg.clone()),
                        surface_results: self.last_surface_results.clone(),
                        expected_surface,
                        elapsed_ms: Some(started.elapsed().as_secs_f64() * 1000.0),
                        source_file: Some(expanded_line.source_file.clone()),
                        source_line: Some(expanded_line.source_line),
                        binding_name: capture_binding.as_ref().map(|b| b.name.clone()),
                        binding_value: None,
                        surface_diagnostics,
                        core_diagnostics: self.last_core_diagnostics.clone(),
                    });
                    if report_mode == RunReportMode::Text {
                        println!(
                            "{} {} {}",
                            "[FAIL]".red().bold(),
                            format!("line {}", line_num).dimmed(),
                            err_msg
                        );
                    }
                    failures.push(format!("line {}: {} -- {}", line_num, line_substituted, err));
                },
            }
        }

        self.execution_policy_override = prev_execution_policy_override;

        let lookup_relation_metadata = self
            .metta_surface_session
            .as_ref()
            .and_then(|session| session.lookup_relation_metadata());

        let report_payload = match report_mode {
            RunReportMode::Text => {
                println!();
                println!("{} {}", "run-metta-file summary:".bold(), file_path.cyan());
                println!("  {} {}", "passed:".green(), passed);
                println!("  {} {}", "failed:".red(), failed);
                println!("  {} {}", "skipped:".dimmed(), skipped);
                println!();
                None
            },
            RunReportMode::Json => Some(run_metta_file_report_json(
                file_path,
                passed,
                failed,
                skipped,
                &entries,
                &import_meta,
                &binding_events,
                RuntimeImportStats {
                    directives_executed: runtime_import_directives,
                    injected_lines: runtime_import_injected_lines,
                },
                surface_policy,
                dispatch_contracts,
                lookup_relation_metadata,
            )),
            RunReportMode::Jsonl => Some(run_metta_file_report_jsonl(
                file_path,
                passed,
                failed,
                skipped,
                &entries,
                &import_meta,
                &binding_events,
                RuntimeImportStats {
                    directives_executed: runtime_import_directives,
                    injected_lines: runtime_import_injected_lines,
                },
                surface_policy,
                dispatch_contracts,
                lookup_relation_metadata,
            )),
        };

        if let Some(payload) = report_payload {
            if let Some(path) = report_file {
                std::fs::write(&path, format!("{payload}\n")).map_err(|e| {
                    anyhow::anyhow!("failed to write report file '{}': {}", path, e)
                })?;
            } else {
                println!("{payload}");
            }
        }

        if failed > 0 {
            anyhow::bail!(
                "run-metta-file failed: {failed} line(s) failed\n{}",
                failures.join("\n")
            );
        }

        Ok(())
    }

    fn cmd_run_mm2_file(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: run-mm2-file <file> [--mork-max-steps <n>]");
        }

        #[cfg(not(feature = "mork-backend"))]
        {
            let _ = args;
            anyhow::bail!("run-mm2-file requires the 'mork-backend' feature flag");
        }

        #[cfg(feature = "mork-backend")]
        {
            use mettail_languages::mork_backend::mork_eval;

            let mut file_path: Option<&str> = None;
            let mut mork_max_steps: Option<usize> = None;
            let mut i = 0usize;
            while i < args.len() {
                let arg = args[i];
                if arg == "--mork-max-steps" {
                    i += 1;
                    if i >= args.len() {
                        anyhow::bail!("missing integer after --mork-max-steps");
                    }
                    mork_max_steps = Some(args[i].parse::<usize>().map_err(|_| {
                        anyhow::anyhow!("invalid --mork-max-steps value '{}'", args[i])
                    })?);
                    i += 1;
                    continue;
                }
                if let Some(raw) = arg.strip_prefix("--mork-max-steps=") {
                    if raw.is_empty() {
                        anyhow::bail!("empty value in --mork-max-steps option");
                    }
                    mork_max_steps = Some(raw.parse::<usize>().map_err(|_| {
                        anyhow::anyhow!("invalid --mork-max-steps value '{}'", raw)
                    })?);
                    i += 1;
                    continue;
                }
                if file_path.is_none() {
                    file_path = Some(arg);
                    i += 1;
                    continue;
                }
                anyhow::bail!(
                    "unexpected argument '{arg}', usage: run-mm2-file <file> [--mork-max-steps <n>]"
                );
            }

            let file_path = file_path.ok_or_else(|| anyhow::anyhow!("missing file path"))?;
            let program = std::fs::read(file_path)
                .map_err(|e| anyhow::anyhow!("failed to read MM2 file '{}': {}", file_path, e))?;

            let mut limits = mettail_runtime::MorkExecutionLimits::default();
            if let Some(max_steps) = mork_max_steps {
                limits.max_steps = max_steps;
            }

            let started = Instant::now();
            let run = mork_eval::run_mm2_program_with_limits(&program, limits)
                .map_err(|e| anyhow::anyhow!("MORK MM2 execution failed: {}", e))?;
            let elapsed_ms = started.elapsed().as_secs_f64() * 1000.0;

            if self.batch_quiet {
                println!("{}", run.dump);
                return Ok(());
            }

            println!();
            println!("{} {}", "Running MM2 file:".bold(), file_path.cyan());
            println!("{} {}", "Transitions:".bold(), run.steps.to_string().green());
            println!("{} {:.2}", "Elapsed ms:".bold(), elapsed_ms);
            println!();
            println!("{}", "Final atomspace dump:".bold());
            print!("{}", run.dump);
            if !run.dump.ends_with('\n') {
                println!();
            }
            Ok(())
        }
    }

    /// Helper to load environment from a file, returns count of loaded declarations
    fn load_env_from_file(&mut self, file_path: &str) -> Result<usize> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Read the file
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| anyhow::anyhow!("Failed to read file '{}': {}", file_path, e))?;

        let mut count = 0;
        let mut errors = Vec::new();
        // Track the most recent comment block to associate with the next definition
        let mut pending_comment: Option<String> = None;

        for (line_num, line) in content.lines().enumerate() {
            let line = line.trim();

            // Handle empty lines - they break comment association
            if line.is_empty() {
                continue;
            }

            // Handle comments - collect them for the next definition
            if line.starts_with("//") {
                let comment_text = line.trim_start_matches("//").trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }
            if line.starts_with('#') {
                let comment_text = line.trim_start_matches('#').trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }

            // Try to parse as assignment
            if let Some((name, term_str)) = Self::parse_assignment(line) {
                // Parse the term (using parse_term_for_env to share variable IDs)
                match language.parse_term_for_env(&term_str) {
                    Ok(term) => {
                        if let Some(env) = self.state.environment_mut() {
                            if let Err(e) = language.add_to_env(env, &name, term.as_ref()) {
                                errors.push(format!("Line {}: {}", line_num + 1, e));
                            } else {
                                // Store the comment if there was one
                                if let Some(comment) = pending_comment.take() {
                                    let _ = language.set_env_comment(env, &name, comment);
                                }
                                count += 1;
                            }
                        }
                    },
                    Err(e) => {
                        errors.push(format!(
                            "Line {}: Failed to parse '{}': {}",
                            line_num + 1,
                            name,
                            e
                        ));
                    },
                }
            } else {
                errors.push(format!("Line {}: Invalid assignment syntax", line_num + 1));
            }

            // Clear pending comment after processing a definition (whether successful or not)
            pending_comment = None;
        }

        // Report errors if any
        if !errors.is_empty() {
            println!();
            println!("{}", "Errors:".red());
            for error in errors {
                println!("  {}", error);
            }
        }

        Ok(count)
    }

    fn cmd_term(&mut self) -> Result<()> {
        println!("{}", "Current term:".bold());
        if let Some(term) = self.state.current_term() {
            let formatted = format_term_pretty(&format!("{}", term));
            println!("{}", formatted.cyan());
        } else {
            println!("{}", "(none)".dimmed());
        }
        println!();
        Ok(())
    }

    // === Type Inspection Commands ===

    fn cmd_type(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Term type:".bold());

        if let Some(term) = self.state.current_term() {
            let term_type = language.infer_term_type(term);
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("  {}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_typeof(&self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: typeof <variable-name>");
        }

        let var_name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            if let Some(var_type) = language.infer_var_type(term, var_name) {
                println!("{} : {}", var_name.cyan(), format!("{}", var_type).green());
            } else {
                println!(
                    "{}",
                    format!("Variable '{}' not found in current term", var_name).yellow()
                );
            }
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_types(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            // Get term type
            let term_type = language.infer_term_type(term);

            // Get all variable types
            let var_types = language.infer_var_types(term);

            if var_types.is_empty() {
                println!("{}", "Free variables:".bold());
                println!("  {}", "(none - all variables are bound)".dimmed());
            } else {
                println!("{}", "Free variables:".bold());
                for var_info in &var_types {
                    println!("  {} : {}", var_info.name.cyan(), format!("{}", var_info.ty).green());
                }
            }

            println!();
            println!("{}", "Term type:".bold());
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_exec_term(&mut self, term_str: &str) -> Result<()> {
        self.exec_or_step_term(term_str.trim(), /* step_mode: */ false)
    }

    /// Step-by-step execution: run Ascent but leave current term at the initial term
    /// so the user can type `apply 0` to apply one rewrite at a time.
    /// Step mode never uses direct eval so the user always sees the initial term and can apply rewrites.
    fn cmd_step_term(&mut self, term_str: &str) -> Result<()> {
        self.exec_or_step_term(term_str.trim(), /* step_mode: */ true)
    }

    /// Shared parse + substitute + (optionally) direct-eval + Ascent. When step_mode is true,
    /// we never use try_direct_eval so the initial term is always shown and rewrites can be applied.
    fn exec_or_step_term(&mut self, term_str: &str, step_mode: bool) -> Result<()> {
        self.last_surface_results = None;
        self.last_core_diagnostics = None;
        if self.supports_surface_metta_runner() && looks_like_surface_metta(term_str) {
            let parsed = {
                let session = self.ensure_metta_surface_session();
                session.parse_line_for_session(term_str)?
            };
            if let Some(stmt) = parsed {
                return self.exec_surface_stmt(stmt, step_mode);
            }
            return Ok(());
        }

        self.exec_or_step_core_term(term_str, step_mode, self.execution_policy_override.backend)
    }

    fn exec_surface_stmt(&mut self, stmt: SurfaceStmt, step_mode: bool) -> Result<()> {
        let policy = self.execution_policy_override;
        let effective_surface_policy =
            policy.effective_surface_policy(self.current_runtime_optimization_hints());
        let surface_fuel_override = policy.surface_fuel;
        let surface_first_branch_only = effective_surface_policy.first_branch_only;
        let exact_priority_override = Some(effective_surface_policy.exact_priority);
        let recursive_memo_override = Some(effective_surface_policy.recursive_memo);
        let core_backend_override = match policy.backend {
            Some(RuntimeBackend::Mork) => Some(RuntimeBackend::Mork),
            Some(RuntimeBackend::Ascent) => Some(RuntimeBackend::Ascent),
            Some(RuntimeBackend::Auto) => Some(RuntimeBackend::Auto),
            None => None,
        };
        let prev_limits = {
            let session = self.ensure_metta_surface_session();
            let prev = session.rewrite_limits();
            let mut next = prev;
            let mut changed = false;
            if let Some(surface_fuel) = surface_fuel_override {
                let bounded = surface_fuel.max(1);
                next.max_steps = bounded;
                next.max_outcomes = next.max_outcomes.min(bounded);
                next.max_branches = next.max_branches.min(bounded.saturating_mul(4));
                changed = true;
            }
            if surface_first_branch_only {
                next.max_branches = 1;
                next.max_outcomes = 1;
                changed = true;
            }
            if changed {
                session.set_rewrite_limits(next);
                Some(prev)
            } else {
                None
            }
        };

        let mork_rule_copies_override = policy.mork_rule_copies;
        let mork_max_steps_override = policy.mork_max_steps;
        let prev_mork_limits = {
            let session = self.ensure_metta_surface_session();
            let prev = session.mork_limits();
            let mut next = prev;
            let mut changed = false;
            if let Some(rule_copies) = mork_rule_copies_override {
                next.rule_copies = rule_copies.max(1);
                changed = true;
            }
            if let Some(max_steps) = mork_max_steps_override {
                next.max_steps = max_steps.max(1);
                changed = true;
            }
            if changed {
                session.set_mork_limits(next);
                Some(prev)
            } else {
                None
            }
        };
        let prev_exact_pref = {
            let session = self.ensure_metta_surface_session();
            let prev = session.prefer_exact_rules();
            if let Some(enabled) = exact_priority_override {
                session.set_prefer_exact_rules(enabled);
                Some(prev)
            } else {
                None
            }
        };
        let prev_recursive_memo = {
            let session = self.ensure_metta_surface_session();
            let prev = session.recursive_memo_enabled();
            if let Some(enabled) = recursive_memo_override {
                session.set_recursive_memo_enabled(enabled);
                Some(prev)
            } else {
                None
            }
        };
        let outcome_result = self.ensure_metta_surface_session().apply_stmt(stmt);
        if let Some(prev) = prev_limits {
            self.ensure_metta_surface_session().set_rewrite_limits(prev);
        }
        if let Some(prev) = prev_mork_limits {
            self.ensure_metta_surface_session().set_mork_limits(prev);
        }
        if let Some(prev) = prev_exact_pref {
            self.ensure_metta_surface_session()
                .set_prefer_exact_rules(prev);
        }
        if let Some(prev) = prev_recursive_memo {
            self.ensure_metta_surface_session()
                .set_recursive_memo_enabled(prev);
        }
        let outcome = outcome_result?;
        match outcome {
            SurfaceOutcome::Mutation { message } => {
                self.last_core_diagnostics = None;
                if !self.suppress_output {
                    println!();
                    println!("{} {}", "✓".green(), message);
                    println!();
                }
                Ok(())
            },
            SurfaceOutcome::EvalMany { core_terms } => {
                if core_terms.is_empty() {
                    anyhow::bail!("surface evaluation produced no runnable branches");
                }
                if step_mode {
                    if !self.suppress_output {
                        println!();
                        println!(
                            "{} {}",
                            "Surface step produced".bold(),
                            format!("{} branch(es):", core_terms.len()).cyan()
                        );
                        for (idx, core_term) in core_terms.iter().enumerate() {
                            println!("  [{}] {}", idx + 1, core_term.dimmed());
                        }
                        if core_terms.len() > 1 {
                            println!(
                                "{} {}",
                                "Step mode note:".yellow().bold(),
                                "selecting branch [1] for interactive stepping".yellow()
                            );
                        }
                    }
                    self.exec_or_step_core_term(
                        &core_terms[0],
                        /* step_mode */ true,
                        core_backend_override,
                    )?;
                    return Ok(());
                }
                if surface_first_branch_only {
                    if !self.suppress_output {
                        println!();
                        println!(
                            "{} {}",
                            "Surface eval mode:".bold(),
                            "using first lowered branch only".yellow()
                        );
                    }
                    self.exec_or_step_core_term(
                        &core_terms[0],
                        /* step_mode */ false,
                        core_backend_override,
                    )?;
                    return Ok(());
                }
                let mut merged_surface = Vec::new();
                let mut seen_surface = HashSet::new();
                let mut merged_diagnostics = Vec::new();
                for (idx, core_term) in core_terms.iter().enumerate() {
                    if !self.suppress_output {
                        println!();
                        println!(
                            "{} {}/{}",
                            "Lowered MeTTa surface to core state:".bold(),
                            idx + 1,
                            core_terms.len()
                        );
                        println!("  {}", core_term.dimmed());
                    }
                    self.exec_or_step_core_term(
                        core_term,
                        /* step_mode */ false,
                        core_backend_override,
                    )?;
                    if let Some(diag) = self.last_core_diagnostics.clone() {
                        merged_diagnostics.push(diag);
                    }
                    if let Some(items) = self.last_surface_results.clone() {
                        for item in items {
                            if seen_surface.insert(item.clone()) {
                                merged_surface.push(item);
                            }
                        }
                    }
                }
                if !merged_surface.is_empty() {
                    merged_surface.sort();
                    self.last_surface_results = Some(merged_surface);
                }
                self.last_core_diagnostics = aggregate_core_eval_diagnostics(&merged_diagnostics);
                Ok(())
            },
        }
    }

    fn exec_or_step_core_term(
        &mut self,
        term_str: &str,
        step_mode: bool,
        backend_override: Option<RuntimeBackend>,
    ) -> Result<()> {
        self.last_surface_results = None;
        self.last_core_diagnostics = None;
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        if !self.suppress_output {
            println!();
            print!("Parsing... ");
        }

        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        if !self.suppress_output {
            println!("{}", "✓".green());
        }

        let term = if let Some(env) = self.state.environment() {
            if !language.is_env_empty(env) {
                if !self.suppress_output {
                    print!("Substituting environment... ");
                }
                let substituted = if step_mode {
                    language
                        .substitute_env_preserve_structure(term.as_ref(), env)
                        .map_err(|e| anyhow::anyhow!("{}", e))?
                } else {
                    language
                        .substitute_env(term.as_ref(), env)
                        .map_err(|e| anyhow::anyhow!("{}", e))?
                };
                if !self.suppress_output {
                    println!("{}", "✓".green());
                }
                substituted
            } else {
                term
            }
        } else {
            term
        };

        // Normalize (beta-reduce Apply/MApply of Lam/MLam) before evaluation
        let term = language.normalize_term(term.as_ref());

        // Direct eval only for exec: step must always run Ascent and show the initial term
        if !step_mode {
            if let Some(result_term) = language.try_direct_eval(term.as_ref()) {
                if self.supports_surface_metta_runner() {
                    if let Some(session) = self.metta_surface_session.as_ref() {
                        let rendered = format!("{}", result_term);
                        if let Some(out_atom) = extract_state_out_atom(&rendered) {
                            let decoded = session.decode_atom_to_surface(&out_atom);
                            self.last_surface_results = Some(vec![decoded.clone()]);
                            if !self.suppress_output {
                                println!();
                                println!("{} {}", "Surface result:".bold(), decoded.green());
                                println!();
                            }
                        }
                    }
                }
                let result_id = result_term.term_id();
                let results = AscentResults::from_single_term(result_term.as_ref());
                self.last_core_diagnostics =
                    Some(build_core_eval_diagnostics(&results, result_id, 0.0, "direct_eval"));
                if !self.suppress_output {
                    println!();
                    println!("{}", "Current term (result):".bold());
                    let formatted = format_term_pretty(&format!("{}", result_term));
                    println!("{}", formatted.cyan());
                    println!();
                }
                self.state
                    .set_term_with_id(result_term, results, result_id)?;
                return Ok(());
            }
        }

        let requested_backend = backend_override.unwrap_or(RuntimeBackend::Auto);
        // Development default: prefer native MORK for HE whenever backend is Auto.
        // Non-HE languages (and HE builds without mork-backend feature) remain unchanged.
        let backend = if matches!(requested_backend, RuntimeBackend::Auto)
            && language.name() == "MeTTaHE"
            && language.supports_backend(RuntimeBackend::Mork)
        {
            RuntimeBackend::Mork
        } else {
            requested_backend
        };
        if !language.supports_backend(backend) {
            anyhow::bail!(
                "backend '{}' is not supported for language '{}'",
                match backend {
                    RuntimeBackend::Auto => "auto",
                    RuntimeBackend::Ascent => "ascent",
                    RuntimeBackend::Mork => "mork",
                },
                language.name()
            );
        }
        self.ensure_core_backend_contract_for_active_language(backend)?;
        if !self.suppress_output {
            print!(
                "Running {}... ",
                match backend {
                    RuntimeBackend::Auto => "core backend",
                    RuntimeBackend::Ascent => "Ascent",
                    RuntimeBackend::Mork => "MORK",
                }
            );
        }
        let start_time = Instant::now();
        let results = language
            .run_backend(term.as_ref(), backend)
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        let end_time = Instant::now();
        let elapsed_ms = end_time.duration_since(start_time).as_secs_f64() * 1000.0;
        let mode = match backend {
            RuntimeBackend::Auto => "auto",
            RuntimeBackend::Ascent => "ascent",
            RuntimeBackend::Mork => "mork",
        };
        self.last_core_diagnostics =
            Some(build_core_eval_diagnostics(&results, term.term_id(), elapsed_ms, mode));
        if !self.suppress_output {
            println!("Time taken: {:?}", end_time.duration_since(start_time));
            println!("{}", "Done!".green());
            println!();
            println!("Computed:");
            println!("  - {} terms", results.all_terms.len());
            println!("  - {} rewrites", results.rewrites.len());
            println!("  - {} normal forms", results.normal_forms().len());
            println!();
        }

        let initial_id = term.term_id();

        if step_mode {
            // Step: always show initial term so user can apply rewrites one by one
            let available = results.rewrites_from(initial_id).len();
            if !self.suppress_output {
                println!("{}", "Current term (initial):".bold());
                let formatted = format_term_pretty(&format!("{}", term));
                println!("{}", formatted.cyan());
                println!();
            }
            self.state.set_term_with_id(term, results, initial_id)?;
            if !self.suppress_output {
                if available > 0 {
                    println!(
                        "  Use {} to apply a rewrite ({} available).",
                        "apply 0".cyan(),
                        available
                    );
                } else {
                    println!("  No rewrites from this term (already a normal form).");
                }
            }
        } else {
            // Exec: show a normal form reachable from the initial term.
            // For MeTTa surface sessions, also show all reachable decoded outputs.
            let reachable_nfs = Self::reachable_normal_forms(&results, initial_id);
            if self.supports_surface_metta_runner() {
                let decoded = self.decode_metta_surface_reachable_results(&results, initial_id);
                if !decoded.is_empty() {
                    self.print_metta_surface_results(&decoded);
                    self.last_surface_results = Some(decoded);
                }
            }
            if let Some(nf) = reachable_nfs.first().copied() {
                let result_term = language
                    .parse_term(&nf.display)
                    .map_err(|e| anyhow::anyhow!("{}", e))?;
                if !self.suppress_output {
                    println!("{}", "Current term (result):".bold());
                    let formatted = format_term_pretty(&nf.display);
                    println!("{}", formatted.cyan());
                    println!();
                }
                self.state
                    .set_term_with_id(result_term, results.clone(), nf.term_id)?;
                return Ok(());
            }
            if !self.suppress_output {
                println!("{}", "Current term:".bold());
                let formatted = format_term_pretty(&format!("{}", term));
                println!("{}", formatted.cyan());
                println!();
            }
            self.state.set_term(term, results)?;
        }
        if !self.suppress_output {
            println!();
        }
        Ok(())
    }

    fn get_results(&self) -> Result<&AscentResults> {
        self.state
            .ascent_results()
            .ok_or_else(|| anyhow::anyhow!("No term loaded. Use 'term: <expr>' first."))
    }

    fn cmd_equations(&self) -> Result<()> {
        let results = self.get_results()?;

        let equivalences = results.equivalences.clone();
        println!();
        println!("{}", "Equivalence Classes:".bold());
        for equ_class in equivalences {
            let terms = equ_class
                .term_ids
                .iter()
                .map(|id| {
                    results
                        .all_terms
                        .iter()
                        .find(|t| t.term_id == *id)
                        .unwrap()
                        .display
                        .as_str()
                })
                .collect::<Vec<_>>();
            println!("  {}", terms.join(" == "));
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites_all(&self) -> Result<()> {
        let results = self.get_results()?;

        let rewrites = results.rewrites.clone();
        println!();
        println!("{}", "Rewrites:".bold());
        for rewrite in rewrites {
            let from_info = self.term_by_id(rewrite.from_id)?;
            let to_info = self.term_by_id(rewrite.to_id)?;
            println!("  {} → {}", from_info.display, to_info.display);
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites(&self) -> Result<()> {
        let results = self.get_results()?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        // Find rewrites from the current term
        let available_rewrites: Vec<_> = results
            .rewrites
            .iter()
            .filter(|r| r.from_id == current_id)
            .collect();

        println!();
        if available_rewrites.is_empty() {
            println!(
                "{} No rewrites available from current term (it's a normal form).",
                "✓".green()
            );
        } else {
            println!("{} available from current term:", "Rewrites".bold());
            println!();
            for (idx, rewrite) in available_rewrites.iter().enumerate() {
                // Find the target term display
                let target_info = self.term_by_id(rewrite.to_id)?;
                let target_display = target_info.display.as_str();

                // Pretty print the target
                let formatted = format_term_pretty(target_display);

                println!("  {}) {}", idx.to_string().cyan(), "→".yellow());
                // Indent each line of the formatted output
                for line in formatted.lines() {
                    println!("     {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn term_by_id(&self, id: u64) -> Result<&TermInfo> {
        let results = self.get_results()?;
        results
            .all_terms
            .iter()
            .find(|t| t.term_id == id)
            .ok_or_else(|| anyhow::anyhow!("Term not found"))
    }

    fn cmd_normal_forms(&self) -> Result<()> {
        let results = self.get_results()?;

        let normal_forms = results.normal_forms();

        println!();
        if normal_forms.is_empty() {
            println!("{} No normal forms computed.", "Warning:".yellow());
        } else {
            println!("{} ({} total):", "Normal forms".bold(), normal_forms.len());
            println!();
            for (idx, nf) in normal_forms.iter().enumerate() {
                let formatted = format_term_pretty(&nf.display);
                println!("  {})", idx.to_string().cyan());
                for line in formatted.lines() {
                    println!("    {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn cmd_relations(&self) -> Result<()> {
        let results = self.get_results()?;

        println!();
        println!("{}", "Computed Relations:".bold());
        println!();

        // Built-in relations
        println!("{}", "  Built-in:".yellow());
        println!("    {} ({} tuples)", "terms".cyan(), results.all_terms.len());
        println!("    {} ({} tuples)", "rewrites".cyan(), results.rewrites.len());
        println!("    {} ({} classes)", "equivalences".cyan(), results.equivalences.len());

        // Custom relations
        if !results.custom_relations.is_empty() {
            println!();
            println!("{}", "  Custom:".yellow());
            for (name, data) in &results.custom_relations {
                let signature = format!("{}({})", name, data.param_types.join(", "));
                println!("    {} ({} tuples)", signature.cyan(), data.tuples.len());
            }
        }

        println!();
        println!("Use {} to view tuples in a specific relation.", "'relation <name>'".green());
        println!();
        Ok(())
    }

    fn cmd_relation(&self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: relation <name>\nUse 'relations' to list available relations.");
        }

        let name = args[0];
        let results = self.get_results()?;

        // Check built-in relations first
        match name {
            "terms" => {
                println!();
                println!("{} ({} tuples):", "terms(Term)".bold(), results.all_terms.len());
                for term_info in &results.all_terms {
                    let nf_marker = if term_info.is_normal_form {
                        " [NF]".dimmed()
                    } else {
                        "".into()
                    };
                    println!("  {}{}", term_info.display.green(), nf_marker);
                }
                println!();
                return Ok(());
            },
            "rewrites" => {
                println!();
                println!("{} ({} tuples):", "rewrites(Term, Term)".bold(), results.rewrites.len());
                for rw in &results.rewrites {
                    let from = results.all_terms.iter().find(|t| t.term_id == rw.from_id);
                    let to = results.all_terms.iter().find(|t| t.term_id == rw.to_id);
                    if let (Some(from), Some(to)) = (from, to) {
                        println!(
                            "  {} {} {}",
                            from.display.green(),
                            "→".yellow(),
                            to.display.green()
                        );
                    }
                }
                println!();
                return Ok(());
            },
            "equivalences" => {
                println!();
                println!("{} ({} classes):", "equivalences".bold(), results.equivalences.len());
                for equiv in &results.equivalences {
                    let terms: Vec<_> = equiv
                        .term_ids
                        .iter()
                        .filter_map(|id| results.all_terms.iter().find(|t| t.term_id == *id))
                        .map(|t| t.display.as_str())
                        .collect();
                    println!("  {}", terms.join(" == ").green());
                }
                println!();
                return Ok(());
            },
            _ => {},
        }

        // Check custom relations
        if let Some(data) = results.custom_relations.get(name) {
            println!();
            let signature = format!("{}({})", name, data.param_types.join(", "));
            println!("{} ({} tuples):", signature.bold(), data.tuples.len());
            for tuple in &data.tuples {
                println!("  ({})", tuple.join(", ").green());
            }
            println!();
            Ok(())
        } else {
            Err(anyhow::anyhow!(
                "Unknown relation: '{}'. Use 'relations' to list available relations.",
                name
            ))
        }
    }

    fn cmd_apply(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: apply <rewrite-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let results = self.get_results()?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        // Find available rewrites
        let available_rewrites: Vec<_> = results
            .rewrites
            .iter()
            .filter(|r| r.from_id == current_id)
            .collect();

        if idx >= available_rewrites.len() {
            anyhow::bail!("Rewrite {} not found. Use 'rewrites' to see available rewrites.", idx);
        }

        let rewrite = available_rewrites[idx];

        // Find the target term
        let target_info = results
            .all_terms
            .iter()
            .find(|t| t.term_id == rewrite.to_id)
            .ok_or_else(|| anyhow::anyhow!("Target term not found"))?;

        // Parse the target term and update its ID to match what's in the graph
        let target_term = language
            .parse_term(&target_info.display)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!();
        println!("{}", "Applied rewrite →".yellow());
        let formatted = format_term_pretty(&target_info.display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state - pass the target_id so we can track position in the graph
        self.state
            .set_term_with_id(target_term, results.clone(), rewrite.to_id)?;

        Ok(())
    }

    fn cmd_goto(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: goto <normal-form-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let results = self.get_results()?;

        let normal_forms = results.normal_forms();

        if idx >= normal_forms.len() {
            anyhow::bail!(
                "Normal form {} not found. Use 'normal-forms' to see available normal forms.",
                idx
            );
        }

        let target_info = &normal_forms[idx];

        // Parse the target term
        let target_term = language
            .parse_term(&target_info.display)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!();
        println!("{}", "Navigated to normal form:".bold());
        let formatted = format_term_pretty(&target_info.display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state with the correct graph ID
        self.state
            .set_term_with_id(target_term, results.clone(), target_info.term_id)?;

        Ok(())
    }

    fn cmd_oracles(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <name>' first."))?;
        let language = self.registry.get(language_name)?;
        let oracles = language.list_oracles();

        println!();
        if oracles.is_empty() {
            println!(
                "{} {} exposes no oracle endpoints.",
                "Info:".yellow(),
                language.name().cyan()
            );
            println!();
            return Ok(());
        }

        println!("{} {}", "Oracle endpoints for".bold(), language.name().cyan());
        println!();
        for oracle in &oracles {
            println!("  {}", oracle.name.green());
            if oracle.operations.is_empty() {
                println!("    {}", "(no operations declared)".dimmed());
            } else {
                println!("    {} {}", "operations:".dimmed(), oracle.operations.join(", "));
            }
            if let Some(docs) = &oracle.docs {
                println!("    {} {}", "docs:".dimmed(), docs);
            }
        }
        println!();
        Ok(())
    }

    fn cmd_oracle_query(&self, args: &[&str]) -> Result<()> {
        if args.len() < 2 {
            anyhow::bail!("Usage: oracle-query <oracle> <operation> [args...]");
        }

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <name>' first."))?;
        let language = self.registry.get(language_name)?;

        let query = OracleQuery::new(
            args[0],
            args[1],
            args[2..].iter().map(|s| (*s).to_string()).collect(),
        );
        let response = language
            .query_oracle(&query)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!();
        println!(
            "{} {}.{}",
            "Oracle response:".bold(),
            query.oracle.cyan(),
            query.operation.cyan()
        );
        if response.rows.is_empty() {
            println!("  {}", "(no rows)".dimmed());
        } else {
            for row in &response.rows {
                let rendered = if row.is_empty() {
                    "()".to_string()
                } else if row.len() == 1 {
                    row[0].clone()
                } else {
                    format!("({})", row.join(", "))
                };
                println!("  {}", rendered.green());
            }
        }
        if !response.diagnostics.is_empty() {
            println!();
            println!("{}", "Diagnostics:".yellow());
            for line in &response.diagnostics {
                println!("  {}", line);
            }
        }
        println!();
        Ok(())
    }

    /// Run a single Datalog-style rule over the current Ascent results.
    /// Requires a loaded language, a prior step (so ascent_results exists), and a current term for env substitution.
    /// Environment substitution includes REPL bindings plus "current_term" (display of the current stepped term).
    fn cmd_query(&mut self, line: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <name>' first."))?;

        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'step <term>' first."))?
            .clone_box();

        let language = self.registry.get(language_name)?;

        self.state.ensure_environment(|| language.create_env());

        // Substitute env bindings (save t, etc.). We do *not* add "current_term" to env here.
        let mut substituted = pre_substitute_env(line, language, self.state.environment().unwrap());

        // Substitute "current_term" with a Rust string literal so the Ascent (syn) parser sees one argument.
        // The term's display can contain { } | . etc. which are valid Rust tokens; only a string literal is safe.
        let current_display = format!("{}", current_term);
        let current_literal = format!(
            "\"{}\"",
            current_display
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r")
                .replace('\t', "\\t")
        );
        substituted = replace_whole_word(&substituted, "current_term", &current_literal);

        let results = self
            .state
            .ascent_results()
            .ok_or_else(|| anyhow::anyhow!("No step results. Use 'step <term>' first."))?;

        match query_run_query(&substituted, results) {
            Ok(rows) => {
                println!();
                if rows.is_empty() {
                    println!("{} (0 rows)", "Query result:".bold());
                } else {
                    println!("{} ({} row(s)):", "Query result:".bold(), rows.len());
                    for row in &rows {
                        let formatted = if row.len() == 1 {
                            row[0].clone()
                        } else {
                            format!("({})", row.join(", "))
                        };
                        println!("  {}", formatted.green());
                    }
                }
                println!();
                Ok(())
            },
            Err(e) => {
                eprintln!("{}", "Query (after substitution):".yellow().bold());
                eprintln!("{}", substituted.dimmed());
                Err(anyhow::anyhow!("{}", e))
            },
        }
    }

    fn cmd_example(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: example <name>\nUse 'list-examples' to see available examples.");
        }

        let example_name = args[0];

        let example = Example::by_name(example_name).ok_or_else(|| {
            anyhow::anyhow!(
                "Example '{}' not found. Use 'list-examples' to see available examples.",
                example_name
            )
        })?;

        println!();
        println!("{} {}", "Example:".bold(), example.name.cyan());
        println!("{} {}", "Description:".bold(), example.description);
        println!();

        // Parse and load the example (multi-line examples run line-by-line).
        for line in example.source.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with(';') || line.starts_with("//") {
                continue;
            }
            self.cmd_exec_term(line)?;
        }

        Ok(())
    }

    fn cmd_list_examples(&self, language_name: &str) -> Result<()> {
        println!();
        println!("{}", "Available Examples:".bold());
        println!();

        // Group by category
        for &category in &[
            ExampleCategory::Simple,
            ExampleCategory::Branching,
            ExampleCategory::Complex,
            ExampleCategory::Parallel,
            ExampleCategory::Advanced,
            ExampleCategory::Performance,
            ExampleCategory::EdgeCase,
            ExampleCategory::MultiComm,
            ExampleCategory::Mobility,
            ExampleCategory::Security,
        ] {
            let examples = Example::by_language_name_and_category(language_name, category);
            if !examples.is_empty() {
                println!("{}", format!("  {:?}:", category).yellow());
                for ex in examples {
                    println!("    {} - {}", ex.name.cyan(), ex.description.dimmed());
                }
                println!();
            }
        }

        println!("Use {} to load an example.", "example <name>".green());
        println!();

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Repl;
    use crate::registry::{build_registry, LanguageRegistry};
    use mettail_languages::mettafull_legacy::MeTTaFullStateLanguage;
    use mettail_runtime::{
        AscentResults, EquationDef, Language, LanguageMetadata, LogicRelationDef, LogicRuleDef,
        OracleDescriptor, OracleQuery, OracleResponse, RewriteDef, RuntimeOptimizationContracts,
        RuntimeOptimizationHints, SurfacePolicyHint, Term, TermDef, TermType, TypeDef, VarTypeInfo,
    };
    use std::any::Any;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_artifact_path(stem: &str, ext: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock should be after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        let mut path = PathBuf::from(".artifacts/test-runtime");
        path.push(format!("{stem}_{pid}_{nanos}.{ext}"));
        path
    }

    fn build_registry_with_legacy_mettafull() -> LanguageRegistry {
        let mut registry = build_registry().expect("registry should initialize");
        registry.register(Box::new(MeTTaFullStateLanguage));
        registry
    }

    #[test]
    fn run_metta_file_jsonl_uses_theory_deterministic_surface_policy_by_default() {
        let registry = build_registry_with_legacy_mettafull();
        let mut repl = Repl::new(registry).expect("repl should initialize");
        repl.set_batch_quiet(true);
        repl.load_language("mettafullstate")
            .expect("mettafullstate should load");

        let input_path = unique_artifact_path("theory_deterministic_input", "metta");
        let report_path = unique_artifact_path("theory_deterministic_report", "jsonl");
        fs::create_dir_all(
            input_path
                .parent()
                .expect("artifact path should have a parent directory"),
        )
        .expect("artifact directory should be creatable");
        fs::write(&input_path, "!(+ 1 1)\n").expect("input file should be writable");

        let cmd = format!(
            "run-metta-file {} --report=jsonl --report-file {}",
            input_path.display(),
            report_path.display()
        );
        repl.run_command(&cmd)
            .expect("run-metta-file command should succeed");

        let report = fs::read_to_string(&report_path).expect("report file should be readable");
        let summary = report.lines().next().expect("jsonl should contain summary");
        assert!(
            summary.contains("\"surface_policy\":\"theory-deterministic\""),
            "expected theory-deterministic summary, got: {summary}"
        );
        assert!(
            summary.contains("\"dispatch_contracts\":{\"deterministic_reduction\":true,\"memoization_safe\":true,\"specialization_safe\":true,\"core_ground_eval_safe\":true}"),
            "expected dispatch contracts in summary, got: {summary}"
        );

        let _ = fs::remove_file(&input_path);
        let _ = fs::remove_file(&report_path);
    }

    #[test]
    fn run_metta_file_json_report_has_no_core_tokens_in_surface_results_for_pln_demo() {
        let registry = build_registry_with_legacy_mettafull();
        let mut repl = Repl::new(registry).expect("repl should initialize");
        repl.set_batch_quiet(true);
        repl.load_language("mettafullstate")
            .expect("mettafullstate should load");

        let report_path = unique_artifact_path("pln_deduction_demo_report", "json");
        fs::create_dir_all(
            report_path
                .parent()
                .expect("artifact path should have a parent directory"),
        )
        .expect("artifact directory should be creatable");

        let rel = PathBuf::from("repl/src/examples/petta_adapted/pln_deduction_demo.metta");
        let local = PathBuf::from("src/examples/petta_adapted/pln_deduction_demo.metta");
        let input_path = if rel.exists() { rel } else { local };
        assert!(input_path.exists(), "fixture should exist: {}", input_path.display());
        let cmd = format!(
            "run-metta-file {} --report=json --report-file {}",
            input_path.display(),
            report_path.display()
        );
        repl.run_command(&cmd)
            .expect("run-metta-file command should succeed");

        let report = fs::read_to_string(&report_path).expect("report file should be readable");
        assert!(
            report.contains("\"failed\":0"),
            "expected zero failures in report, got: {report}"
        );

        // Focused leak regression: this case previously surfaced `C_div` in user output.
        assert!(
            !report.contains("C_div"),
            "surface results should not leak C_div core token: {report}"
        );
        assert!(
            !report.contains("C_add"),
            "surface results should not leak C_add core token: {report}"
        );

        let _ = fs::remove_file(&report_path);
    }

    #[test]
    fn run_metta_file_mettahe_accepts_prose_and_spaced_bang_forms() {
        let registry = build_registry().expect("registry should initialize");
        let mut repl = Repl::new(registry).expect("repl should initialize");
        repl.set_batch_quiet(true);
        repl.load_language("mettahe").expect("mettahe should load");

        let input_path = unique_artifact_path("mettahe_compat_input", "metta");
        let report_path = unique_artifact_path("mettahe_compat_report", "json");
        fs::create_dir_all(
            input_path
                .parent()
                .expect("artifact path should have a parent directory"),
        )
        .expect("artifact directory should be creatable");
        fs::write(
            &input_path,
            ";;;;;;;;;;;;;;;;;;;;;;;;\nAuto type-checking can be enabled\n(= (id $x) $x)\n! (id 5)\n!\n",
        )
        .expect("input file should be writable");

        let cmd = format!(
            "run-metta-file {} --report=json --report-file {}",
            input_path.display(),
            report_path.display()
        );
        repl.run_command(&cmd)
            .expect("run-metta-file command should succeed");

        let report = fs::read_to_string(&report_path).expect("report file should be readable");
        assert!(
            report.contains("\"failed\":0"),
            "expected zero failures in report, got: {report}"
        );

        let _ = fs::remove_file(&input_path);
        let _ = fs::remove_file(&report_path);
    }

    struct MissingContractsMetadata;

    static MISSING_CONTRACTS_METADATA: MissingContractsMetadata = MissingContractsMetadata;

    fn base_metadata() -> &'static dyn LanguageMetadata {
        let inner = MeTTaFullStateLanguage;
        inner.metadata()
    }

    impl LanguageMetadata for MissingContractsMetadata {
        fn name(&self) -> &'static str {
            base_metadata().name()
        }

        fn types(&self) -> &'static [TypeDef] {
            base_metadata().types()
        }

        fn terms(&self) -> &'static [TermDef] {
            base_metadata().terms()
        }

        fn equations(&self) -> &'static [EquationDef] {
            base_metadata().equations()
        }

        fn rewrites(&self) -> &'static [RewriteDef] {
            base_metadata().rewrites()
        }

        fn logic_relations(&self) -> &'static [LogicRelationDef] {
            base_metadata().logic_relations()
        }

        fn logic_rules(&self) -> &'static [LogicRuleDef] {
            base_metadata().logic_rules()
        }

        fn runtime_optimization_hints(&self) -> RuntimeOptimizationHints {
            RuntimeOptimizationHints {
                surface_policy: SurfacePolicyHint::Default,
                enable_core_ground_eval: true,
                optimization_contracts: RuntimeOptimizationContracts::default(),
            }
        }
    }

    struct MissingContractsLanguage;

    impl Language for MissingContractsLanguage {
        fn name(&self) -> &'static str {
            let inner = MeTTaFullStateLanguage;
            inner.name()
        }

        fn metadata(&self) -> &'static dyn LanguageMetadata {
            &MISSING_CONTRACTS_METADATA
        }

        fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
            let inner = MeTTaFullStateLanguage;
            inner.parse_term(input)
        }

        fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
            let inner = MeTTaFullStateLanguage;
            inner.parse_term_for_env(input)
        }

        fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> {
            let inner = MeTTaFullStateLanguage;
            inner.run_ascent(term)
        }

        fn list_oracles(&self) -> Vec<OracleDescriptor> {
            let inner = MeTTaFullStateLanguage;
            inner.list_oracles()
        }

        fn query_oracle(&self, query: &OracleQuery) -> Result<OracleResponse, String> {
            let inner = MeTTaFullStateLanguage;
            inner.query_oracle(query)
        }

        fn try_direct_eval(&self, term: &dyn Term) -> Option<Box<dyn Term>> {
            let inner = MeTTaFullStateLanguage;
            inner.try_direct_eval(term)
        }

        fn normalize_term(&self, term: &dyn Term) -> Box<dyn Term> {
            let inner = MeTTaFullStateLanguage;
            inner.normalize_term(term)
        }

        fn format_term(&self, term: &dyn Term) -> String {
            let inner = MeTTaFullStateLanguage;
            inner.format_term(term)
        }

        fn create_env(&self) -> Box<dyn Any + Send + Sync> {
            let inner = MeTTaFullStateLanguage;
            inner.create_env()
        }

        fn add_to_env(&self, env: &mut dyn Any, name: &str, term: &dyn Term) -> Result<(), String> {
            let inner = MeTTaFullStateLanguage;
            inner.add_to_env(env, name, term)
        }

        fn remove_from_env(&self, env: &mut dyn Any, name: &str) -> Result<bool, String> {
            let inner = MeTTaFullStateLanguage;
            inner.remove_from_env(env, name)
        }

        fn clear_env(&self, env: &mut dyn Any) {
            let inner = MeTTaFullStateLanguage;
            inner.clear_env(env);
        }

        fn substitute_env(&self, term: &dyn Term, env: &dyn Any) -> Result<Box<dyn Term>, String> {
            let inner = MeTTaFullStateLanguage;
            inner.substitute_env(term, env)
        }

        fn substitute_env_preserve_structure(
            &self,
            term: &dyn Term,
            env: &dyn Any,
        ) -> Result<Box<dyn Term>, String> {
            let inner = MeTTaFullStateLanguage;
            inner.substitute_env_preserve_structure(term, env)
        }

        fn list_env(&self, env: &dyn Any) -> Vec<(String, String, Option<String>)> {
            let inner = MeTTaFullStateLanguage;
            inner.list_env(env)
        }

        fn set_env_comment(
            &self,
            env: &mut dyn Any,
            name: &str,
            comment: String,
        ) -> Result<(), String> {
            let inner = MeTTaFullStateLanguage;
            inner.set_env_comment(env, name, comment)
        }

        fn is_env_empty(&self, env: &dyn Any) -> bool {
            let inner = MeTTaFullStateLanguage;
            inner.is_env_empty(env)
        }

        fn infer_term_type(&self, term: &dyn Term) -> TermType {
            let inner = MeTTaFullStateLanguage;
            inner.infer_term_type(term)
        }

        fn infer_var_types(&self, term: &dyn Term) -> Vec<VarTypeInfo> {
            let inner = MeTTaFullStateLanguage;
            inner.infer_var_types(term)
        }

        fn infer_var_type(&self, term: &dyn Term, var_name: &str) -> Option<TermType> {
            let inner = MeTTaFullStateLanguage;
            inner.infer_var_type(term, var_name)
        }
    }

    #[test]
    fn core_ground_eval_hint_is_disabled_when_contracts_missing_in_dispatch() {
        if std::env::var_os("METTAIL_CORE_GROUND_EVAL").is_some() {
            return;
        }

        let mut registry = LanguageRegistry::new();
        registry.register(Box::new(MissingContractsLanguage));
        let mut repl = Repl::new(registry).expect("repl should initialize");
        repl.set_batch_quiet(true);
        repl.load_language("mettafullstate")
            .expect("mettafullstate should load");

        let core_enabled = repl
            .metta_surface_session
            .as_ref()
            .expect("surface session should be available")
            .core_ground_eval_enabled();

        assert!(!core_enabled, "core ground-eval should be disabled when contracts are missing");
    }
}
