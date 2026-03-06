use anyhow::Result;
use clap::Parser;
use mettail_repl::{build_registry, Repl};

/// MeTTaIL Term Explorer - Interactive REPL for exploring rewrite systems
#[derive(Parser, Debug)]
#[command(name = "mettail")]
#[command(about = "Interactive term exploration for programming languages", long_about = None)]
#[command(
    after_help = "Examples:\n  mettail --lang mettahe --parser-backend tree-sitter --run-metta-file ../hyperon-experimental/python/tests/scripts/b4_nondeterm.metta\n  mettail --lang mettahe --run-metta-file ../hyperon-experimental/python/tests/scripts/b5_types_prelim.metta --surface-fuel 1024 --surface-deterministic\n  mettail --run-mm2-file ../MORK/examples/fibonacci_unfold_fold/fibonacci_bottom_up.mm2 --mm2-max-steps 200\n  mettail --lang mm0lite --run-mm0lite-file examples/mm0lite/demo.mm0 --mm0lite-state-file examples/mm0lite/demo.state\n  mettail --lang mettahe -c \"(= (id $x) $x)\" -c \"!(id 5)\"\n  mettail mettahe --interactive"
)]
struct Args {
    /// Language to load on startup (positional form)
    #[arg(value_name = "LANGUAGE")]
    language: Option<String>,

    /// Language to load on startup
    #[arg(long, value_name = "LANGUAGE")]
    lang: Option<String>,

    /// Run a .metta surface file and exit unless --interactive (requires --lang)
    #[arg(long, value_name = "FILE")]
    run_metta_file: Option<String>,

    /// Run a raw MM2 file directly through MORK (requires --features mork-backend)
    #[arg(long, value_name = "FILE")]
    run_mm2_file: Option<String>,

    /// Run an MM0 theorem DB + MM0Lite state file through MM0Lite backend (requires --lang mm0lite)
    #[arg(long, value_name = "FILE")]
    run_mm0lite_file: Option<String>,

    /// MM0Lite state input for --run-mm0lite-file
    #[arg(long, value_name = "FILE")]
    mm0lite_state_file: Option<String>,

    /// Report format for --run-metta-file: text|json|jsonl
    #[arg(long, default_value = "text", value_name = "MODE", value_parser = ["text", "json", "jsonl"])]
    report: String,

    /// Optional report output path for --run-metta-file
    #[arg(long, value_name = "PATH")]
    report_file: Option<String>,

    /// Surface parser backend: legacy|tree-sitter
    #[arg(long, value_name = "BACKEND", value_parser = ["legacy", "tree-sitter"])]
    parser_backend: Option<String>,

    /// Run a REPL command non-interactively (repeatable)
    #[arg(short = 'c', long = "command", value_name = "CMD")]
    commands: Vec<String>,

    /// Drop into interactive REPL after batch commands
    #[arg(long)]
    interactive: bool,

    /// Reduce non-essential output in batch mode (recommended with --report json/jsonl)
    #[arg(long)]
    quiet_batch: bool,

    /// Max surface rewrite steps per eval line (run-metta-file only)
    #[arg(long, value_name = "N")]
    surface_fuel: Option<usize>,

    /// Max core rewrites allowed per eval line (run-metta-file only)
    #[arg(long, value_name = "N")]
    core_fuel: Option<usize>,

    /// Execute only the first lowered surface branch per eval line (run-metta-file only)
    #[arg(long)]
    surface_first_branch: bool,

    /// Prefer exact (non-pattern) equation matches during surface rewriting (run-metta-file only)
    #[arg(long)]
    surface_exact_priority: bool,

    /// Enable deterministic ground-call memoization in surface rewriting (run-metta-file only)
    #[arg(long)]
    surface_memo: bool,

    /// Disable default ground-call memoization in surface rewriting (run-metta-file only)
    #[arg(long)]
    surface_no_memo: bool,

    /// Deterministic surface policy: first-branch + exact-priority + memo (run-metta-file only)
    #[arg(long)]
    surface_deterministic: bool,

    /// Use MORK forward-chaining engine instead of Ascent/datalog (run-metta-file only; requires --features mork-backend)
    #[arg(long)]
    mork_backend: bool,

    /// MORK policy: number of unfold/base/fold rule copies (run-metta-file only)
    #[arg(long, value_name = "N")]
    mork_rule_copies: Option<usize>,

    /// MORK policy: max fixpoint transitions (run-metta-file only)
    #[arg(long, value_name = "N")]
    mork_max_steps: Option<usize>,

    /// MORK policy: max fixpoint transitions for --run-mm2-file
    #[arg(long, value_name = "N")]
    mm2_max_steps: Option<usize>,

    /// MORK policy: max transitions for --run-mm0lite-file
    #[arg(long, value_name = "N")]
    mm0lite_max_steps: Option<usize>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    if let Some(backend) = &args.parser_backend {
        std::env::set_var("METTAIL_PARSER_BACKEND", backend);
    }

    if args.report_file.is_some() && args.run_metta_file.is_none() {
        anyhow::bail!("--report-file requires --run-metta-file");
    }
    if [
        args.run_metta_file.is_some(),
        args.run_mm2_file.is_some(),
        args.run_mm0lite_file.is_some(),
    ]
    .into_iter()
    .filter(|x| *x)
    .count()
        > 1
    {
        anyhow::bail!(
            "--run-metta-file, --run-mm2-file, and --run-mm0lite-file are mutually exclusive"
        );
    }
    if (args.surface_fuel.is_some()
        || args.core_fuel.is_some()
        || args.surface_first_branch
        || args.surface_exact_priority
        || args.surface_memo
        || args.surface_no_memo
        || args.surface_deterministic
        || args.mork_backend
        || args.mork_rule_copies.is_some()
        || args.mork_max_steps.is_some())
        && args.run_metta_file.is_none()
    {
        anyhow::bail!(
            "--surface-fuel/--core-fuel/--surface-first-branch/--surface-exact-priority/--surface-memo/--surface-no-memo/--surface-deterministic/--mork-backend/--mork-rule-copies/--mork-max-steps require --run-metta-file"
        );
    }
    if args.mm2_max_steps.is_some() && args.run_mm2_file.is_none() {
        anyhow::bail!("--mm2-max-steps requires --run-mm2-file");
    }
    if args.mm0lite_state_file.is_some() && args.run_mm0lite_file.is_none() {
        anyhow::bail!("--mm0lite-state-file requires --run-mm0lite-file");
    }
    if args.mm0lite_max_steps.is_some() && args.run_mm0lite_file.is_none() {
        anyhow::bail!("--mm0lite-max-steps requires --run-mm0lite-file");
    }
    if args.run_mm0lite_file.is_some() && args.mm0lite_state_file.is_none() {
        anyhow::bail!("--run-mm0lite-file requires --mm0lite-state-file");
    }
    if args.surface_memo && args.surface_no_memo {
        anyhow::bail!("--surface-memo and --surface-no-memo are mutually exclusive");
    }

    // Build the language registry
    let registry = build_registry().unwrap_or_else(|e| {
        eprintln!("Warning: {}", e);
        eprintln!("Continuing with empty registry...");
        mettail_repl::LanguageRegistry::new()
    });

    // Create and run the REPL
    let mut repl = Repl::new(registry)?;
    repl.set_batch_quiet(args.quiet_batch);

    // If a language was specified, load it on startup.
    let startup_language = args.lang.or(args.language);
    if let Some(language_name) = startup_language {
        repl.load_language(&language_name)?;
    }

    let mut batch_commands: Vec<String> = Vec::new();
    batch_commands.extend(args.commands);

    if let Some(file) = args.run_metta_file {
        if repl.name_str().is_none() {
            anyhow::bail!("--run-metta-file requires --lang (e.g. --lang mettahe)");
        }
        let mut cmd = format!("run-metta-file {file}");
        if args.report != "text" {
            cmd.push_str(&format!(" --report={}", args.report));
        }
        if let Some(path) = args.report_file {
            cmd.push_str(&format!(" --report-file={path}"));
        }
        if let Some(surface_fuel) = args.surface_fuel {
            cmd.push_str(&format!(" --surface-fuel={surface_fuel}"));
        }
        if let Some(core_fuel) = args.core_fuel {
            cmd.push_str(&format!(" --core-fuel={core_fuel}"));
        }
        if args.surface_first_branch {
            cmd.push_str(" --surface-first-branch");
        }
        if args.surface_exact_priority {
            cmd.push_str(" --surface-exact-priority");
        }
        if args.surface_memo {
            cmd.push_str(" --surface-memo");
        }
        if args.surface_no_memo {
            cmd.push_str(" --surface-no-memo");
        }
        if args.surface_deterministic {
            cmd.push_str(" --surface-deterministic");
        }
        if args.mork_backend {
            cmd.push_str(" --mork-backend");
        }
        if let Some(rule_copies) = args.mork_rule_copies {
            cmd.push_str(&format!(" --mork-rule-copies={rule_copies}"));
        }
        if let Some(max_steps) = args.mork_max_steps {
            cmd.push_str(&format!(" --mork-max-steps={max_steps}"));
        }
        batch_commands.push(cmd);
    }

    if let Some(file) = args.run_mm2_file {
        let mut cmd = format!("run-mm2-file {file}");
        if let Some(max_steps) = args.mm2_max_steps {
            cmd.push_str(&format!(" --mork-max-steps={max_steps}"));
        }
        batch_commands.push(cmd);
    }

    if let Some(db_file) = args.run_mm0lite_file {
        if repl.name_str().is_none() {
            anyhow::bail!("--run-mm0lite-file requires --lang mm0lite");
        }
        let state_file = args
            .mm0lite_state_file
            .ok_or_else(|| anyhow::anyhow!("--run-mm0lite-file requires --mm0lite-state-file"))?;
        let mut cmd = format!("run-mm0lite-file {db_file} {state_file}");
        if let Some(max_steps) = args.mm0lite_max_steps {
            cmd.push_str(&format!(" --mork-max-steps={max_steps}"));
        }
        batch_commands.push(cmd);
    }

    for cmd in &batch_commands {
        repl.run_command(cmd)?;
    }

    let has_batch = !batch_commands.is_empty();
    if !has_batch || args.interactive {
        repl.run()?;
    }

    Ok(())
}
