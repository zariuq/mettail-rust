use anyhow::Result;
use clap::{Parser, Subcommand};
use mettail_repl::{build_registry, LanguageRegistry, Repl};
use std::fs;

/// MeTTaIL Term Explorer - Interactive REPL for exploring rewrite systems
#[derive(Parser, Debug)]
#[command(name = "mettail")]
#[command(about = "Interactive term exploration for programming languages", long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,

    /// Backward-compatible positional language for interactive REPL startup.
    #[arg(value_name = "LANGUAGE")]
    language: Option<String>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Start the interactive REPL (same behavior as default mode).
    Repl {
        /// Language to load on startup
        #[arg(value_name = "LANGUAGE")]
        language: Option<String>,
    },
    /// Run one term non-interactively and print machine-parseable output.
    Run {
        /// Language name (e.g. rhocalc, lambda, tinymlsmoke)
        #[arg(long = "lang", short = 'l', value_name = "LANGUAGE")]
        language: String,
        /// Term text to parse and execute
        #[arg(long = "term", short = 't', value_name = "TERM", conflicts_with = "term_file")]
        term: Option<String>,
        /// Read term text from file
        #[arg(long = "term-file", value_name = "FILE", conflicts_with = "term")]
        term_file: Option<String>,
    },
    /// List available language names.
    Languages,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let registry = build_registry_safe();

    match args.command {
        Some(Command::Repl { language }) => run_repl(registry, language)?,
        Some(Command::Run {
            language,
            term,
            term_file,
        }) => run_once(&registry, &language, term.as_deref(), term_file.as_deref())?,
        Some(Command::Languages) => {
            for name in sorted_language_names(&registry) {
                println!("{name}");
            }
        },
        None => run_repl(registry, args.language)?,
    }

    Ok(())
}

fn build_registry_safe() -> LanguageRegistry {
    build_registry().unwrap_or_else(|e| {
        eprintln!("Warning: {}", e);
        eprintln!("Continuing with empty registry...");
        LanguageRegistry::new()
    })
}

fn run_repl(registry: LanguageRegistry, language: Option<String>) -> Result<()> {
    let mut repl = Repl::new(registry)?;
    if let Some(language_name) = language {
        repl.load_language(&language_name)?;
    }
    repl.run()?;
    Ok(())
}

fn sorted_language_names(registry: &LanguageRegistry) -> Vec<String> {
    let mut names: Vec<String> = registry.list().into_iter().map(str::to_string).collect();
    names.sort();
    names
}

fn sanitize_line(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

fn resolve_term_input(term: Option<&str>, term_file: Option<&str>) -> Result<String> {
    match (term, term_file) {
        (Some(t), None) => Ok(t.to_string()),
        (None, Some(path)) => Ok(fs::read_to_string(path)?.trim().to_string()),
        (None, None) => anyhow::bail!("Provide exactly one of --term or --term-file"),
        (Some(_), Some(_)) => anyhow::bail!("Provide exactly one of --term or --term-file"),
    }
}

fn run_once(
    registry: &LanguageRegistry,
    language_name: &str,
    term: Option<&str>,
    term_file: Option<&str>,
) -> Result<()> {
    let language = match registry.get(language_name) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("ERROR={}", sanitize_line(&e.to_string()));
            eprintln!(
                "AVAILABLE_LANGUAGES={}",
                sorted_language_names(registry).join(",")
            );
            std::process::exit(2);
        },
    };

    let input = resolve_term_input(term, term_file)?;
    println!("MODE=run");
    println!("LANGUAGE={}", language.name());
    println!("INPUT={}", sanitize_line(&input));

    let parsed = match language.parse_term(&input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("PARSE_OK=0");
            eprintln!("PARSE_ERROR={}", sanitize_line(&e));
            std::process::exit(3);
        },
    };
    println!("PARSE_OK=1");
    println!("TERM_ID={}", parsed.term_id());

    let initial_id = parsed.term_id();
    let results = match language.run_ascent(parsed.as_ref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("ASCENT_OK=0");
            eprintln!("ASCENT_ERROR={}", sanitize_line(&e));
            std::process::exit(4);
        },
    };
    println!("ASCENT_OK=1");
    println!("ALL_TERMS={}", results.all_terms.len());
    println!("REWRITES={}", results.rewrites.len());
    println!("NORMAL_FORMS={}", results.normal_forms().len());

    let targets: Vec<String> = results
        .rewrites_from(initial_id)
        .into_iter()
        .filter_map(|rw| {
            results
                .all_terms
                .iter()
                .find(|t| t.term_id == rw.to_id)
                .map(|info| sanitize_line(&info.display))
        })
        .collect();
    println!("REWRITE_TARGETS={}", targets.join(" | "));

    if let Some(nf) = results.normal_form_reachable_from(initial_id) {
        println!("REACHABLE_NORMAL_FORM={}", sanitize_line(&nf.display));
    } else {
        println!("REACHABLE_NORMAL_FORM=");
    }

    Ok(())
}
