use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::Path;

use mettail_runtime::{
    language_supports_auto_backend, AscentResults, Language, RuntimeBackend, TermInfo,
};

#[cfg(feature = "lang-ambient")]
use mettail_languages::ambient::AmbientLanguage;
#[cfg(feature = "lang-calculator")]
use mettail_languages::calculator::CalculatorLanguage;
#[cfg(feature = "lang-imp")]
use mettail_languages::imp_from_lean::IMPLanguage;
#[cfg(feature = "lang-lambda")]
use mettail_languages::lambda::LambdaLanguage;
#[cfg(feature = "lang-he")]
use mettail_languages::mettahe_from_lean::MeTTaHELanguage;
#[cfg(feature = "lang-he")]
use mettail_languages::mettahe_surface::run_mettahe_surface_file_from_path;
#[cfg(feature = "lang-minskylite")]
use mettail_languages::minskylite_from_lean::MinskyLiteLanguage;
#[cfg(feature = "lang-mm0lite")]
use mettail_languages::mm0lite_from_lean::MM0LiteLanguage;
#[cfg(all(feature = "lang-mm0lite", feature = "mork-backend"))]
use mettail_languages::mm0lite_from_lean::{
    parse_mm0_theorem_facts, run_mm0lite_mork_backend_with_limits, with_mm0_theorem_facts,
};
#[cfg(feature = "lang-petta")]
use mettail_languages::petta_from_lean::{
    run_metta_surface_file_from_path, run_metta_surface_file_via_backend_from_path, PeTTaLanguage,
};
#[cfg(feature = "lang-pyashcore")]
use mettail_languages::pyashcore_from_lean::PyashCoreLanguage;
#[cfg(feature = "lang-rhocalc")]
use mettail_languages::rhocalc::RhoCalcLanguage;
#[cfg(all(feature = "lang-mm0lite", feature = "mork-backend"))]
use mettail_runtime::MorkExecutionLimits;

struct Args {
    lang: String,
    backend: RuntimeBackend,
    term: Option<String>,
    file: Option<String>,
    #[cfg(feature = "lang-mm0lite")]
    mm0_db: Option<String>,
}

fn usage() -> ! {
    eprintln!(
        "Usage: mettail-direct --lang <name> [--backend auto|ascent|mork] (--term <text> | --file <path>) [--mm0-db <path>]"
    );
    eprintln!("Examples:");
    eprintln!(
        "  cargo run -p mettail-languages --bin mettail-direct --no-default-features --features \"lang-petta\" -- --lang petta --file examples/program.metta"
    );
    eprintln!(
        "  cargo run -p mettail-languages --bin mettail-direct --no-default-features --features \"mork-backend lang-he\" -- --lang mettahe --backend mork --term 'C_State(...)'"
    );
    std::process::exit(2);
}

fn parse_args() -> Result<Args, String> {
    let mut lang = None;
    let mut backend = RuntimeBackend::Auto;
    let mut term = None;
    let mut file = None;
    #[cfg(feature = "lang-mm0lite")]
    let mut mm0_db = None;

    let mut it = env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--lang" => lang = Some(it.next().ok_or("--lang requires a value")?),
            "--backend" => {
                backend = match it.next().ok_or("--backend requires a value")?.as_str() {
                    "auto" => RuntimeBackend::Auto,
                    "ascent" => RuntimeBackend::Ascent,
                    "mork" => RuntimeBackend::Mork,
                    other => {
                        return Err(format!(
                            "unsupported backend '{}'; expected auto|ascent|mork",
                            other
                        ))
                    },
                }
            },
            "--term" => term = Some(it.next().ok_or("--term requires a value")?),
            "--file" => file = Some(it.next().ok_or("--file requires a value")?),
            "--mm0-db" => {
                #[cfg(feature = "lang-mm0lite")]
                {
                    mm0_db = Some(it.next().ok_or("--mm0-db requires a value")?);
                }
                #[cfg(not(feature = "lang-mm0lite"))]
                {
                    let _ = it.next().ok_or("--mm0-db requires a value")?;
                    return Err("--mm0-db requires the lang-mm0lite feature".to_string());
                }
            },
            "--help" | "-h" => usage(),
            other => return Err(format!("unknown argument '{}'", other)),
        }
    }

    let lang = lang.ok_or("--lang is required")?;
    let inputs = term.is_some() as u8 + file.is_some() as u8;
    if inputs != 1 {
        return Err("provide exactly one of --term or --file".to_string());
    }
    Ok(Args {
        lang,
        backend,
        term,
        file,
        #[cfg(feature = "lang-mm0lite")]
        mm0_db,
    })
}

fn build_language(name: &str) -> Result<Box<dyn Language>, String> {
    #[cfg(feature = "lang-ambient")]
    if name.eq_ignore_ascii_case("ambient") {
        return Ok(Box::new(AmbientLanguage));
    }
    #[cfg(feature = "lang-calculator")]
    if name.eq_ignore_ascii_case("calculator") {
        return Ok(Box::new(CalculatorLanguage));
    }
    #[cfg(feature = "lang-he")]
    if name.eq_ignore_ascii_case("mettahe") || name.eq_ignore_ascii_case("he") {
        return Ok(Box::new(MeTTaHELanguage));
    }
    #[cfg(feature = "lang-imp")]
    if name.eq_ignore_ascii_case("imp") {
        return Ok(Box::new(IMPLanguage));
    }
    #[cfg(feature = "lang-lambda")]
    if name.eq_ignore_ascii_case("lambda") {
        return Ok(Box::new(LambdaLanguage));
    }
    #[cfg(feature = "lang-minskylite")]
    if name.eq_ignore_ascii_case("minskylite") {
        return Ok(Box::new(MinskyLiteLanguage));
    }
    #[cfg(feature = "lang-mm0lite")]
    if name.eq_ignore_ascii_case("mm0lite") {
        return Ok(Box::new(MM0LiteLanguage));
    }
    #[cfg(feature = "lang-petta")]
    if name.eq_ignore_ascii_case("petta") {
        return Ok(Box::new(PeTTaLanguage));
    }
    #[cfg(feature = "lang-pyashcore")]
    if name.eq_ignore_ascii_case("pyashcore") {
        return Ok(Box::new(PyashCoreLanguage));
    }
    #[cfg(feature = "lang-rhocalc")]
    if name.eq_ignore_ascii_case("rhocalc") {
        return Ok(Box::new(RhoCalcLanguage));
    }
    Err(format!(
        "language '{}' is unavailable in this build; enable the corresponding lang-* feature",
        name
    ))
}

fn reachable_normal_forms<'a>(results: &'a AscentResults, start_id: u64) -> Vec<&'a TermInfo> {
    let term_by_id = |id: u64| results.all_terms.iter().find(|t| t.term_id == id);
    let Some(start) = term_by_id(start_id) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut visited = HashSet::new();
    let mut queue = std::collections::VecDeque::from([start.term_id]);
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

fn print_eval_results(results: &mettail_runtime::EvalResults) {
    if results.normal_forms.is_empty() {
        println!("No results.");
        return;
    }
    for nf in &results.normal_forms {
        println!("{}", nf);
    }
}

fn print_results(results: &AscentResults, start_id: u64) {
    let normal_forms = reachable_normal_forms(results, start_id);
    if normal_forms.is_empty() {
        println!("No reachable normal forms.");
        for term in &results.all_terms {
            let nf = if term.is_normal_form { " [normal]" } else { "" };
            println!("{}{}", term.display, nf);
        }
        return;
    }
    println!("Reachable normal forms: {}", normal_forms.len());
    for nf in normal_forms {
        println!("{}", nf.display);
    }
}

fn should_use_registered_backend(language: &dyn Language, backend: RuntimeBackend) -> bool {
    matches!(backend, RuntimeBackend::Mork)
        || (matches!(backend, RuntimeBackend::Auto)
            && language_supports_auto_backend(language.name()))
}

fn main() -> Result<(), String> {
    let args = parse_args().unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        usage();
    });

    #[cfg(feature = "mork-backend")]
    mettail_languages::register_default_core_backends()?;

    let language = build_language(&args.lang)?;

    #[cfg(feature = "lang-petta")]
    if args.lang.eq_ignore_ascii_case("petta") && args.file.is_some() {
        let file_path = args.file.as_ref().unwrap();
        if file_path.ends_with(".metta") {
            let result = if should_use_registered_backend(language.as_ref(), args.backend) {
                run_metta_surface_file_via_backend_from_path(
                    language.as_ref(),
                    args.backend,
                    Path::new(file_path),
                    language.metadata().library_aliases(),
                )?
            } else {
                run_metta_surface_file_from_path(
                    Path::new(file_path),
                    language.metadata().library_aliases(),
                )?
            };
            for line in &result.outputs {
                println!("{}", line);
            }
            // Test assertions are now handled by MORK TestAssertion host
            // kind; failures appear as [error] lines in outputs.
            let error_count = result.outputs.iter().filter(|l| l.starts_with("[error]")).count();
            if error_count > 0 {
                return Err(format!("{} error(s) in output", error_count));
            }
            return Ok(());
        }
    }

    #[cfg(feature = "lang-he")]
    if (args.lang.eq_ignore_ascii_case("mettahe") || args.lang.eq_ignore_ascii_case("he"))
        && args.file.is_some()
    {
        let file_path = args.file.as_ref().unwrap();
        if file_path.ends_with(".metta") {
            let result = run_mettahe_surface_file_from_path(
                language.as_ref(),
                args.backend,
                Path::new(file_path),
                language.metadata().library_aliases(),
            )?;
            for line in &result.outputs {
                println!("{}", line);
            }
            // Test assertions are now handled by MORK TestAssertion host
            // kind; failures appear as [error] lines in outputs.
            let error_count = result.outputs.iter().filter(|l| l.starts_with("[error]")).count();
            if error_count > 0 {
                return Err(format!("{} error(s) in output", error_count));
            }
            return Ok(());
        }
    }

    let input = if let Some(term) = args.term {
        term
    } else {
        fs::read_to_string(args.file.as_ref().expect("validated input path"))
            .map_err(|e| format!("failed to read input file: {e}"))?
    };

    #[cfg(all(feature = "lang-mm0lite", feature = "mork-backend"))]
    if args.lang.eq_ignore_ascii_case("mm0lite") && args.mm0_db.is_some() {
        let db_src = fs::read_to_string(args.mm0_db.as_ref().expect("validated mm0 db path"))
            .map_err(|e| format!("failed to read MM0 DB file: {e}"))?;
        let theorem_facts = parse_mm0_theorem_facts(&db_src)?;
        let lang = MM0LiteLanguage;
        let term = lang.parse_term(&input)?;
        let results = with_mm0_theorem_facts(&theorem_facts, || {
            if matches!(args.backend, RuntimeBackend::Mork | RuntimeBackend::Auto) {
                run_mm0lite_mork_backend_with_limits(term.as_ref(), MorkExecutionLimits::default())
            } else {
                lang.run_backend(term.as_ref(), args.backend)
            }
        })?;
        print_results(&results, term.term_id());
        return Ok(());
    }

    let term = language.parse_term(&input)?;

    if should_use_registered_backend(language.as_ref(), args.backend) {
        let results = language.run_backend(term.as_ref(), args.backend)?;
        print_results(&results, term.term_id());
    } else {
        let results = language.run_eval(term.as_ref())?;
        print_eval_results(&results);
    }
    Ok(())
}
