use codex_imp_harness::imp_from_lean::IMPLanguage;
#[cfg(feature = "mork-backend")]
use codex_imp_harness::imp_from_lean::run_imp_mork_backend;
use mettail_runtime::Language;

fn main() {
    let mut args = std::env::args().skip(1);
    let mut backend = String::from("mork");
    let mut rest = Vec::new();
    while let Some(arg) = args.next() {
        if arg == "--backend" {
            backend = args.next().unwrap_or_else(|| {
                eprintln!("missing value after --backend");
                std::process::exit(2);
            });
        } else {
            rest.push(arg);
        }
    }
    let input = rest.join(" ");
    if input.trim().is_empty() {
        eprintln!("usage: smoke [--backend mork|ascent] '<imp input>'");
        std::process::exit(2);
    }

    mettail_runtime::clear_var_cache();
    let lang = IMPLanguage;
    let term = lang.parse_term(&input).expect("parse should succeed");
    let results = match backend.as_str() {
        "ascent" => lang
            .run_ascent(term.as_ref())
            .expect("Ascent execution should succeed"),
        "mork" => run_mork(term.as_ref()),
        other => {
            eprintln!("unsupported backend '{}'; expected ascent or mork", other);
            std::process::exit(2);
        },
    };

    for term in &results.all_terms {
        println!("{}", term.display);
    }
}

fn run_mork(term: &dyn mettail_runtime::Term) -> mettail_runtime::AscentResults {
    #[cfg(feature = "mork-backend")]
    {
        return run_imp_mork_backend(term).expect("MORK execution should succeed");
    }
    #[cfg(not(feature = "mork-backend"))]
    {
        let _ = term;
        eprintln!("backend 'mork' requires building smoke with --features mork-backend");
        std::process::exit(2);
    }
}
