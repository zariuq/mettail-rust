use mettail_languages::tinyml_from_lean::TinyMLSmokeLanguage;
use mettail_runtime::Language;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!(
            "Usage: {} <input-term> <expected-term>",
            args.first().map_or("tinymlsmoke_roundtrip", String::as_str)
        );
        std::process::exit(2);
    }

    let input = &args[1];
    let expected = &args[2];

    let lang = TinyMLSmokeLanguage;
    mettail_runtime::clear_var_cache();

    let term = match lang.parse_term(input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("PARSE_ERROR={}", e);
            std::process::exit(3);
        },
    };

    let initial_id = term.term_id();
    let results = match lang.run_ascent(term.as_ref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("ASCENT_ERROR={}", e);
            std::process::exit(4);
        },
    };

    let mut actual_targets: Vec<String> = Vec::new();
    for rw in results.rewrites_from(initial_id) {
        if let Some(info) = results.all_terms.iter().find(|t| t.term_id == rw.to_id) {
            actual_targets.push(info.display.clone());
        }
    }

    println!("RUST_INPUT={}", input);
    println!("RUST_EXPECTED={}", expected);
    println!("RUST_TARGETS={}", actual_targets.join(" | "));

    if actual_targets.iter().any(|t| t == expected) {
        println!("ROUNDTRIP_OK");
        return;
    }

    eprintln!("ROUNDTRIP_FAIL");
    std::process::exit(5);
}
