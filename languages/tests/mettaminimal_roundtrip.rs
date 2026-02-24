use mettail_languages::mettaminimal_from_lean::MeTTaMinimalStateLanguage;
use mettail_runtime::Language;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!(
            "Usage: {} <input-term> <expected-term>",
            args.first()
                .map_or("mettaminimal_roundtrip", String::as_str)
        );
        std::process::exit(2);
    }

    let input = &args[1];
    let expected = &args[2];

    let lang = MeTTaMinimalStateLanguage;
    mettail_runtime::clear_var_cache();

    let term = match lang.parse_term(input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("PARSE_ERROR={}", e);
            std::process::exit(3);
        },
    };

    let initial_id = term.term_id();
    let expected_term = match lang.parse_term(expected) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("EXPECTED_PARSE_ERROR={}", e);
            std::process::exit(6);
        },
    };
    let expected_id = expected_term.term_id();

    let results = match lang.run_ascent(term.as_ref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("ASCENT_ERROR={}", e);
            std::process::exit(4);
        },
    };

    let mut actual_targets: Vec<String> = Vec::new();
    let mut hit_expected_id = false;
    for rw in results.rewrites_from(initial_id) {
        if rw.to_id == expected_id {
            hit_expected_id = true;
        }
        if let Some(info) = results.all_terms.iter().find(|t| t.term_id == rw.to_id) {
            actual_targets.push(info.display.clone());
        }
    }

    println!("RUST_INPUT={}", input);
    println!("RUST_EXPECTED={}", expected);
    println!("RUST_TARGETS={}", actual_targets.join(" | "));

    if hit_expected_id
        || actual_targets
            .iter()
            .any(|t| t.replace(' ', "") == expected.replace(' ', ""))
    {
        println!("ROUNDTRIP_OK");
        return;
    }

    eprintln!("ROUNDTRIP_FAIL");
    std::process::exit(5);
}
