use mettail_languages::minskylite_from_lean::MinskyLiteLanguage;
use mettail_runtime::Language;

fn all_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .all_terms
        .iter()
        .map(|t| t.display.clone())
        .collect()
}

fn run_minskylite(input: &str) -> mettail_runtime::AscentResults {
    mettail_runtime::clear_var_cache();
    let lang = MinskyLiteLanguage;
    let term = lang.parse_term(input).expect("parse should succeed");
    lang.run_ascent(term.as_ref())
        .expect("Ascent execution should succeed")
}

#[test]
fn inc_then_halt_reaches_done() {
    let results = run_minskylite("state incA halt Z Z running");
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("done")),
        "expected done terminal state, got: {displays:?}"
    );
}

#[test]
fn zero_branch_keeps_zero_register() {
    let results = run_minskylite("state decA ( halt , halt ) Z Z running");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("halt") && d.contains("done")),
        "expected halt+done state after zero-branch, got: {displays:?}"
    );
}
