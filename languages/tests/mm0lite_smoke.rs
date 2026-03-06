use mettail_languages::mm0lite_from_lean::MM0LiteLanguage;
use mettail_runtime::Language;

fn all_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .all_terms
        .iter()
        .map(|t| t.display.clone())
        .collect()
}

fn run_mm0lite(input: &str) -> mettail_runtime::AscentResults {
    mettail_runtime::clear_var_cache();
    let lang = MM0LiteLanguage;
    let term = lang.parse_term(input).expect("parse should succeed");
    lang.run_ascent(term.as_ref())
        .expect("Ascent execution should succeed")
}

#[test]
fn push_goal_then_verify_reaches_verified() {
    let results = run_mm0lite("state [ push P :: [] ] P {} pending");
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("verified")),
        "expected verified terminal state, got: {displays:?}"
    );
}

#[test]
fn wrong_goal_does_not_verify() {
    let results = run_mm0lite("state [ push P :: [] ] Q {} pending");
    let displays = all_displays(&results);
    assert!(
        !displays.iter().any(|d| d.contains("verified")),
        "unexpected verification for wrong goal, got: {displays:?}"
    );
}
