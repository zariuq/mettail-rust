use mettail_languages::imp_from_lean::IMPLanguage;
use mettail_runtime::Language;

fn all_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results.all_terms.iter().map(|t| t.display.clone()).collect()
}

fn run_imp(input: &str) -> mettail_runtime::AscentResults {
    mettail_runtime::clear_var_cache();
    let lang = IMPLanguage;
    let term = lang.parse_term(input).expect("parse should succeed");
    lang.run_ascent(term.as_ref())
        .expect("Ascent execution should succeed")
}

#[test]
fn skip_reaches_done() {
    let results = run_imp("run skip with store ( 0 , 0 , 0 )");
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("done")),
        "expected done terminal state, got: {displays:?}"
    );
}

#[test]
fn assignment_updates_store() {
    let results = run_imp("run x := S 0 with store ( 0 , 0 , 0 )");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("done") && d.contains("store") && d.contains("S 0")),
        "expected updated store with S 0, got: {displays:?}"
    );
}
