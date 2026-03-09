#[cfg(feature = "mork-backend")]
use mettail_languages::imp_from_lean::{run_imp_mork_backend, IMPLanguage};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{clear_var_cache, Language};

#[cfg(feature = "mork-backend")]
fn all_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .all_terms
        .iter()
        .map(|t| t.display.clone())
        .collect()
}

#[cfg(feature = "mork-backend")]
fn run_imp(input: &str) -> mettail_runtime::AscentResults {
    clear_var_cache();
    let lang = IMPLanguage;
    let term = lang.parse_term(input).expect("parse should succeed");
    run_imp_mork_backend(term.as_ref()).expect("MORK execution should succeed")
}

#[cfg(feature = "mork-backend")]
#[test]
fn skip_reaches_done() {
    let results = run_imp("run skip with store ( 0 , 0 , 0 )");
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("C_Done")),
        "expected done terminal state, got: {displays:?}"
    );
}

#[cfg(feature = "mork-backend")]
#[test]
fn assignment_updates_store() {
    let results = run_imp("run x := S 0 with store ( 0 , 0 , 0 )");
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| {
            d.contains("C_Done") && d.contains("C_Store(C_Succ(C_Zero) , C_Zero , C_Zero)")
        }),
        "expected updated store with S 0, got: {displays:?}"
    );
}
