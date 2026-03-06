#[cfg(feature = "mork-backend")]
mod minskylite_mork_diff {
    use std::collections::BTreeSet;

    use mettail_languages::minskylite_artifacts::{
        load_minskylite_transition_artifact, minskylite_artifact_dir,
    };
    use mettail_languages::minskylite_from_lean::{
        run_minskylite_mork_backend, MinskyLiteLanguage,
    };
    use mettail_runtime::{AscentResults, Language};

    fn terminal_done_displays(results: &AscentResults) -> Vec<String> {
        let mut outs = results
            .all_terms
            .iter()
            .filter(|t| t.display.contains("done"))
            .map(|t| t.display.clone())
            .collect::<Vec<_>>();
        outs.sort();
        outs.dedup();
        outs
    }

    fn assert_backend_parity(input: &str) {
        mettail_runtime::clear_var_cache();
        let lang = MinskyLiteLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");

        let ascent = lang
            .run_ascent(term.as_ref())
            .expect("ascent backend should succeed");
        let mork = run_minskylite_mork_backend(term.as_ref()).expect("mork backend should succeed");

        let ascent_outs = terminal_done_displays(&ascent);
        let mork_outs = terminal_done_displays(&mork);
        assert!(
            !mork_outs.is_empty(),
            "MinskyLite MORK backend produced no done states\ninput: {input}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
        );
        for out in &mork_outs {
            assert!(
                ascent_outs.contains(out),
                "MinskyLite Ascent backend is missing MORK terminal state\ninput: {input}\nmissing: {out}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
            );
        }
        assert!(
            !ascent_outs.is_empty(),
            "MinskyLite Ascent backend produced no done states\ninput: {input}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
        );
    }

    fn collect_mork_rule_coverage(input: &str, covered: &mut BTreeSet<String>) {
        mettail_runtime::clear_var_cache();
        let lang = MinskyLiteLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_minskylite_mork_backend(term.as_ref()).expect("mork backend should succeed");
        for rw in &mork.rewrites {
            if let Some(rule) = &rw.rule_name {
                covered.insert(rule.clone());
            }
        }
    }

    #[test]
    fn parity_increment_then_halt() {
        assert_backend_parity("state incA halt Z Z running");
    }

    #[test]
    fn parity_deca_zero_branch() {
        assert_backend_parity("state decA ( halt , halt ) Z Z running");
    }

    #[test]
    fn parity_decb_positive_branch() {
        assert_backend_parity("state decB ( halt , halt ) Z S Z running");
    }

    #[test]
    fn corpus_transition_rule_coverage_matches_minskylite_artifact() {
        let mut covered = BTreeSet::new();
        collect_mork_rule_coverage("state incA halt Z Z running", &mut covered);
        collect_mork_rule_coverage("state incB halt Z Z running", &mut covered);
        collect_mork_rule_coverage("state decA ( halt , halt ) Z Z running", &mut covered);
        collect_mork_rule_coverage("state decA ( halt , halt ) S Z Z running", &mut covered);
        collect_mork_rule_coverage("state decB ( halt , halt ) Z Z running", &mut covered);
        collect_mork_rule_coverage("state decB ( halt , halt ) Z S Z running", &mut covered);

        let transition = load_minskylite_transition_artifact(&minskylite_artifact_dir())
            .expect("MinskyLite transition artifact should load");
        for rule in &transition.rules {
            assert!(
                covered.contains(&rule.rule_id),
                "transition rule '{}' from artifact was not exercised by MinskyLite MORK corpus",
                rule.rule_id
            );
        }
    }
}
