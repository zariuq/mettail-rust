#[cfg(feature = "mork-backend")]
mod imp_mork_diff {
    use std::collections::BTreeSet;

    use mettail_languages::imp_artifacts::{imp_artifact_dir, load_imp_transition_artifact};
    use mettail_languages::imp_from_lean::{run_imp_mork_backend, IMPLanguage};
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
        let lang = IMPLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");

        let ascent = lang.run_ascent(term.as_ref()).expect("ascent backend should succeed");
        let mork = run_imp_mork_backend(term.as_ref()).expect("mork backend should succeed");

        let ascent_outs = terminal_done_displays(&ascent);
        let mork_outs = terminal_done_displays(&mork);
        assert!(!mork_outs.is_empty(), "IMP MORK backend produced no done states\ninput: {input}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}");
        for out in &mork_outs {
            assert!(
                ascent_outs.contains(out),
                "IMP Ascent backend is missing MORK terminal state\ninput: {input}\nmissing: {out}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
            );
        }
    }

    fn collect_mork_rule_coverage(input: &str, covered: &mut BTreeSet<String>) {
        mettail_runtime::clear_var_cache();
        let lang = IMPLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_imp_mork_backend(term.as_ref()).expect("mork backend should succeed");
        for rw in &mork.rewrites {
            if let Some(rule) = &rw.rule_name {
                covered.insert(rule.clone());
            }
        }
    }

    #[test]
    fn parity_skip() {
        assert_backend_parity("run skip with store ( 0 , 0 , 0 )");
    }

    #[test]
    fn parity_assign_plus() {
        assert_backend_parity("run x := S 0 + S 0 with store ( 0 , 0 , 0 )");
    }

    #[test]
    fn parity_if_and_not() {
        assert_backend_parity(
            "run if not false and true then x := S 0 else x := 0 with store ( 0 , 0 , 0 )",
        );
    }

    #[test]
    fn corpus_transition_rule_coverage_hits_key_imp_rules() {
        let mut covered = BTreeSet::new();
        collect_mork_rule_coverage("run skip with store ( 0 , 0 , 0 )", &mut covered);
        collect_mork_rule_coverage("run x := S 0 + S 0 with store ( 0 , 0 , 0 )", &mut covered);
        collect_mork_rule_coverage(
            "run if not false and true then x := S 0 else x := 0 with store ( 0 , 0 , 0 )",
            &mut covered,
        );
        collect_mork_rule_coverage(
            "run while x == 0 do x := S 0 with store ( 0 , 0 , 0 )",
            &mut covered,
        );

        let transition = load_imp_transition_artifact(&imp_artifact_dir())
            .expect("IMP transition artifact should load");
        for required in ["C_Start", "C_RunStmt", "C_RunA", "C_RunB", "C_RetNat", "C_RetBool", "C_RetUnit"] {
            assert!(
                transition.sources.iter().any(|s| s.source_instr == required),
                "required source instruction '{}' missing from IMP transition artifact",
                required
            );
        }
        assert!(covered.contains("R_Start"));
        assert!(covered.contains("R_Final"));
        assert!(covered.contains("R_Assign"));
        assert!(covered.contains("R_APlus"));
        assert!(covered.contains("R_KAssign"));
    }
}
