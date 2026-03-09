#[cfg(feature = "mork-backend")]
mod imp_mork_diff {
    use std::collections::BTreeSet;

    use mettail_languages::imp_artifacts::{imp_artifact_dir, load_imp_transition_artifact};
    use mettail_languages::imp_from_lean::{run_imp_mork_backend, IMPLanguage};
    use mettail_runtime::{clear_var_cache, AscentResults, Language};

    fn terminal_done_displays(results: &AscentResults) -> Vec<String> {
        let mut outs = results
            .all_terms
            .iter()
            .filter(|t| t.display.contains("C_Done"))
            .map(|t| t.display.clone())
            .collect::<Vec<_>>();
        outs.sort();
        outs.dedup();
        outs
    }

    fn assert_mork_reaches_done(input: &str) {
        clear_var_cache();
        let lang = IMPLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_imp_mork_backend(term.as_ref()).expect("mork backend should succeed");
        let mork_outs = terminal_done_displays(&mork);
        assert!(
            !mork_outs.is_empty(),
            "IMP MORK backend produced no done states\ninput: {input}\nmork: {mork_outs:?}"
        );
    }

    fn collect_mork_rule_coverage(input: &str, covered: &mut BTreeSet<String>) {
        clear_var_cache();
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
        assert_mork_reaches_done("run skip with store ( 0 , 0 , 0 )");
    }

    #[test]
    fn parity_assign_plus() {
        assert_mork_reaches_done("run x := S 0 + S 0 with store ( 0 , 0 , 0 )");
    }

    #[test]
    fn parity_if_and_not() {
        assert_mork_reaches_done(
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
        for required in
            ["C_Start", "C_RunStmt", "C_RunA", "C_RunB", "C_RetNat", "C_RetBool", "C_RetUnit"]
        {
            assert!(
                transition
                    .sources
                    .iter()
                    .any(|s| s.source_instr == required),
                "required source instruction '{}' missing from IMP transition artifact",
                required
            );
        }
        for required_logical in ["C_Start:R_Start", "C_RetUnit:R_Final", "C_RunStmt:R_Assign", "C_RunA:R_APlus", "C_RetNat:R_KAssign"] {
            let expected_rule_id = transition
                .rules
                .iter()
                .find(|rule| rule.logical_transition_id == required_logical)
                .map(|rule| rule.rule_id.as_str())
                .unwrap_or_else(|| panic!("required logical transition '{}' missing from IMP transition artifact", required_logical));
            assert!(
                covered.contains(expected_rule_id),
                "expected MORK coverage to include rule id '{}' for logical transition '{}', got {:?}",
                expected_rule_id,
                required_logical,
                covered
            );
        }
    }
}
