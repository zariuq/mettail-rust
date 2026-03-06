#[cfg(feature = "mork-backend")]
mod mm0lite_mork_diff {
    use std::collections::BTreeSet;

    use mettail_languages::mm0lite_artifacts::{
        load_mm0lite_transition_artifact, mm0lite_artifact_dir,
    };
    use mettail_languages::mm0lite_from_lean::{
        run_mm0lite_mork_backend, MM0LiteLanguage, MM0LiteTerm, MM0LiteTermInner, ProofResult,
        ProofState,
    };
    use mettail_runtime::{AscentResults, Language};

    fn terminal_out_displays(lang: &MM0LiteLanguage, results: &AscentResults) -> Vec<String> {
        let mut outs = Vec::new();
        for term in &results.all_terms {
            let parsed = lang
                .parse_term_for_env(&term.display)
                .expect("MM0Lite term display should reparse");
            let wrapped = parsed
                .as_any()
                .downcast_ref::<MM0LiteTerm>()
                .expect("reparsed term should downcast to MM0LiteTerm");
            let state = match &wrapped.0 {
                MM0LiteTermInner::ProofState(state) => state,
                _ => continue,
            };
            if let ProofState::C_MMState(_, _, _, out) = state {
                if !matches!(out.as_ref(), ProofResult::C_Pending) {
                    outs.push(format!("{}", out));
                }
            }
        }
        outs.sort();
        outs.dedup();
        outs
    }

    fn assert_backend_parity(input: &str) {
        mettail_runtime::clear_var_cache();
        let lang = MM0LiteLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");

        let ascent = lang
            .run_ascent(term.as_ref())
            .expect("ascent backend should succeed");
        let mork = run_mm0lite_mork_backend(term.as_ref()).expect("mork backend should succeed");

        let ascent_outs = terminal_out_displays(&lang, &ascent);
        let mork_outs = terminal_out_displays(&lang, &mork);
        assert_eq!(
            ascent_outs, mork_outs,
            "MM0Lite backend output mismatch\ninput: {input}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
        );
    }

    fn collect_mork_rule_coverage(input: &str, covered: &mut BTreeSet<String>) {
        mettail_runtime::clear_var_cache();
        let lang = MM0LiteLanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mm0lite_mork_backend(term.as_ref()).expect("mork backend should succeed");
        for rw in &mork.rewrites {
            if let Some(rule) = &rw.rule_name {
                covered.insert(rule.clone());
            }
        }
    }

    #[test]
    fn parity_push_goal_then_verify() {
        assert_backend_parity("state [ push P :: [] ] P {} pending");
    }

    #[test]
    fn parity_wrong_goal_stays_unverified() {
        assert_backend_parity("state [ push P :: [] ] Q {} pending");
    }

    #[test]
    fn parity_imp_instr_modus_ponens_from_preloaded_stack() {
        assert_backend_parity("state [ mp :: [] ] Q { ( P -> Q ) ; { P ; {} } } pending");
    }

    #[test]
    fn corpus_transition_rule_coverage_matches_mm0lite_artifact() {
        let mut covered = BTreeSet::new();
        collect_mork_rule_coverage("state [ push P :: [] ] P {} pending", &mut covered);
        collect_mork_rule_coverage("state [ push P :: [] ] Q {} pending", &mut covered);
        collect_mork_rule_coverage(
            "state [ push P :: [ use thm_imp_p_q :: [ mp :: [] ] ] ] Q {} pending",
            &mut covered,
        );

        let transition = load_mm0lite_transition_artifact(&mm0lite_artifact_dir())
            .expect("MM0Lite transition artifact should load");
        for rule in &transition.rules {
            assert!(
                covered.contains(&rule.rule_id),
                "transition rule '{}' from artifact was not exercised by MM0Lite MORK corpus",
                rule.rule_id
            );
        }
    }
}
