#[cfg(feature = "mork-backend")]
mod mettahe_mork_smoke {
    use codex_he_harness::mettahe_from_lean::{
        he_transition_artifact_rule_ids, run_mettahe_mork_backend, Instr, MeTTaHELanguage,
        MeTTaHETerm, MeTTaHETermInner, State,
    };
    use mettail_runtime::{AscentResults, Language};

    fn done_out_displays(lang: &MeTTaHELanguage, results: &AscentResults) -> Vec<String> {
        let mut outs = Vec::new();
        for term in &results.all_terms {
            if !term.display.starts_with("C_State(C_Done") {
                continue;
            }
            let parsed = lang
                .parse_term_for_env(&term.display)
                .expect("done-state display should reparse");
            let wrapped = parsed
                .as_any()
                .downcast_ref::<MeTTaHETerm>()
                .expect("reparsed done state should downcast to MeTTaHETerm");
            let state = match &wrapped.0 {
                MeTTaHETermInner::State(state) => state,
                _ => continue,
            };
            if let State::C_State(instr, _, out) = state {
                if matches!(instr.as_ref(), Instr::C_Done) {
                    outs.push(format!("{}", out));
                }
            }
        }
        outs.sort();
        outs.dedup();
        outs
    }

    fn run_case(input: &str) -> Vec<String> {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        done_out_displays(&lang, &mork)
    }

    #[test]
    fn metta_empty_reaches_done_on_mork() {
        let outs = run_case("C_State(C_Metta(C_Empty, C_AtomType), C_Space(C_ExprNil), C_Empty)");
        assert_eq!(outs, vec!["C_Empty".to_string()]);
    }

    #[test]
    fn metta_symbol_atomtype_reaches_done_on_mork() {
        let outs =
            run_case("C_State(C_Metta(C_SymAtom(foo), C_AtomType), C_Space(C_ExprNil), C_Empty)");
        assert_eq!(outs, vec!["C_SymAtom(foo)".to_string()]);
    }

    #[test]
    fn metta_call_equation_match_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_AtomType",
            "),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_SymAtom(result1)",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
        assert_eq!(outs, vec!["C_SymAtom(result1)".to_string()]);
    }

    #[test]
    fn typecast_match_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_TypeCast(C_SymAtom(foo), C_SymbolType),",
            "C_Space(",
            "C_ExprCons(",
            "C_TypeAnnotation(C_SymAtom(foo), C_SymbolType),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
        assert_eq!(outs, vec!["C_SymAtom(foo)".to_string()]);
    }

    #[test]
    fn typecast_mismatch_reaches_error_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_TypeCast(C_SymAtom(foo), C_GroundedType),",
            "C_Space(",
            "C_ExprCons(",
            "C_TypeAnnotation(C_SymAtom(foo), C_SymbolType),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
        assert!(
            outs.iter()
                .any(|o| o.contains("C_ErrorAtom") && o.contains("C_BadType")),
            "expected type-cast mismatch error, got: {outs:?}"
        );
    }

    #[test]
    fn transition_artifact_has_expected_rule_ids() {
        let ids = he_transition_artifact_rule_ids().expect("he transition artifact should load");
        for required in ["R0", "R36", "R37", "R38", "R39", "R40", "R41", "R42"] {
            assert!(ids.contains(&required.to_string()), "missing HE rule id {required}");
        }
    }
}
