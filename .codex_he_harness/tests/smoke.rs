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
    fn metta_call_no_match_returns_original_call_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_SymAtom(g), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
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
        assert_eq!(outs.len(), 1);
        assert!(
            outs[0].contains("C_SymAtom(g)")
                && outs[0].contains("C_SymAtom(a)")
                && outs[0].contains("C_ExprNil"),
            "expected original call expression, got: {outs:?}"
        );
    }

    #[test]
    fn metta_call_pattern_equation_substitutes_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_AtomType",
            "),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_VarAtom(C_SymAtom(x)), C_ExprNil)),",
            "C_VarAtom(C_SymAtom(x))",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
        assert_eq!(outs, vec!["C_SymAtom(a)".to_string()]);
    }

    #[test]
    fn return_after_op_no_args_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_SymAtom(f)),",
            "C_Space(C_ExprNil),",
            "C_KAfterOp(",
            "C_ExprNil,",
            "C_ArrowType(C_ExprNil, C_AtomType),",
            "C_AtomType,",
            "C_Empty",
            ")",
            ")"
        ));
        assert_eq!(outs.len(), 1);
        assert!(
            outs[0].contains("C_ExprCons(C_SymAtom(f)") && outs[0].contains("C_ExprNil"),
            "expected unary call result, got: {outs:?}"
        );
    }

    #[test]
    fn return_after_op_two_args_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_SymAtom(f)),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(",
            "C_SymAtom(f),",
            "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprNil))",
            "),",
            "C_SymAtom(result2)",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_KAfterOp(",
            "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
            "C_ArrowType(C_ExprCons(C_AtomType, C_ExprCons(C_AtomType, C_ExprNil)), C_AtomType),",
            "C_AtomType,",
            "C_Empty",
            ")",
            ")"
        ));
        assert_eq!(outs, vec!["C_SymAtom(result2)".to_string()]);
    }

    #[test]
    fn return_after_args_error_bubbles_to_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_ErrorAtom(C_SymAtom(foo), C_BadType(C_GroundedType, C_SymbolType))),",
            "C_Space(C_ExprNil),",
            "C_KAfterArgs(C_SymAtom(f), C_AtomType, C_Empty)",
            ")"
        ));
        assert!(
            outs.iter()
                .any(|o| o.contains("C_ErrorAtom") && o.contains("C_BadType")),
            "expected bubbled after-args error, got: {outs:?}"
        );
    }

    #[test]
    fn return_after_args_call_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_SymAtom(result_after_args)",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_KAfterArgs(C_SymAtom(f), C_AtomType, C_Empty)",
            ")"
        ));
        assert_eq!(outs, vec!["C_SymAtom(result_after_args)".to_string()]);
    }

    #[test]
    fn return_arg_tail_empty_bubbles_to_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_Empty),",
            "C_Space(C_ExprNil),",
            "C_KArgCons(C_SymAtom(a), C_Empty)",
            ")"
        ));
        assert_eq!(outs, vec!["C_Empty".to_string()]);
    }

    #[test]
    fn return_arg_head_recurse_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_SymAtom(a)),",
            "C_Space(C_ExprNil),",
            "C_KArgTail(",
            "C_SymAtom(orig),",
            "C_ExprCons(C_SymAtom(b), C_ExprNil),",
            "C_ExprCons(C_AtomType, C_ExprNil),",
            "C_Empty",
            ")",
            ")"
        ));
        assert_eq!(outs.len(), 1);
        assert!(
            outs[0].contains("C_SymAtom(a)")
                && outs[0].contains("C_SymAtom(b)")
                && outs[0].contains("C_ExprNil"),
            "expected argument recurse result, got: {outs:?}"
        );
    }

    #[test]
    fn return_tuple_cons_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_ExprCons(C_SymAtom(b), C_ExprNil)),",
            "C_Space(C_ExprNil),",
            "C_KTupleCons(C_SymAtom(a), C_Empty)",
            ")"
        ));
        assert_eq!(outs.len(), 1);
        assert!(
            outs[0].contains("C_SymAtom(a)")
                && outs[0].contains("C_SymAtom(b)")
                && outs[0].contains("C_ExprNil"),
            "expected tuple cons result, got: {outs:?}"
        );
    }

    #[test]
    fn return_tuple_head_error_bubbles_to_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_ErrorAtom(C_SymAtom(foo), C_BadType(C_GroundedType, C_SymbolType))),",
            "C_Space(C_ExprNil),",
            "C_KTupleTail(C_ExprNil, C_Empty)",
            ")"
        ));
        assert!(
            outs.iter()
                .any(|o| o.contains("C_ErrorAtom") && o.contains("C_BadType")),
            "expected bubbled tuple-head error, got: {outs:?}"
        );
    }

    #[test]
    fn return_tuple_head_recurse_reaches_done_on_mork() {
        let outs = run_case(concat!(
            "C_State(",
            "C_Return(C_SymAtom(a)),",
            "C_Space(",
            "C_ExprCons(",
            "C_TypeAnnotation(",
            "C_SymAtom(f),",
            "C_ArrowType(C_ExprCons(C_AtomType, C_ExprNil), C_AtomType)",
            "),",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
            "C_SymAtom(result_tuple_tail)",
            "),",
            "C_ExprNil)",
            ")",
            "),",
            "C_KTupleTail(",
            "C_ExprCons(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
            "C_ExprNil",
            "),",
            "C_Empty",
            ")",
            ")"
        ));
        assert_eq!(outs.len(), 1);
        assert!(
            outs[0].contains("C_SymAtom(a)")
                && outs[0].contains("C_SymAtom(result_tuple_tail)")
                && outs[0].contains("C_ExprNil"),
            "expected tuple recurse result, got: {outs:?}"
        );
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
