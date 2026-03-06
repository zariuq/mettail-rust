#[cfg(feature = "mork-backend")]
mod mettahe_mork_diff {
    use std::collections::BTreeSet;

    use mettail_languages::mettahe_from_lean::{
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

    fn assert_backend_parity(input: &str) {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let term = lang.parse_term(input).expect("parse should succeed");

        let ascent = lang
            .run_ascent(term.as_ref())
            .expect("ascent backend should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        assert!(
            !mork.phase_timings_ms.contains_key("mork_fallback_ascent_ms"),
            "MORK backend must not fall back to Ascent for this parity case\ninput: {input}\nphase timings: {:?}",
            mork.phase_timings_ms
        );

        let ascent_outs = done_out_displays(&lang, &ascent);
        let mork_outs = done_out_displays(&lang, &mork);
        assert_eq!(
            ascent_outs, mork_outs,
            "backend output mismatch\ninput: {input}\nascent: {ascent_outs:?}\nmork: {mork_outs:?}"
        );
    }

    fn collect_emitted_rule_ids(input: &str, out: &mut BTreeSet<String>) {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        for rw in &mork.rewrites {
            if let Some(rule) = &rw.rule_name {
                out.insert(rule.clone());
            }
        }
    }

    #[test]
    fn parity_single_equation_match() {
        assert_backend_parity(concat!(
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
    }

    #[test]
    fn parity_nondeterministic_two_equations() {
        assert_backend_parity(concat!(
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
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_SymAtom(result2)",
            "),",
            "C_ExprNil",
            ")",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_type_atom_literal() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_MettaCall(C_AtomType,C_AtomType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_error_atom_literal() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_MettaCall(C_ErrorAtom(C_SymAtom(src),C_NoReturn),C_AtomType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_grounded_call_shape_literal() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_OpAdd,C_ExprCons(C_GInt(C_2),C_ExprCons(C_GInt(C_3),C_ExprNil))),",
            "C_AtomType",
            "),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_variable_pattern_equation() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_SymAtom(id), C_ExprCons(C_SymAtom(alpha), C_ExprNil)),",
            "C_AtomType",
            "),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(id), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
            "C_VarAtom(x)",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_no_equation_match_fallback() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_MettaCall(",
            "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
            "C_AtomType",
            "),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(g), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
            "C_SymAtom(result1)",
            "),",
            "C_ExprNil",
            ")",
            "),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_return_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_Return(C_SymAtom(done_value)),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_metta_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_Metta(C_SymAtom(foo), C_UndefinedType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_interpexpr_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_InterpExpr(C_SymAtom(foo), C_UndefinedType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_interpfunc_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_InterpFunc(C_SymAtom(foo), C_AtomType, C_AtomType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_interptuple_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_InterpTuple(C_ExprNil),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_typecast_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_TypeCast(C_SymAtom(f), C_AtomType),",
            "C_Space(C_ExprCons(C_TypeAnnotation(C_SymAtom(f), C_AtomType), C_ExprNil)),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn parity_interpargs_entry_state_native_path() {
        assert_backend_parity(concat!(
            "C_State(",
            "C_InterpArgs(C_SymAtom(a), C_ExprNil, C_ExprCons(C_AtomType, C_ExprNil)),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        ));
    }

    #[test]
    fn corpus_emitted_rules_are_declared_in_he_transition_artifact() {
        let mut emitted = BTreeSet::new();
        collect_emitted_rule_ids(
            concat!(
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
                "C_ExprCons(",
                "C_EqAtom(",
                "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
                "C_SymAtom(result2)",
                "),",
                "C_ExprNil",
                ")",
                ")",
                "),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );
        collect_emitted_rule_ids(
            concat!(
                "C_State(",
                "C_Metta(C_SymAtom(foo), C_UndefinedType),",
                "C_Space(C_ExprNil),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );
        collect_emitted_rule_ids(
            concat!(
                "C_State(",
                "C_TypeCast(C_SymAtom(f), C_AtomType),",
                "C_Space(C_ExprCons(C_TypeAnnotation(C_SymAtom(f), C_AtomType), C_ExprNil)),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );
        collect_emitted_rule_ids(
            concat!(
                "C_State(",
                "C_InterpTuple(C_ExprCons(C_SymAtom(x), C_ExprNil)),",
                "C_Space(C_ExprNil),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );
        collect_emitted_rule_ids(
            concat!(
                "C_State(",
                "C_InterpArgs(C_SymAtom(a), C_ExprNil, C_ExprCons(C_AtomType, C_ExprNil)),",
                "C_Space(C_ExprNil),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );
        collect_emitted_rule_ids(
            concat!(
                "C_State(",
                "C_Return(C_SymAtom(done_value)),",
                "C_Space(C_ExprNil),",
                "C_Empty",
                ")"
            ),
            &mut emitted,
        );

        let declared: BTreeSet<String> = he_transition_artifact_rule_ids()
            .expect("HE transition artifact should load")
            .into_iter()
            .collect();
        for rule in emitted {
            assert!(
                declared.contains(&rule),
                "HE MORK emitted rule '{}' that is not declared by transition artifact",
                rule
            );
        }
    }
}
