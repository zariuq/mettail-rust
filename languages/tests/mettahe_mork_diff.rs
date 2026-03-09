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

    fn all_displays(results: &AscentResults) -> Vec<String> {
        let mut displays: Vec<_> = results.all_terms.iter().map(|t| t.display.clone()).collect();
        displays.sort();
        displays
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
    fn parity_untyped_equation_defined_function_from_metta() {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let input = concat!(
            "C_State(",
            "C_Metta(",
            "C_ExprCons(C_SymAtom(id), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_UndefinedType",
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
        );
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        assert!(
            !mork.phase_timings_ms.contains_key("mork_fallback_ascent_ms"),
            "MORK backend must not fall back to Ascent for this untyped equation case\ninput: {input}\nphase timings: {:?}",
            mork.phase_timings_ms
        );
        let mork_outs = done_out_displays(&lang, &mork);
        assert_eq!(
            mork_outs,
            vec!["C_GInt(C_5)"],
            "MORK should reduce untyped equation-defined function calls even though Ascent still misses IE_NoType\ninput: {input}\nterms: {:?}\nrewrites: {:?}",
            all_displays(&mork),
            mork.rewrites
        );
    }

    #[test]
    fn mork_grounded_int_undefined_type_reaches_done() {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let input = concat!(
            "C_State(",
            "C_Metta(C_GInt(C_5), C_UndefinedType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        );
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        let mork_outs = done_out_displays(&lang, &mork);
        assert_eq!(
            mork_outs,
            vec!["C_GInt(C_5)"],
            "grounded int with UndefinedType should reach Done unchanged\ninput: {input}\nterms: {:?}\nrewrites: {:?}",
            all_displays(&mork),
            mork.rewrites
        );
    }

    #[test]
    fn mork_untyped_equation_defined_function_emits_reduced_intermediate() {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let input = concat!(
            "C_State(",
            "C_Metta(",
            "C_ExprCons(C_SymAtom(id), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_UndefinedType",
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
        );
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        let displays = all_displays(&mork);
        assert!(
            displays
                .iter()
                .any(|d| d.contains("C_Metta(C_GInt(C_5)") && d.contains("C_UndefinedType")),
            "untyped equation-defined function should emit reduced intermediate branch\ninput: {input}\nterms: {displays:?}\nrewrites: {:?}",
            mork.rewrites
        );
    }

    #[test]
    fn mork_surface_lowered_double_has_only_terminal_10() {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let input = concat!(
            "C_State(",
            "C_Metta(",
            "C_ExprCons(C_SymAtom(double), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_UndefinedType",
            "),",
            "C_Space(",
            "C_ExprCons(",
            "C_EqAtom(",
            "C_ExprCons(C_SymAtom(double), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
            "C_ExprCons(C_OpAdd, C_ExprCons(C_VarAtom(x), C_ExprCons(C_VarAtom(x), C_ExprNil)))",
            "),",
            "C_ExprCons(",
            "C_TypeAnnotation(C_OpAdd,C_ArrowType(C_GroundedType,C_GroundedType)),",
            "C_ExprNil",
            ")",
            ")",
            "),",
            "C_Empty",
            ")"
        );
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        let mork_outs = done_out_displays(&lang, &mork);
        assert_eq!(
            mork_outs,
            vec!["C_GInt(C_10)"],
            "surface-lowered double should end only at 10\ninput: {input}\nterms: {:?}\nrewrites: {:?}",
            all_displays(&mork),
            mork.rewrites
        );
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
        // MORK correctly defaults typeOf to UndefinedType (HE spec: Space.lean:107),
        // so bare symbols evaluate to themselves. Ascent lacks this evaluator fix,
        // so we test MORK correctness directly rather than ascent parity.
        let input = concat!(
            "C_State(",
            "C_Metta(C_SymAtom(foo), C_UndefinedType),",
            "C_Space(C_ExprNil),",
            "C_Empty",
            ")"
        );
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        let mork = run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed");
        let mork_outs = done_out_displays(&lang, &mork);
        assert_eq!(
            mork_outs,
            vec!["C_SymAtom(foo)"],
            "bare symbol should evaluate to itself in empty space\ninput: {input}\nmork: {mork_outs:?}"
        );
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
                "C_Metta(",
                "C_ExprCons(C_SymAtom(id), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
                "C_UndefinedType",
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

    // ═══ Minimal instruction tests (MORK template-driven) ═══════════════

    fn run_mork(input: &str) -> AscentResults {
        mettail_runtime::clear_var_cache();
        let lang = MeTTaHELanguage;
        let term = lang.parse_term(input).expect("parse should succeed");
        run_mettahe_mork_backend(term.as_ref()).expect("mork backend should succeed")
    }

    fn mork_all_displays(results: &AscentResults) -> Vec<String> {
        results.all_terms.iter().map(|t| t.display.clone()).collect()
    }

    fn mork_done_outs(input: &str) -> Vec<String> {
        let lang = MeTTaHELanguage;
        let results = run_mork(input);
        done_out_displays(&lang, &results)
    }

    #[test]
    fn mork_superpose_three_elements() {
        let results = run_mork(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(superpose), C_ExprCons(",
                  "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprCons(C_SymAtom(c), C_ExprNil))),",
                  "C_ExprNil",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        let displays = mork_all_displays(&results);
        let has_a = displays.iter().any(|d| d.contains("C_SymAtom(a)") && d.contains("C_Done"));
        let has_b = displays.iter().any(|d| d.contains("C_SymAtom(b)") && d.contains("C_Done"));
        let has_c = displays.iter().any(|d| d.contains("C_SymAtom(c)") && d.contains("C_Done"));
        assert!(
            has_a && has_b && has_c,
            "expected Done states for a, b, c from superpose, got: {displays:?}"
        );
    }

    #[test]
    fn mork_superpose_empty() {
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(superpose), C_ExprCons(C_ExprNil, C_ExprNil)),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        assert_eq!(outs, vec!["C_Empty"], "empty superpose should yield Empty, got: {outs:?}");
    }

    #[test]
    fn mork_match_single_hit() {
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(match), C_ExprCons(",
                  "C_SymAtom(symhex_2673656c66),",
                  "C_ExprCons(",
                    "C_ExprCons(C_SymAtom(color), C_ExprCons(C_VarAtom(v), C_ExprNil)),",
                    "C_ExprCons(C_VarAtom(v), C_ExprNil)",
                  ")",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(",
                "C_ExprCons(",
                  "C_ExprCons(C_SymAtom(color), C_ExprCons(C_SymAtom(red), C_ExprNil)),",
                  "C_ExprNil",
                ")",
              "),",
              "C_Empty",
            ")"
        ));
        assert!(
            outs.iter().any(|o| o.contains("C_SymAtom(red)")),
            "match should find (color red) and return red, got: {outs:?}"
        );
    }

    #[test]
    fn mork_match_no_hit() {
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(match), C_ExprCons(",
                  "C_SymAtom(symhex_2673656c66),",
                  "C_ExprCons(",
                    "C_ExprCons(C_SymAtom(foo), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                    "C_ExprCons(C_VarAtom(x), C_ExprNil)",
                  ")",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        assert_eq!(outs, vec!["C_Empty"], "match with no hits should yield Empty, got: {outs:?}");
    }

    #[test]
    fn mork_unify_success() {
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(unify), C_ExprCons(",
                  "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
                  "C_ExprCons(",
                    "C_ExprCons(C_SymAtom(a), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                    "C_ExprCons(C_VarAtom(x),",
                      "C_ExprCons(C_SymAtom(nope), C_ExprNil)",
                    ")",
                  ")",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        assert!(
            outs.iter().any(|o| o.contains("C_SymAtom(b)")),
            "unify should match (a b) against (a $x) and return b, got: {outs:?}"
        );
    }

    #[test]
    fn mork_unify_failure() {
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(unify), C_ExprCons(",
                  "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
                  "C_ExprCons(",
                    "C_ExprCons(C_SymAtom(c), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                    "C_ExprCons(C_SymAtom(yes),",
                      "C_ExprCons(C_SymAtom(nope), C_ExprNil)",
                    ")",
                  ")",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        assert!(
            outs.iter().any(|o| o.contains("C_SymAtom(nope)")),
            "unify with pattern mismatch should return failure branch, got: {outs:?}"
        );
    }

    #[test]
    fn mork_collapse_basic() {
        // (collapse hello) with AtomType → nested eval of (hello, AtomType)
        // hello is a symbol with AtomType → R2 fires → Return(hello) → Done
        // collapse collects [hello], packs as list, then outer Metta evaluates it
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(collapse), C_ExprCons(",
                  "C_SymAtom(hello),",
                  "C_ExprNil",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        // Nested eval of (hello, AtomType) → Done(hello)
        // Packed as (hello), then outer evaluation proceeds
        assert!(
            !outs.is_empty(),
            "collapse basic should produce Done result, got: {outs:?}"
        );
        // The packed list (hello) = ExprCons(SymAtom(hello), ExprNil)
        // should appear somewhere in the output
        assert!(
            outs.iter().any(|d| d.contains("hello")),
            "collapse result should contain 'hello', got: {outs:?}"
        );
    }

    #[test]
    fn mork_collapse_superpose() {
        // (collapse (superpose (a b c))) → should collect [a, b, c] as a list
        // Nested eval: superpose branches into 3 states, each reaches Done
        // collapse packs all 3 results
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(collapse), C_ExprCons(",
                  "C_ExprCons(C_SymAtom(superpose), C_ExprCons(",
                    "C_ExprCons(C_SymAtom(a), C_ExprCons(C_SymAtom(b), C_ExprCons(C_SymAtom(c), C_ExprNil))),",
                    "C_ExprNil",
                  ")),",
                  "C_ExprNil",
                ")),",
                "C_AtomType",
              "),",
              "C_Space(C_ExprNil),",
              "C_Empty",
            ")"
        ));
        // Should have a result containing all three elements
        assert!(
            !outs.is_empty(),
            "collapse of superpose should produce Done result, got: {outs:?}"
        );
        let all_output = outs.join(" ");
        assert!(
            all_output.contains("C_SymAtom(a)") && all_output.contains("C_SymAtom(b)") && all_output.contains("C_SymAtom(c)"),
            "collapse should collect all 3 superpose branches, got: {outs:?}"
        );
    }

    #[test]
    fn mork_collapse_equation_nondet() {
        // (collapse (f a)) with space containing two equations for (f a)
        // and a type annotation for f → both equation results collected
        let outs = mork_done_outs(concat!(
            "C_State(",
              "C_MettaCall(",
                "C_ExprCons(C_SymAtom(collapse), C_ExprCons(",
                  "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
                  "C_ExprNil",
                ")),",
                "C_UndefinedType",
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
                    "C_ExprCons(",
                      "C_TypeAnnotation(",
                        "C_SymAtom(f),",
                        "C_ArrowType(C_ExprCons(C_SymbolType, C_ExprNil), C_SymbolType)",
                      "),",
                      "C_ExprNil",
                    ")",
                  ")",
                ")",
              "),",
              "C_Empty",
            ")"
        ));
        assert!(
            !outs.is_empty(),
            "collapse of nondeterministic equation should produce results, got: {outs:?}"
        );
        let all_output = outs.join(" ");
        assert!(
            all_output.contains("result1") && all_output.contains("result2"),
            "collapse should collect both equation match results, got: {outs:?}"
        );
    }
}
