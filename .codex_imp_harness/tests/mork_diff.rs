#[cfg(feature = "mork-backend")]
mod imp_mork_contracts {
    use std::collections::BTreeSet;

    use codex_imp_harness::imp_artifacts::{imp_artifact_dir, load_imp_transition_artifact};
    use codex_imp_harness::imp_from_lean::{
        run_imp_mork_backend, BAtom, BConj, BExp, BNeg, IMPLanguage, IMPTerm, IMPTermInner, Nat,
        State, Stmt, StmtAtom, Store,
    };
    use mettail_runtime::{AscentResults, Language, Term};

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

    fn parse_constructor(input: &str) -> Box<dyn Term> {
        let lang = IMPLanguage;
        lang.parse_term(input)
            .expect("constructor-form parse should succeed")
    }

    fn zero() -> Box<Nat> {
        Box::new(Nat::C_Zero)
    }

    fn store_xyz(x: Box<Nat>, y: Box<Nat>, z: Box<Nat>) -> Box<Store> {
        Box::new(Store::C_Store(x, y, z))
    }

    fn stmt_skip() -> Box<Stmt> {
        Box::new(Stmt::C_StmtAtomPromote(Box::new(StmtAtom::C_Skip)))
    }

    fn build_if_true_and_not_false() -> Box<dyn Term> {
        let cond = Box::new(BExp::C_BExpConj(Box::new(BConj::C_BAnd(
            Box::new(BConj::C_BConjNeg(Box::new(BNeg::C_BNot(Box::new(
                BNeg::C_BNegAtom(Box::new(BAtom::C_BFalseAtom)),
            ))))),
            Box::new(BNeg::C_BNegAtom(Box::new(BAtom::C_BTrueAtom))),
        ))));
        Box::new(IMPTerm(IMPTermInner::State(State::C_Start(
            Box::new(Stmt::C_StmtAtomPromote(Box::new(StmtAtom::C_If(
                cond,
                stmt_skip(),
                stmt_skip(),
            )))),
            store_xyz(zero(), zero(), zero()),
        ))))
    }

    fn build_while_false_noop() -> Box<dyn Term> {
        let cond = Box::new(BExp::C_BExpConj(Box::new(BConj::C_BConjNeg(Box::new(
            BNeg::C_BNegAtom(Box::new(BAtom::C_BFalseAtom)),
        )))));
        Box::new(IMPTerm(IMPTermInner::State(State::C_Start(
            Box::new(Stmt::C_StmtAtomPromote(Box::new(StmtAtom::C_While(
                cond,
                stmt_skip(),
            )))),
            store_xyz(zero(), zero(), zero()),
        ))))
    }

    fn run_mork(term: Box<dyn Term>) -> AscentResults {
        mettail_runtime::clear_var_cache();
        run_imp_mork_backend(term.as_ref()).expect("mork backend should succeed")
    }

    fn collect_mork_rule_coverage(term: Box<dyn Term>, covered: &mut BTreeSet<String>) {
        let mork = run_mork(term);
        for rw in &mork.rewrites {
            if let Some(rule) = &rw.rule_name {
                covered.insert(rule.clone());
            }
        }
    }

    #[test]
    fn mork_constructor_cases_produce_done_states() {
        let cases = [
            parse_constructor(
                "C_Start ( C_StmtAtomPromote ( C_Skip ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
            ),
            parse_constructor(
                "C_Start ( C_StmtAtomPromote ( C_Assign ( C_VarX , C_AExpMul ( C_AMulAtom ( C_ANat ( C_Succ ( C_Zero ) ) ) ) ) ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
            ),
            build_if_true_and_not_false(),
            build_while_false_noop(),
        ];
        for case in cases {
            let done = terminal_done_displays(&run_mork(case));
            assert!(
                !done.is_empty(),
                "expected at least one done state from MORK execution"
            );
        }
    }

    #[test]
    fn corpus_transition_rule_coverage_hits_key_imp_rules() {
        let mut covered = BTreeSet::new();
        collect_mork_rule_coverage(
            parse_constructor(
                "C_Start ( C_StmtAtomPromote ( C_Skip ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
            ),
            &mut covered,
        );
        collect_mork_rule_coverage(
            parse_constructor(
                "C_Start ( C_StmtAtomPromote ( C_Assign ( C_VarX , C_AExpPlus ( C_AExpMul ( C_AMulAtom ( C_ANat ( C_Succ ( C_Zero ) ) ) ) , C_AMulAtom ( C_ANat ( C_Succ ( C_Zero ) ) ) ) ) ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
            ),
            &mut covered,
        );
        collect_mork_rule_coverage(build_if_true_and_not_false(), &mut covered);
        collect_mork_rule_coverage(build_while_false_noop(), &mut covered);

        let transition = load_imp_transition_artifact(&imp_artifact_dir())
            .expect("IMP transition artifact should load");
        for required in [
            "C_Start",
            "C_RunStmt",
            "C_RunA",
            "C_RunB",
            "C_RetNat",
            "C_RetBool",
            "C_RetUnit",
        ] {
            assert!(
                transition.sources.iter().any(|s| s.source_instr == required),
                "required source instruction '{}' missing from IMP transition artifact",
                required
            );
        }
        assert!(covered.contains("R0"));
        assert!(covered.contains("R2"));
        assert!(covered.contains("R4"));
        assert!(covered.contains("R5"));
        assert!(covered.contains("R10"));
        assert!(covered.contains("R19"));
        assert!(covered.contains("R25"));
        assert!(covered.contains("R36"));
    }
}
