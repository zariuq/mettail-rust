#[cfg(feature = "mork-backend")]
mod imp_mork_smoke {
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

    fn run_mork_case(term: Box<dyn Term>) -> Vec<String> {
        mettail_runtime::clear_var_cache();
        let results = run_imp_mork_backend(term.as_ref()).expect("MORK execution should succeed");
        terminal_done_displays(&results)
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

    #[test]
    fn skip_reaches_done_on_mork() {
        let done_terms = run_mork_case(parse_constructor(
            "C_Start ( C_StmtAtomPromote ( C_Skip ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
        ));
        assert!(
            done_terms.iter().any(|d| {
                d.contains(
                    "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
                )
            }),
            "expected skip done term, got: {done_terms:?}"
        );
    }

    #[test]
    fn assignment_updates_store_on_mork() {
        let done_terms = run_mork_case(parse_constructor(
            "C_Start ( C_StmtAtomPromote ( C_Assign ( C_VarX , C_AExpMul ( C_AMulAtom ( C_ANat ( C_Succ ( C_Zero ) ) ) ) ) ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
        ));
        assert!(
            done_terms.iter().any(|d| {
                d.contains(
                    "C_ImpState(C_RetUnit , C_Store(C_Succ(C_Zero) , C_Zero , C_Zero) , C_KDone , C_Done)",
                )
            }),
            "expected assignment done term, got: {done_terms:?}"
        );
    }

    #[test]
    fn if_true_and_not_false_reaches_done_on_mork() {
        let done_terms = run_mork_case(build_if_true_and_not_false());
        assert!(
            done_terms.iter().any(|d| {
                d.contains(
                    "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
                )
            }),
            "expected if done term, got: {done_terms:?}"
        );
    }

    #[test]
    fn while_false_is_noop_on_mork() {
        let done_terms = run_mork_case(build_while_false_noop());
        assert!(
            done_terms.iter().any(|d| {
                d.contains(
                    "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
                )
            }),
            "expected while-false done term, got: {done_terms:?}"
        );
    }
}
