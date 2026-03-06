use codex_imp_harness::imp_from_lean::{
    run_imp_mork_backend, BAtom, BConj, BExp, BNeg, IMPLanguage, IMPTerm, IMPTermInner, Nat, State,
    Stmt, StmtAtom, Store,
};
use mettail_runtime::{Language, Term};

struct Case {
    name: &'static str,
    input: CaseInput,
    expected_done_fragment: &'static str,
}

enum CaseInput {
    Parse(&'static str),
    Build(fn() -> Box<dyn Term>),
}

const CASES: &[Case] = &[
    Case {
        name: "skip",
        input: CaseInput::Parse(
            "C_Start ( C_StmtAtomPromote ( C_Skip ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
        ),
        expected_done_fragment: "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
    },
    Case {
        name: "assign_x_one",
        input: CaseInput::Parse(
            "C_Start ( C_StmtAtomPromote ( C_Assign ( C_VarX , C_AExpMul ( C_AMulAtom ( C_ANat ( C_Succ ( C_Zero ) ) ) ) ) ) , C_Store ( C_Zero , C_Zero , C_Zero ) )",
        ),
        expected_done_fragment: "C_ImpState(C_RetUnit , C_Store(C_Succ(C_Zero) , C_Zero , C_Zero) , C_KDone , C_Done)",
    },
    Case {
        name: "if_true_and_not_false",
        input: CaseInput::Build(build_if_true_and_not_false),
        expected_done_fragment: "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
    },
    Case {
        name: "while_false_noop",
        input: CaseInput::Build(build_while_false_noop),
        expected_done_fragment: "C_ImpState(C_RetUnit , C_Store(C_Zero , C_Zero , C_Zero) , C_KDone , C_Done)",
    },
];

fn main() {
    let mut failed = false;
    for case in CASES {
        match run_case(case) {
            Ok(done) => {
                println!("PASS {} -> {}", case.name, done);
            },
            Err(err) => {
                eprintln!("FAIL {} -> {}", case.name, err);
                failed = true;
            },
        }
    }

    if failed {
        std::process::exit(1);
    }
}

fn run_case(case: &Case) -> Result<String, String> {
    mettail_runtime::clear_var_cache();
    let lang = IMPLanguage;
    let term = match case.input {
        CaseInput::Parse(input) => lang
            .parse_term(input)
            .map_err(|e| format!("parse failed: {e}"))?,
        CaseInput::Build(build) => build(),
    };
    let results = run_imp_mork_backend(term.as_ref())
        .map_err(|e| format!("mork execution failed: {e}"))?;

    let mut done_terms = results
        .all_terms
        .iter()
        .filter(|t| t.display.contains("C_Done"))
        .map(|t| t.display.clone())
        .collect::<Vec<_>>();
    done_terms.sort();
    done_terms.dedup();

    if let Some(done) = done_terms
        .iter()
        .find(|t| t.contains(case.expected_done_fragment))
    {
        return Ok(done.clone());
    }

    Err(format!(
        "expected done fragment not found\nexpected: {}\nactual done terms: {:?}",
        case.expected_done_fragment, done_terms
    ))
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
