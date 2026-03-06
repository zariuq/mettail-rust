#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

include!("generated/imp_language_working.rs");

#[cfg(feature = "mork-backend")]
use crate::imp_artifacts::{
    imp_artifact_dir, load_imp_lookup_artifact, load_imp_rewrite_ir_artifact,
    load_imp_transition_artifact,
};
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, NativeTransitionContract, NativeTransitionRuleMeta,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{
    dispatch_ordered_rules, run_transition_graph, AscentResults, MorkExecutionLimits, Term,
};
#[cfg(feature = "mork-backend")]
use std::sync::OnceLock;
#[cfg(feature = "mork-backend")]
use std::time::Instant;

#[cfg(feature = "mork-backend")]
fn imp_rewrite_contract() -> Result<&'static NativeTransitionContract, String> {
    static CONTRACT: OnceLock<Result<NativeTransitionContract, String>> = OnceLock::new();
    match CONTRACT.get_or_init(|| {
        let dir = imp_artifact_dir();
        let transition = load_imp_transition_artifact(&dir)?;
        let lookup = load_imp_lookup_artifact(&dir)?;
        let rewrite_ir = load_imp_rewrite_ir_artifact(&dir)?;
        build_native_transition_contract("IMP", transition, lookup, rewrite_ir, |lookup| {
            let family = lookup
                .families
                .iter()
                .find(|f| f.family == "storeGet")
                .ok_or_else(|| "IMP lookup-plan must expose storeGet family".to_string())?;
            if family.query_arity != 2 || family.payload_arity != 1 {
                return Err(format!(
                    "IMP storeGet family arity mismatch: query_arity={}, payload_arity={} (expected 2/1)",
                    family.query_arity, family.payload_arity
                ));
            }
            if !family.contracts.exact_result || !family.contracts.no_false_negatives {
                return Err("IMP storeGet family must be exact and no-false-negatives".to_string());
            }
            Ok(())
        })
    }) {
        Ok(contract) => Ok(contract),
        Err(err) => Err(err.clone()),
    }
}

#[cfg(feature = "mork-backend")]
fn running_status() -> Box<Status> {
    Box::new(Status::C_Running)
}

#[cfg(feature = "mork-backend")]
fn done_status() -> Box<Status> {
    Box::new(Status::C_Done)
}

#[cfg(feature = "mork-backend")]
fn true_bool() -> Box<Bool> {
    Box::new(Bool::C_BoolTrue)
}

#[cfg(feature = "mork-backend")]
fn false_bool() -> Box<Bool> {
    Box::new(Bool::C_BoolFalse)
}

#[cfg(feature = "mork-backend")]
fn mk_state(control: Control, store: Box<Store>, kont: Box<Kont>, status: Box<Status>) -> State {
    State::C_ImpState(Box::new(control), store, kont, status)
}

#[cfg(feature = "mork-backend")]
fn promote_stmt_atom(atom: &StmtAtom) -> Box<Stmt> {
    Box::new(Stmt::C_StmtAtomPromote(Box::new(atom.clone())))
}

#[cfg(feature = "mork-backend")]
fn nat_add(lhs: &Nat, rhs: &Nat) -> Option<Box<Nat>> {
    match lhs {
        Nat::C_Zero => Some(Box::new(rhs.clone())),
        Nat::C_Succ(prev) => nat_add(prev.as_ref(), rhs).map(|sum| Box::new(Nat::C_Succ(sum))),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn nat_mul(lhs: &Nat, rhs: &Nat) -> Option<Box<Nat>> {
    match lhs {
        Nat::C_Zero => Some(Box::new(Nat::C_Zero)),
        Nat::C_Succ(prev) => {
            let partial = nat_mul(prev.as_ref(), rhs)?;
            nat_add(rhs, partial.as_ref())
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn nat_le(lhs: &Nat, rhs: &Nat) -> Option<Box<Bool>> {
    match (lhs, rhs) {
        (Nat::C_Zero, Nat::C_Zero | Nat::C_Succ(_)) => Some(true_bool()),
        (Nat::C_Succ(_), Nat::C_Zero) => Some(false_bool()),
        (Nat::C_Succ(a), Nat::C_Succ(b)) => nat_le(a.as_ref(), b.as_ref()),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn nat_eq(lhs: &Nat, rhs: &Nat) -> Option<Box<Bool>> {
    match (lhs, rhs) {
        (Nat::C_Zero, Nat::C_Zero) => Some(true_bool()),
        (Nat::C_Zero, Nat::C_Succ(_)) | (Nat::C_Succ(_), Nat::C_Zero) => Some(false_bool()),
        (Nat::C_Succ(a), Nat::C_Succ(b)) => nat_eq(a.as_ref(), b.as_ref()),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn store_get(store: &Store, var: &ImpVar) -> Option<Box<Nat>> {
    match (store, var) {
        (Store::C_Store(x, _, _), ImpVar::C_VarX) => Some(x.clone()),
        (Store::C_Store(_, y, _), ImpVar::C_VarY) => Some(y.clone()),
        (Store::C_Store(_, _, z), ImpVar::C_VarZ) => Some(z.clone()),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn store_set(store: &Store, var: &ImpVar, value: &Nat) -> Option<Box<Store>> {
    match (store, var) {
        (Store::C_Store(_, y, z), ImpVar::C_VarX) => Some(Box::new(Store::C_Store(
            Box::new(value.clone()),
            y.clone(),
            z.clone(),
        ))),
        (Store::C_Store(x, _, z), ImpVar::C_VarY) => Some(Box::new(Store::C_Store(
            x.clone(),
            Box::new(value.clone()),
            z.clone(),
        ))),
        (Store::C_Store(x, y, _), ImpVar::C_VarZ) => Some(Box::new(Store::C_Store(
            x.clone(),
            y.clone(),
            Box::new(value.clone()),
        ))),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn expect_contract(
    meta: &NativeTransitionRuleMeta,
    transition_kind: &str,
    guard_family: &str,
    effect_kind: &str,
) -> Result<(), String> {
    if meta.transition_kind != transition_kind
        || meta.guard_family != guard_family
        || meta.effect_kind != effect_kind
    {
        return Err(format!(
            "IMP contract mismatch for rule '{}' (logical id '{}'): expected kind='{}' guard='{}' effect='{}', got kind='{}' guard='{}' effect='{}'",
            meta.rule_id,
            meta.logical_transition_id,
            transition_kind,
            guard_family,
            effect_kind,
            meta.transition_kind,
            meta.guard_family,
            meta.effect_kind,
        ));
    }
    Ok(())
}

#[cfg(feature = "mork-backend")]
fn imp_apply_rule(meta: &NativeTransitionRuleMeta, state: &State) -> Result<Vec<State>, String> {
    let next = match meta.rule_name.as_str() {
        "R_Start" => {
            expect_contract(meta, "enter", "shape", "advance_state")?;
            match state {
                State::C_Start(stmt, store) => Some(mk_state(
                    Control::C_RunStmt(stmt.clone()),
                    store.clone(),
                    Box::new(Kont::C_KDone),
                    running_status(),
                )),
                _ => None,
            }
        },
        "R_Skip" => {
            expect_contract(meta, "transition", "shape", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunStmt(stmt) => match stmt.as_ref() {
                        Stmt::C_StmtAtomPromote(atom) if matches!(atom.as_ref(), StmtAtom::C_Skip) => Some(mk_state(
                            Control::C_RetUnit,
                            store.clone(),
                            k.clone(),
                            running_status(),
                        )),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_Assign" => {
            expect_contract(meta, "assign", "shape", "store_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunStmt(stmt) => match stmt.as_ref() {
                        Stmt::C_StmtAtomPromote(atom) => match atom.as_ref() {
                            StmtAtom::C_Assign(x, e) => Some(mk_state(
                                Control::C_RunA(e.clone()),
                                store.clone(),
                                Box::new(Kont::C_KAssign(x.clone(), k.clone())),
                                running_status(),
                            )),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_Seq" => {
            expect_contract(meta, "sequence", "shape", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunStmt(stmt) => match stmt.as_ref() {
                        Stmt::C_Seq(s1, s2) => Some(mk_state(
                            Control::C_RunStmt(s1.clone()),
                            store.clone(),
                            Box::new(Kont::C_KSeq(promote_stmt_atom(s2.as_ref()), k.clone())),
                            running_status(),
                        )),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_If" => {
            expect_contract(meta, "branch", "shape", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunStmt(stmt) => match stmt.as_ref() {
                        Stmt::C_StmtAtomPromote(atom) => match atom.as_ref() {
                            StmtAtom::C_If(b, t, f) => Some(mk_state(
                                Control::C_RunB(b.clone()),
                                store.clone(),
                                Box::new(Kont::C_KIf(t.clone(), f.clone(), k.clone())),
                                running_status(),
                            )),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_While" => {
            expect_contract(meta, "while", "shape", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunStmt(stmt) => match stmt.as_ref() {
                        Stmt::C_StmtAtomPromote(atom) => match atom.as_ref() {
                            StmtAtom::C_While(b, body) => Some(mk_state(
                                Control::C_RunB(b.clone()),
                                store.clone(),
                                Box::new(Kont::C_KWhile(b.clone(), body.clone(), k.clone())),
                                running_status(),
                            )),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_ANat" => {
            expect_contract(meta, "arith", "shape", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunA(expr) => match expr.as_ref() {
                        AExp::C_AExpMul(m) => match m.as_ref() {
                            AMul::C_AMulAtom(atom) => match atom.as_ref() {
                                AAtom::C_ANat(n) => Some(mk_state(
                                    Control::C_RetNat(n.clone()),
                                    store.clone(),
                                    k.clone(),
                                    running_status(),
                                )),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_AVar" => {
            expect_contract(meta, "arith", "lookup", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunA(expr) => match expr.as_ref() {
                        AExp::C_AExpMul(m) => match m.as_ref() {
                            AMul::C_AMulAtom(atom) => match atom.as_ref() {
                                AAtom::C_AVar(x) => store_get(store.as_ref(), x.as_ref()).map(|n| {
                                    mk_state(
                                        Control::C_RetNat(n),
                                        store.clone(),
                                        k.clone(),
                                        running_status(),
                                    )
                                }),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_AParen" => {
            expect_contract(meta, "arith", "shape", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunA(expr) => match expr.as_ref() {
                        AExp::C_AExpMul(m) => match m.as_ref() {
                            AMul::C_AMulAtom(atom) => match atom.as_ref() {
                                AAtom::C_AParen(e) => Some(mk_state(
                                    Control::C_RunA(e.clone()),
                                    store.clone(),
                                    k.clone(),
                                    running_status(),
                                )),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_AMul" => {
            expect_contract(meta, "arith", "shape", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunA(expr) => match expr.as_ref() {
                        AExp::C_AExpMul(m) => match m.as_ref() {
                            AMul::C_AMulTimes(lhs, rhs) => Some(mk_state(
                                Control::C_RunA(Box::new(AExp::C_AExpMul(lhs.clone()))),
                                store.clone(),
                                Box::new(Kont::C_KTimesL(rhs.clone(), k.clone())),
                                running_status(),
                            )),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_APlus" => {
            expect_contract(meta, "arith_plus", "shape", "arith_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunA(expr) => match expr.as_ref() {
                        AExp::C_AExpPlus(lhs, rhs) => Some(mk_state(
                            Control::C_RunA(lhs.clone()),
                            store.clone(),
                            Box::new(Kont::C_KPlusL(rhs.clone(), k.clone())),
                            running_status(),
                        )),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BTrue" => {
            expect_contract(meta, "bool", "bool_true", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNegAtom(atom) if matches!(atom.as_ref(), BAtom::C_BTrueAtom) => Some(mk_state(
                                    Control::C_RetBool(true_bool()),
                                    store.clone(),
                                    k.clone(),
                                    running_status(),
                                )),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BFalse" => {
            expect_contract(meta, "bool", "bool_false", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNegAtom(atom) if matches!(atom.as_ref(), BAtom::C_BFalseAtom) => Some(mk_state(
                                    Control::C_RetBool(false_bool()),
                                    store.clone(),
                                    k.clone(),
                                    running_status(),
                                )),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BParen" => {
            expect_contract(meta, "bool", "shape", "advance_state")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNegAtom(atom) => match atom.as_ref() {
                                    BAtom::C_BParen(b) => Some(mk_state(
                                        Control::C_RunB(b.clone()),
                                        store.clone(),
                                        k.clone(),
                                        running_status(),
                                    )),
                                    _ => None,
                                },
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BLe" => {
            expect_contract(meta, "bool_le", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNegAtom(atom) => match atom.as_ref() {
                                    BAtom::C_BLe(lhs, rhs) => Some(mk_state(
                                        Control::C_RunA(lhs.clone()),
                                        store.clone(),
                                        Box::new(Kont::C_KLeL(rhs.clone(), k.clone())),
                                        running_status(),
                                    )),
                                    _ => None,
                                },
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BEq" => {
            expect_contract(meta, "bool_eq", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNegAtom(atom) => match atom.as_ref() {
                                    BAtom::C_BEq(lhs, rhs) => Some(mk_state(
                                        Control::C_RunA(lhs.clone()),
                                        store.clone(),
                                        Box::new(Kont::C_KEqL(rhs.clone(), k.clone())),
                                        running_status(),
                                    )),
                                    _ => None,
                                },
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BNot" => {
            expect_contract(meta, "bool_not", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BConjNeg(neg) => match neg.as_ref() {
                                BNeg::C_BNot(b) => Some(mk_state(
                                    Control::C_RunB(Box::new(BExp::C_BExpConj(Box::new(BConj::C_BConjNeg(b.clone()))))),
                                    store.clone(),
                                    Box::new(Kont::C_KNot(k.clone())),
                                    running_status(),
                                )),
                                _ => None,
                            },
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_BAnd" => {
            expect_contract(meta, "bool_and", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, k, _) => match ctrl.as_ref() {
                    Control::C_RunB(expr) => match expr.as_ref() {
                        BExp::C_BExpConj(conj) => match conj.as_ref() {
                            BConj::C_BAnd(lhs, rhs) => Some(mk_state(
                                Control::C_RunB(Box::new(BExp::C_BExpConj(lhs.clone()))),
                                store.clone(),
                                Box::new(Kont::C_KAndL(rhs.clone(), k.clone())),
                                running_status(),
                            )),
                            _ => None,
                        },
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KSeq" => {
            expect_contract(meta, "sequence", "shape", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetUnit, Kont::C_KSeq(stmt, k)) => Some(mk_state(
                        Control::C_RunStmt(stmt.clone()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KAssign" => {
            expect_contract(meta, "assign", "lookup", "store_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(n), Kont::C_KAssign(x, k)) => {
                        store_set(store.as_ref(), x.as_ref(), n.as_ref()).map(|store2| {
                            mk_state(Control::C_RetUnit, store2, k.clone(), running_status())
                        })
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KIf_True" => {
            expect_contract(meta, "branch", "bool_true", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KIf(t, _, k)) if matches!(b.as_ref(), Bool::C_BoolTrue) => Some(mk_state(
                        Control::C_RunStmt(t.clone()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KIf_False" => {
            expect_contract(meta, "branch", "bool_false", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KIf(_, f, k)) if matches!(b.as_ref(), Bool::C_BoolFalse) => Some(mk_state(
                        Control::C_RunStmt(f.clone()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KWhile_True" => {
            expect_contract(meta, "while", "bool_true", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KWhile(cond, body, k)) if matches!(b.as_ref(), Bool::C_BoolTrue) => {
                        let loop_stmt = promote_stmt_atom(&StmtAtom::C_While(cond.clone(), body.clone()));
                        Some(mk_state(
                            Control::C_RunStmt(body.clone()),
                            store.clone(),
                            Box::new(Kont::C_KSeq(loop_stmt, k.clone())),
                            running_status(),
                        ))
                    },
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KWhile_False" => {
            expect_contract(meta, "while", "bool_false", "kont_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KWhile(_, _, k)) if matches!(b.as_ref(), Bool::C_BoolFalse) => Some(mk_state(
                        Control::C_RetUnit,
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KPlus_L" => {
            expect_contract(meta, "arith_plus", "shape", "arith_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(n), Kont::C_KPlusL(rhs, k)) => Some(mk_state(
                        Control::C_RunA(Box::new(AExp::C_AExpMul(rhs.clone()))),
                        store.clone(),
                        Box::new(Kont::C_KPlusR(n.clone(), k.clone())),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KPlus_R" => {
            expect_contract(meta, "arith_plus", "lookup", "arith_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(rhs), Kont::C_KPlusR(lhs, k)) => nat_add(lhs.as_ref(), rhs.as_ref()).map(|sum| {
                        mk_state(Control::C_RetNat(sum), store.clone(), k.clone(), running_status())
                    }),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KTimes_L" => {
            expect_contract(meta, "arith_times", "shape", "arith_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(n), Kont::C_KTimesL(rhs, k)) => Some(mk_state(
                        Control::C_RunA(Box::new(AExp::C_AExpMul(Box::new(AMul::C_AMulAtom(rhs.clone()))))),
                        store.clone(),
                        Box::new(Kont::C_KTimesR(n.clone(), k.clone())),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KTimes_R" => {
            expect_contract(meta, "arith_times", "lookup", "arith_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(rhs), Kont::C_KTimesR(lhs, k)) => nat_mul(lhs.as_ref(), rhs.as_ref()).map(|prod| {
                        mk_state(Control::C_RetNat(prod), store.clone(), k.clone(), running_status())
                    }),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KLe_L" => {
            expect_contract(meta, "bool_le", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(lhs), Kont::C_KLeL(rhs, k)) => Some(mk_state(
                        Control::C_RunA(rhs.clone()),
                        store.clone(),
                        Box::new(Kont::C_KLeR(lhs.clone(), k.clone())),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KLe_R" => {
            expect_contract(meta, "bool_le", "lookup", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(rhs), Kont::C_KLeR(lhs, k)) => nat_le(lhs.as_ref(), rhs.as_ref()).map(|out| {
                        mk_state(Control::C_RetBool(out), store.clone(), k.clone(), running_status())
                    }),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KEq_L" => {
            expect_contract(meta, "bool_eq", "shape", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(lhs), Kont::C_KEqL(rhs, k)) => Some(mk_state(
                        Control::C_RunA(rhs.clone()),
                        store.clone(),
                        Box::new(Kont::C_KEqR(lhs.clone(), k.clone())),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KEq_R" => {
            expect_contract(meta, "bool_eq", "lookup", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetNat(rhs), Kont::C_KEqR(lhs, k)) => nat_eq(lhs.as_ref(), rhs.as_ref()).map(|out| {
                        mk_state(Control::C_RetBool(out), store.clone(), k.clone(), running_status())
                    }),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KNot_True" => {
            expect_contract(meta, "bool_not", "bool_true", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KNot(k)) if matches!(b.as_ref(), Bool::C_BoolTrue) => Some(mk_state(
                        Control::C_RetBool(false_bool()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KNot_False" => {
            expect_contract(meta, "bool_not", "bool_false", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KNot(k)) if matches!(b.as_ref(), Bool::C_BoolFalse) => Some(mk_state(
                        Control::C_RetBool(true_bool()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KAnd_True" => {
            expect_contract(meta, "bool_and", "bool_true", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KAndL(rhs, k)) if matches!(b.as_ref(), Bool::C_BoolTrue) => Some(mk_state(
                        Control::C_RunB(Box::new(BExp::C_BExpConj(Box::new(BConj::C_BConjNeg(rhs.clone()))))),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_KAnd_False" => {
            expect_contract(meta, "bool_and", "bool_false", "bool_update")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetBool(b), Kont::C_KAndL(_, k)) if matches!(b.as_ref(), Bool::C_BoolFalse) => Some(mk_state(
                        Control::C_RetBool(false_bool()),
                        store.clone(),
                        k.clone(),
                        running_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        "R_Final" => {
            expect_contract(meta, "finalize", "shape", "set_done")?;
            match state {
                State::C_ImpState(ctrl, store, kont, _) => match (ctrl.as_ref(), kont.as_ref()) {
                    (Control::C_RetUnit, Kont::C_KDone) => Some(mk_state(
                        Control::C_RetUnit,
                        store.clone(),
                        Box::new(Kont::C_KDone),
                        done_status(),
                    )),
                    _ => None,
                },
                _ => None,
            }
        },
        _ => {
            return Err(format!(
                "IMP MORK backend has no semantic handler for rule '{}' (id '{}', logical id '{}', source '{}')",
                meta.rule_name, meta.rule_id, meta.logical_transition_id, meta.source_instr
            ));
        },
    };
    Ok(next.into_iter().collect())
}

#[cfg(feature = "mork-backend")]
fn imp_source_instr(state: &State) -> Option<&'static str> {
    match state {
        State::C_Start(_, _) => Some("C_Start"),
        State::C_ImpState(ctrl, _, _, status) => {
            if !matches!(status.as_ref(), Status::C_Running) {
                return None;
            }
            match ctrl.as_ref() {
                Control::C_RunStmt(_) => Some("C_RunStmt"),
                Control::C_RunA(_) => Some("C_RunA"),
                Control::C_RunB(_) => Some("C_RunB"),
                Control::C_RetNat(_) => Some("C_RetNat"),
                Control::C_RetBool(_) => Some("C_RetBool"),
                Control::C_RetUnit => Some("C_RetUnit"),
                _ => None,
            }
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn imp_native_step_state(state: &State) -> Result<Vec<(String, State)>, String> {
    let Some(source_instr) = imp_source_instr(state) else {
        return Ok(Vec::new());
    };
    let contract = imp_rewrite_contract()?;
    let ordered = contract.ordered_rules_for(source_instr).ok_or_else(|| {
        format!("IMP transition artifact missing source instruction '{}'", source_instr)
    })?;
    dispatch_ordered_rules(
        ordered,
        |rule| {
            let meta = contract.rule(rule).cloned().ok_or_else(|| {
                format!(
                    "IMP rewrite contract missing metadata for rule '{}' listed under source '{}'",
                    rule, source_instr
                )
            })?;
            if meta.source_instr != source_instr {
                return Err(format!(
                    "IMP rewrite contract mismatch: rule '{}' expected source '{}', got '{}'",
                    rule, source_instr, meta.source_instr
                ));
            }
            Ok(meta)
        },
        |_rule, meta| imp_apply_rule(meta, state),
    )
}

#[cfg(feature = "mork-backend")]
fn run_imp_native_state_graph(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let wrapped = term
        .as_any()
        .downcast_ref::<IMPTerm>()
        .ok_or_else(|| {
            "IMP MORK backend expects IMP parsed core term wrapper (IMPTerm)".to_string()
        })?;
    let start_state = match &wrapped.0 {
        IMPTermInner::State(st) => st.clone(),
        _ => {
            return Err(format!(
                "IMP MORK backend expects top-level State term, got wrapper variant: {}",
                wrapped
            ));
        },
    };

    let start_display = format!("{}", term);
    let start_id = term.term_id();
    run_transition_graph(start_state, &start_display, start_id, limits, |state| {
        imp_native_step_state(state)
    })
}

#[cfg(feature = "mork-backend")]
pub fn run_imp_mork_backend(term: &dyn Term) -> Result<AscentResults, String> {
    run_imp_mork_backend_with_limits(term, MorkExecutionLimits::default())
}

#[cfg(feature = "mork-backend")]
pub fn run_imp_mork_backend_with_limits(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let started = Instant::now();
    let mut results = run_imp_native_state_graph(term, limits)?;
    results
        .phase_timings_ms
        .insert("mork_native_state_ms".to_string(), started.elapsed().as_secs_f64() * 1000.0);
    Ok(results)
}
