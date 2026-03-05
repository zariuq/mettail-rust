#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use std::sync::{Mutex, OnceLock};
language! {
    name: MeTTaFullState,
    options {
        runtime_surface_policy: deterministic,
        core_ground_eval: true,
        runtime_contract_deterministic_reduction: true,
        runtime_contract_memoization_safe: true,
        runtime_contract_specialization_safe: true,
    },

    // BEGIN GENERATED (Lean Export: types/terms/equations/rewrites)
    types {
        State
        Instr
        Atom
        Space
    },

    terms {
        C_State . instr:Instr, space:Space, out:Atom |- "C_State" "(" instr "," space "," out ")" : State;
        C_Eval . src:Atom |- "C_Eval" "(" src ")" : Instr;
        C_Unify . lhs:Atom, rhs:Atom |- "C_Unify" "(" lhs "," rhs ")" : Instr;
        C_Match . lhs:Atom, rhs:Atom |- "C_Match" "(" lhs "," rhs ")" : Instr;
        C_Chain . src:Atom, tmpl:Atom |- "C_Chain" "(" src "," tmpl ")" : Instr;
        C_TypeCheck . atom:Atom, ty:Atom |- "C_TypeCheck" "(" atom "," ty ")" : Instr;
        C_Cast . atom:Atom, ty:Atom |- "C_Cast" "(" atom "," ty ")" : Instr;
        C_Grounded1 . op:Atom, arg:Atom |- "C_Grounded1" "(" op "," arg ")" : Instr;
        C_Grounded2 . op:Atom, lhs:Atom, rhs:Atom |- "C_Grounded2" "(" op "," lhs "," rhs ")" : Instr;
        C_If . cond:Atom, thenVal:Atom, elseVal:Atom |- "C_If" "(" cond "," thenVal "," elseVal ")" : Instr;
        C_Return . dst:Atom |- "C_Return" "(" dst ")" : Instr;
        C_Done . |- "C_Done" : Instr;
        C_ATrue . |- "C_ATrue" : Atom;
        C_AFalse . |- "C_AFalse" : Atom;
        C_GBoolTrue . |- "C_GBoolTrue" : Atom;
        C_GBoolFalse . |- "C_GBoolFalse" : Atom;
        C_Bool . |- "C_Bool" : Atom;
        C_Atom . |- "C_Atom" : Atom;
        C_not . |- "C_not" : Atom;
        C_and . |- "C_and" : Atom;
        C_or . |- "C_or" : Atom;
        C_xor . |- "C_xor" : Atom;
        C_eqBool . |- "C_eqBool" : Atom;
        C_add . |- "C_add" : Atom;
        C_sub . |- "C_sub" : Atom;
        C_mul . |- "C_mul" : Atom;
        C_div . |- "C_div" : Atom;
        C_modOp . |- "C_modOp" : Atom;
        C_lt . |- "C_lt" : Atom;
        C_le . |- "C_le" : Atom;
        C_gt . |- "C_gt" : Atom;
        C_ge . |- "C_ge" : Atom;
        C_eqInt . |- "C_eqInt" : Atom;
        C_concat . |- "C_concat" : Atom;
        C_length . |- "C_length" : Atom;
        C_ANil . |- "C_ANil" : Atom;
        C_ACons . head:Atom, tail:Atom |- "C_ACons" "(" head "," tail ")" : Atom;
        C_AEqEntry . src:Atom, dst:Atom |- "C_AEqEntry" "(" src "," dst ")" : Atom;
        C_APEqEntry . src:Atom, dst:Atom |- "C_APEqEntry" "(" src "," dst ")" : Atom;
        C_ATypeEntry . atom:Atom, ty:Atom |- "C_ATypeEntry" "(" atom "," ty ")" : Atom;
        C_AError . tag:Atom, msg:Atom |- "C_AError" "(" tag "," msg ")" : Atom;
        C_GInt . token:Atom |- "C_GInt" "(" token ")" : Atom;
        C_GString . token:Atom |- "C_GString" "(" token ")" : Atom;
        C_GStringVec . chunks:Atom |- "C_GStringVec" "(" chunks ")" : Atom;
        C_GStringCodes . codes:Atom |- "C_GStringCodes" "(" codes ")" : Atom;
        C_UserAtom . name:Atom |- "C_UserAtom" "(" name ")" : Atom;
        C_Space . eqs:Atom, tys:Atom |- "C_Space" "(" eqs "," tys ")" : Space;
    },

    equations {    },

    rewrites {
        R0G . | coreGroundEvalLookup(space, src, dst) |- (C_State (C_Eval src) space out) ~> (C_State (C_Return dst) space dst);
        R0 . | noCoreGroundEval(space, src), eqnLookup(space, src, dst) |- (C_State (C_Eval src) space out) ~> (C_State (C_Return dst) space dst);
        R0P . | noCoreGroundEval(space, src), patternEqnLookup(space, src, dst) |- (C_State (C_Eval src) space out) ~> (C_State (C_Return dst) space dst);
        R1 . | noCoreGroundEval(space, src), noEqnLookup(space, src) |- (C_State (C_Eval src) space out) ~> (C_State (C_Return src) space src);
        R2 . | eq(lhs, rhs) |- (C_State (C_Unify lhs rhs) space out) ~> (C_State (C_Return C_ATrue) space C_ATrue);
        R3 . | neq(lhs, rhs) |- (C_State (C_Unify lhs rhs) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R4 . | eq(lhs, rhs) |- (C_State (C_Match lhs rhs) space out) ~> (C_State (C_Return C_ATrue) space C_ATrue);
        R5 . | neq(lhs, rhs) |- (C_State (C_Match lhs rhs) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R6 . | eqnLookup(space, src, dst) |- (C_State (C_Chain src tmpl) space out) ~> (C_State (C_Return dst) space dst);
        R6P . | patternEqnLookup(space, src, dst) |- (C_State (C_Chain src tmpl) space out) ~> (C_State (C_Return dst) space dst);
        R7 . | noEqnLookup(space, src) |- (C_State (C_Chain src tmpl) space out) ~> (C_State (C_Return tmpl) space tmpl);
        R8 . | typeOf(space, atom, ty) |- (C_State (C_TypeCheck atom ty) space out) ~> (C_State (C_Return C_ATrue) space C_ATrue);
        R9 . | notTypeOf(space, atom, ty) |- (C_State (C_TypeCheck atom ty) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R10 . | cast(space, atom, ty, casted) |- (C_State (C_Cast atom ty) space out) ~> (C_State (C_Return casted) space casted);
        R11 . | notCast(space, atom, ty) |- (C_State (C_Cast atom ty) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R12 . | groundedCall3(op, arg, result) |- (C_State (C_Grounded1 op arg) space out) ~> (C_State (C_Return result) space result);
        R13 . | noGroundedCall2(op, arg) |- (C_State (C_Grounded1 op arg) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R14 . | groundedCall4(op, lhs, rhs, result) |- (C_State (C_Grounded2 op lhs rhs) space out) ~> (C_State (C_Return result) space result);
        R15 . | noGroundedCall3(op, lhs, rhs) |- (C_State (C_Grounded2 op lhs rhs) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
        R16R0 . | coreGroundEvalLookup(space, dst, dst_any0) |- (C_State (C_Return dst) space out) ~> (C_State (C_Eval dst) space out);
        R16R1 . | eqnLookup(space, dst, dst_any1) |- (C_State (C_Return dst) space out) ~> (C_State (C_Eval dst) space out);
        R16R2 . | patternEqnLookup(space, dst, dst_any2) |- (C_State (C_Return dst) space out) ~> (C_State (C_Eval dst) space out);
        R16D . | noCoreGroundEval(space, dst), noEqnLookup(space, dst) |- (C_State (C_Return dst) space out) ~> (C_State C_Done space dst);
        R17 . | eq(cond, C_GBoolTrue) |- (C_State (C_If cond thenVal elseVal) space out) ~> (C_State (C_Return thenVal) space thenVal);
        R18 . | eq(cond, C_GBoolFalse) |- (C_State (C_If cond thenVal elseVal) space out) ~> (C_State (C_Return elseVal) space elseVal);
        R19 . | nonBoolAtom(cond) |- (C_State (C_If cond thenVal elseVal) space out) ~> (C_State (C_Return C_AFalse) space C_AFalse);
    },
    // END GENERATED (Lean Export: types/terms/equations/rewrites)

    // BEGIN HANDWRITTEN (premise backend logic)
    logic {
        // Seed domain relations from state terms so relation premises can bind nested fields.
        space(sp) <--
            state(st),
            if let State::C_State(_, ref sp0, _) = st,
            let sp = (**sp0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(_, _, ref out0) = st,
            let a = (**out0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Eval(ref src0) = &**instr,
            let a = (**src0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Unify(ref lhs0, _) = &**instr,
            let a = (**lhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Unify(_, ref rhs0) = &**instr,
            let a = (**rhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Match(ref lhs0, _) = &**instr,
            let a = (**lhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Match(_, ref rhs0) = &**instr,
            let a = (**rhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Chain(ref src0, _) = &**instr,
            let a = (**src0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Chain(_, ref tmpl0) = &**instr,
            let a = (**tmpl0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_TypeCheck(ref atom0, _) = &**instr,
            let a = (**atom0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_TypeCheck(_, ref ty0) = &**instr,
            let a = (**ty0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Cast(ref atom0, _) = &**instr,
            let a = (**atom0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Cast(_, ref ty0) = &**instr,
            let a = (**ty0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded1(ref op0, _) = &**instr,
            let a = (**op0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded1(_, ref arg0) = &**instr,
            let a = (**arg0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded2(ref op0, _, _) = &**instr,
            let a = (**op0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded2(_, ref lhs0, _) = &**instr,
            let a = (**lhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded2(_, _, ref rhs0) = &**instr,
            let a = (**rhs0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_If(ref cond0, _, _) = &**instr,
            let a = (**cond0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_If(_, ref then0, _) = &**instr,
            let a = (**then0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_If(_, _, ref else0) = &**instr,
            let a = (**else0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Return(ref dst0) = &**instr,
            let a = (**dst0).clone();

        atom(a) <--
            space(sp),
            if let Space::C_Space(ref eqs, _) = sp,
            let a = (**eqs).clone();

        atom(a) <--
            space(sp),
            if let Space::C_Space(_, ref tys) = sp,
            let a = (**tys).clone();

        atom(a) <--
            atom(list),
            if let Atom::C_ACons(ref head, _) = list,
            let a = (**head).clone();

        atom(a) <--
            atom(list),
            if let Atom::C_ACons(_, ref tail) = list,
            let a = (**tail).clone();

        atom(a) <--
            atom(entry),
            if let Atom::C_AEqEntry(ref src0, _) = entry,
            let a = (**src0).clone();

        atom(a) <--
            atom(entry),
            if let Atom::C_AEqEntry(_, ref dst0) = entry,
            let a = (**dst0).clone();

        atom(a) <--
            atom(entry),
            if let Atom::C_ATypeEntry(ref atom0, _) = entry,
            let a = (**atom0).clone();

        atom(a) <--
            atom(entry),
            if let Atom::C_ATypeEntry(_, ref ty0) = entry,
            let a = (**ty0).clone();

        atom(a) <--
            atom(err),
            if let Atom::C_AError(ref tag0, _) = err,
            let a = (**tag0).clone();

        atom(a) <--
            atom(err),
            if let Atom::C_AError(_, ref msg0) = err,
            let a = (**msg0).clone();

        atom(a) <--
            atom(ua),
            if let Atom::C_UserAtom(ref name) = ua,
            let a = (**name).clone();

        relation eqListContains(Atom, Atom, Atom);
        relation patternEqListContains(Atom, Atom, Atom);
        relation noEqPatternListContains(Atom, Atom);
        relation eqListDomain(Atom, Atom);
        relation typeListContains(Atom, Atom, Atom);
        relation noTypeListContains(Atom, Atom, Atom);
        relation nonBoolAtom(Atom);
        relation nonIntAtom(Atom);
        relation nonStringAtom(Atom);
        relation boolQuery(Atom);
        relation intQuery(Atom);
        relation stringQuery(Atom);
        relation compareQuery(Atom, Atom);
        relation ifCondQuery(Atom);

        relation eqnLookup(Space, Atom, Atom);
        relation patternEqnLookup(Space, Atom, Atom);
        relation coreGroundEvalLookup(Space, Atom, Atom);
        relation noCoreGroundEval(Space, Atom);
        relation noEqnLookup(Space, Atom);
        relation eqQuery(Space, Atom);
        relation eqNeedle(Atom);
        relation eq(Atom, Atom);
        relation neq(Atom, Atom);
        relation typeOf(Space, Atom, Atom);
        relation notTypeOf(Space, Atom, Atom);
        relation cast(Space, Atom, Atom, Atom);
        relation notCast(Space, Atom, Atom);
        relation typeQuery(Space, Atom, Atom);
        relation typeNeedle(Atom, Atom);
        relation groundedCall3(Atom, Atom, Atom);
        relation noGroundedCall2(Atom, Atom);
        relation groundedCall4(Atom, Atom, Atom, Atom);
        relation noGroundedCall3(Atom, Atom, Atom);
        relation grounded1Query(Atom, Atom);
        relation grounded2Query(Atom, Atom, Atom);

        // Restrict equation negative-case materialization to actual Eval/Chain queries.
        eqQuery(sp, src) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Eval(ref src0) = &**instr,
            let sp = (**sp0).clone(),
            let src = (**src0).clone();

        eqQuery(sp, src) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Chain(ref src0, _) = &**instr,
            let sp = (**sp0).clone(),
            let src = (**src0).clone();

        eqQuery(sp, src) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref src0) = &**instr,
            let sp = (**sp0).clone(),
            let src = (**src0).clone();

        eqNeedle(src) <--
            eqQuery(_, src);

        // Restrict equation list traversals to the active queried space/list and its tails.
        eqListDomain(list, src) <--
            eqQuery(sp, src),
            space(sp),
            if let Space::C_Space(ref eqs, _) = sp,
            let list = (**eqs).clone();

        eqListDomain(tail, src) <--
            eqListDomain(list, src),
            if let Atom::C_ACons(_, ref tail0) = list,
            let tail = (**tail0).clone();

        // Lookup relation over encoded list atoms.
        eqListContains(list, src, dst) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(ref head, _) = list,
            if let Atom::C_AEqEntry(ref src0, ref dst0) = &**head,
            let src_l = (**src0).clone(),
            if src_l == *src,
            let dst = (**dst0).clone();

        eqListContains(list, src, dst) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(_, ref tail) = list,
            eqListContains((**tail).clone(), src, dst);

        // Pattern equation lookup over encoded list atoms.
        patternEqListContains(list, src, dst) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(ref head, _) = list,
            if let Atom::C_APEqEntry(ref src_pat, ref dst_pat) = &**head,
            if let Some(dst0) = match_apply_pattern_entry(&**src_pat, &**dst_pat, src),
            let dst = dst0;

        patternEqListContains(list, src, dst) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(_, ref tail) = list,
            patternEqListContains((**tail).clone(), src, dst);

        // Single-pass proof that no exact or pattern equation matches this source.
        noEqPatternListContains(Atom::C_ANil, src) <--
            eqNeedle(src);

        noEqPatternListContains(list, src) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if let Atom::C_AEqEntry(ref src0, _) = &**head,
            let src_l = (**src0).clone(),
            if src_l != *src,
            noEqPatternListContains((**tail).clone(), src);

        noEqPatternListContains(list, src) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if let Atom::C_APEqEntry(ref src_pat, ref dst_pat) = &**head,
            if match_apply_pattern_entry(&**src_pat, &**dst_pat, src).is_none(),
            noEqPatternListContains((**tail).clone(), src);

        noEqPatternListContains(list, src) <--
            eqListDomain(list, src), eqNeedle(src),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if !matches!(&**head, Atom::C_AEqEntry(_, _)),
            if !matches!(&**head, Atom::C_APEqEntry(_, _)),
            noEqPatternListContains((**tail).clone(), src);

        // Restrict type negative-case materialization to actual TypeCheck/Cast queries.
        typeQuery(sp, atom0, ty) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_TypeCheck(ref atom1, ref ty1) = &**instr,
            let sp = (**sp0).clone(),
            let atom0 = (**atom1).clone(),
            let ty = (**ty1).clone();

        typeQuery(sp, atom0, ty) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Cast(ref atom1, ref ty1) = &**instr,
            let sp = (**sp0).clone(),
            let atom0 = (**atom1).clone(),
            let ty = (**ty1).clone();

        typeNeedle(atom0, ty) <--
            typeQuery(_, atom0, ty);

        // Type relation over encoded list atoms.
        typeListContains(list, atom0, ty) <--
            atom(list), typeNeedle(atom0, ty),
            if let Atom::C_ACons(ref head, _) = list,
            if let Atom::C_ATypeEntry(ref atom1, ref ty1) = &**head,
            let atom_l = (**atom1).clone(),
            if atom_l == *atom0,
            let ty_l = (**ty1).clone(),
            if ty_l == *ty;

        typeListContains(list, atom0, ty) <--
            atom(list), typeNeedle(atom0, ty),
            if let Atom::C_ACons(_, ref tail) = list,
            typeListContains((**tail).clone(), atom0, ty);

        // Proof of absent (atom, ty) mapping over encoded list atoms.
        noTypeListContains(Atom::C_ANil, atom0, ty) <--
            typeNeedle(atom0, ty);

        noTypeListContains(list, atom0, ty) <--
            atom(list), typeNeedle(atom0, ty),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if let Atom::C_ATypeEntry(ref atom1, ref ty1) = &**head,
            let atom_l = (**atom1).clone(),
            if atom_l != *atom0,
            noTypeListContains((**tail).clone(), atom0, ty);

        noTypeListContains(list, atom0, ty) <--
            atom(list), typeNeedle(atom0, ty),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if let Atom::C_ATypeEntry(ref atom1, ref ty1) = &**head,
            let atom_l = (**atom1).clone(),
            let ty_l = (**ty1).clone(),
            if atom_l == *atom0,
            if ty_l != *ty,
            noTypeListContains((**tail).clone(), atom0, ty);

        noTypeListContains(list, atom0, ty) <--
            atom(list), typeNeedle(atom0, ty),
            if let Atom::C_ACons(ref head, ref tail) = list,
            if !matches!(&**head, Atom::C_ATypeEntry(_, _)),
            noTypeListContains((**tail).clone(), atom0, ty);

        // Space-indexed operational facts.
        eqnLookup(sp, src, dst) <--
            eqQuery(sp, src),
            if let Space::C_Space(ref eqs, _) = sp,
            eqListContains((**eqs).clone(), src, dst);

        patternEqnLookup(sp, src, dst) <--
            eqQuery(sp, src),
            if let Space::C_Space(ref eqs, _) = sp,
            patternEqListContains((**eqs).clone(), src, dst);

        coreGroundEvalLookup(sp, src, dst) <--
            eqQuery(sp, src),
            if let Some(dst0) = eval_ground_call_core(sp, src),
            let dst = dst0;

        noCoreGroundEval(sp, src) <--
            eqQuery(sp, src),
            if eval_ground_call_core(sp, src).is_none();

        noEqnLookup(sp, src) <--
            eqQuery(sp, src),
            if let Space::C_Space(ref eqs, _) = sp,
            noEqPatternListContains((**eqs).clone(), src);

        typeOf(sp, atom0, ty) <--
            typeQuery(sp, atom0, ty),
            if let Space::C_Space(_, ref tys) = sp,
            typeListContains((**tys).clone(), atom0, ty);

        notTypeOf(sp, atom0, ty) <--
            typeQuery(sp, atom0, ty),
            if let Space::C_Space(_, ref tys) = sp,
            noTypeListContains((**tys).clone(), atom0, ty);

        cast(sp, atom0, ty, atom0) <--
            typeOf(sp, atom0, ty);

        notCast(sp, atom0, ty) <--
            notTypeOf(sp, atom0, ty);

        // Query-scoped equality/inequality: avoid global atom cross-products.
        compareQuery(lhs, rhs) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Unify(ref lhs0, ref rhs0) = &**instr,
            let lhs = (**lhs0).clone(),
            let rhs = (**rhs0).clone();

        compareQuery(lhs, rhs) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Match(ref lhs0, ref rhs0) = &**instr,
            let lhs = (**lhs0).clone(),
            let rhs = (**rhs0).clone();

        ifCondQuery(cond) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_If(ref cond0, _, _) = &**instr,
            let cond = (**cond0).clone();

        eq(lhs, rhs) <--
            compareQuery(lhs, rhs),
            if lhs == rhs;

        eq(cond, Atom::C_GBoolTrue) <--
            ifCondQuery(cond),
            if *cond == Atom::C_GBoolTrue;

        eq(cond, Atom::C_GBoolFalse) <--
            ifCondQuery(cond),
            if *cond == Atom::C_GBoolFalse;

        neq(lhs, rhs) <--
            compareQuery(lhs, rhs),
            if lhs != rhs;

        // Query-scoped needles: avoid global materialization of non* relations.
        boolQuery(cond) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_If(ref cond0, _, _) = &**instr,
            let cond = (**cond0).clone();

        boolQuery(lhs) <--
            grounded2Query(op, lhs, _),
            if *op == Atom::C_and || *op == Atom::C_or || *op == Atom::C_xor || *op == Atom::C_eqBool;
        boolQuery(rhs) <--
            grounded2Query(op, _, rhs),
            if *op == Atom::C_and || *op == Atom::C_or || *op == Atom::C_xor || *op == Atom::C_eqBool;

        intQuery(lhs) <--
            grounded2Query(op, lhs, _),
            if *op == Atom::C_add || *op == Atom::C_sub || *op == Atom::C_mul
                || *op == Atom::C_div || *op == Atom::C_modOp || *op == Atom::C_lt
                || *op == Atom::C_le || *op == Atom::C_gt || *op == Atom::C_ge || *op == Atom::C_eqInt;
        intQuery(rhs) <--
            grounded2Query(op, _, rhs),
            if *op == Atom::C_add || *op == Atom::C_sub || *op == Atom::C_mul
                || *op == Atom::C_div || *op == Atom::C_modOp || *op == Atom::C_lt
                || *op == Atom::C_le || *op == Atom::C_gt || *op == Atom::C_ge || *op == Atom::C_eqInt;

        stringQuery(lhs) <--
            grounded2Query(Atom::C_concat, lhs, _);
        stringQuery(rhs) <--
            grounded2Query(Atom::C_concat, _, rhs);
        stringQuery(arg) <--
            grounded1Query(Atom::C_length, arg);

        nonBoolAtom(a) <--
            boolQuery(a),
            if *a != Atom::C_GBoolTrue,
            if *a != Atom::C_GBoolFalse;

        nonIntAtom(a) <--
            intQuery(a),
            if !matches!(a, Atom::C_GInt(_));

        nonStringAtom(a) <--
            stringQuery(a),
            if !matches!(a, Atom::C_GString(_)),
            if !matches!(a, Atom::C_GStringCodes(_));

        // Restrict noGroundedCall* derivations to actual grounded instruction queries.
        grounded1Query(op, arg) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded1(ref op0, ref arg0) = &**instr,
            let op = (**op0).clone(),
            let arg = (**arg0).clone();

        grounded2Query(op, lhs, rhs) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Grounded2(ref op0, ref lhs0, ref rhs0) = &**instr,
            let op = (**op0).clone(),
            let lhs = (**lhs0).clone(),
            let rhs = (**rhs0).clone();

        // Grounded operations (small executable subset).
        groundedCall3(Atom::C_not, Atom::C_GBoolTrue, Atom::C_GBoolFalse);
        groundedCall3(Atom::C_not, Atom::C_GBoolFalse, Atom::C_GBoolTrue);

        groundedCall4(Atom::C_and, Atom::C_GBoolTrue, Atom::C_GBoolTrue, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_and, Atom::C_GBoolTrue, Atom::C_GBoolFalse, Atom::C_GBoolFalse);
        groundedCall4(Atom::C_and, Atom::C_GBoolFalse, Atom::C_GBoolTrue, Atom::C_GBoolFalse);
        groundedCall4(Atom::C_and, Atom::C_GBoolFalse, Atom::C_GBoolFalse, Atom::C_GBoolFalse);

        groundedCall4(Atom::C_or, Atom::C_GBoolTrue, Atom::C_GBoolTrue, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_or, Atom::C_GBoolTrue, Atom::C_GBoolFalse, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_or, Atom::C_GBoolFalse, Atom::C_GBoolTrue, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_or, Atom::C_GBoolFalse, Atom::C_GBoolFalse, Atom::C_GBoolFalse);

        groundedCall4(Atom::C_xor, Atom::C_GBoolTrue, Atom::C_GBoolTrue, Atom::C_GBoolFalse);
        groundedCall4(Atom::C_xor, Atom::C_GBoolTrue, Atom::C_GBoolFalse, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_xor, Atom::C_GBoolFalse, Atom::C_GBoolTrue, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_xor, Atom::C_GBoolFalse, Atom::C_GBoolFalse, Atom::C_GBoolFalse);

        groundedCall4(Atom::C_eqBool, Atom::C_GBoolTrue, Atom::C_GBoolTrue, Atom::C_GBoolTrue);
        groundedCall4(Atom::C_eqBool, Atom::C_GBoolTrue, Atom::C_GBoolFalse, Atom::C_GBoolFalse);
        groundedCall4(Atom::C_eqBool, Atom::C_GBoolFalse, Atom::C_GBoolTrue, Atom::C_GBoolFalse);
        groundedCall4(Atom::C_eqBool, Atom::C_GBoolFalse, Atom::C_GBoolFalse, Atom::C_GBoolTrue);

        groundedCall4(Atom::C_add, lhs, rhs, result) <--
            grounded2Query(Atom::C_add, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = make_int_atom(ln + rn);

        groundedCall4(Atom::C_sub, lhs, rhs, result) <--
            grounded2Query(Atom::C_sub, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = make_int_atom(ln - rn);

        groundedCall4(Atom::C_mul, lhs, rhs, result) <--
            grounded2Query(Atom::C_mul, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = make_int_atom(ln * rn);

        groundedCall4(Atom::C_div, lhs, rhs, result) <--
            grounded2Query(Atom::C_div, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            if rn != 0,
            let result = make_int_atom(ln / rn);

        groundedCall4(Atom::C_modOp, lhs, rhs, result) <--
            grounded2Query(Atom::C_modOp, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            if rn != 0,
            let result = make_int_atom(ln % rn);

        groundedCall4(Atom::C_lt, lhs, rhs, result) <--
            grounded2Query(Atom::C_lt, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = if ln < rn { Atom::C_GBoolTrue } else { Atom::C_GBoolFalse };

        groundedCall4(Atom::C_le, lhs, rhs, result) <--
            grounded2Query(Atom::C_le, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = if ln <= rn { Atom::C_GBoolTrue } else { Atom::C_GBoolFalse };

        groundedCall4(Atom::C_gt, lhs, rhs, result) <--
            grounded2Query(Atom::C_gt, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = if ln > rn { Atom::C_GBoolTrue } else { Atom::C_GBoolFalse };

        groundedCall4(Atom::C_ge, lhs, rhs, result) <--
            grounded2Query(Atom::C_ge, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = if ln >= rn { Atom::C_GBoolTrue } else { Atom::C_GBoolFalse };

        groundedCall4(Atom::C_eqInt, lhs, rhs, result) <--
            grounded2Query(Atom::C_eqInt, lhs, rhs),
            if let Atom::C_GInt(ref ln_tok) = lhs,
            if let Atom::C_GInt(ref rn_tok) = rhs,
            if let Some(ln) = parse_int_token(&**ln_tok),
            if let Some(rn) = parse_int_token(&**rn_tok),
            let result = if ln == rn { Atom::C_GBoolTrue } else { Atom::C_GBoolFalse };

        groundedCall4(Atom::C_concat, lhs, rhs, result) <--
            grounded2Query(Atom::C_concat, lhs, rhs),
            if let Some(ls) = extract_string_from_atom(&lhs),
            if let Some(rs) = extract_string_from_atom(&rhs),
            let result = make_string_atom(format!("{}{}", ls, rs));

        groundedCall3(Atom::C_length, arg, result) <--
            grounded1Query(Atom::C_length, arg),
            if let Some(s) = extract_string_from_atom(&arg),
            let result = make_int_atom(s.len() as i64);

        // No-case grounded dispatch rules (stratified, no negation over helper relations).
        noGroundedCall2(op, arg) <--
            grounded1Query(op, arg),
            if *op != Atom::C_not,
            if *op != Atom::C_length;

        noGroundedCall2(Atom::C_not, arg) <--
            grounded1Query(Atom::C_not, arg),
            if *arg != Atom::C_GBoolTrue,
            if *arg != Atom::C_GBoolFalse;

        noGroundedCall3(op, lhs, rhs) <--
            grounded2Query(op, lhs, rhs),
            if *op != Atom::C_and,
            if *op != Atom::C_or,
            if *op != Atom::C_xor,
            if *op != Atom::C_eqBool,
            if *op != Atom::C_add,
            if *op != Atom::C_sub,
            if *op != Atom::C_mul,
            if *op != Atom::C_div,
            if *op != Atom::C_modOp,
            if *op != Atom::C_lt,
            if *op != Atom::C_le,
            if *op != Atom::C_gt,
            if *op != Atom::C_ge,
            if *op != Atom::C_eqInt,
            if *op != Atom::C_concat;

        noGroundedCall3(Atom::C_and, lhs, rhs) <--
            grounded2Query(Atom::C_and, lhs, rhs),
            nonBoolAtom(lhs);
        noGroundedCall3(Atom::C_and, lhs, rhs) <--
            grounded2Query(Atom::C_and, lhs, rhs),
            nonBoolAtom(rhs);

        noGroundedCall3(Atom::C_or, lhs, rhs) <--
            grounded2Query(Atom::C_or, lhs, rhs),
            nonBoolAtom(lhs);
        noGroundedCall3(Atom::C_or, lhs, rhs) <--
            grounded2Query(Atom::C_or, lhs, rhs),
            nonBoolAtom(rhs);

        noGroundedCall3(Atom::C_xor, lhs, rhs) <--
            grounded2Query(Atom::C_xor, lhs, rhs),
            nonBoolAtom(lhs);
        noGroundedCall3(Atom::C_xor, lhs, rhs) <--
            grounded2Query(Atom::C_xor, lhs, rhs),
            nonBoolAtom(rhs);

        noGroundedCall3(Atom::C_eqBool, lhs, rhs) <--
            grounded2Query(Atom::C_eqBool, lhs, rhs),
            nonBoolAtom(lhs);
        noGroundedCall3(Atom::C_eqBool, lhs, rhs) <--
            grounded2Query(Atom::C_eqBool, lhs, rhs),
            nonBoolAtom(rhs);

        noGroundedCall3(Atom::C_add, lhs, rhs) <--
            grounded2Query(Atom::C_add, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_add, lhs, rhs) <--
            grounded2Query(Atom::C_add, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_sub, lhs, rhs) <--
            grounded2Query(Atom::C_sub, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_sub, lhs, rhs) <--
            grounded2Query(Atom::C_sub, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_mul, lhs, rhs) <--
            grounded2Query(Atom::C_mul, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_mul, lhs, rhs) <--
            grounded2Query(Atom::C_mul, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_lt, lhs, rhs) <--
            grounded2Query(Atom::C_lt, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_lt, lhs, rhs) <--
            grounded2Query(Atom::C_lt, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_eqInt, lhs, rhs) <--
            grounded2Query(Atom::C_eqInt, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_eqInt, lhs, rhs) <--
            grounded2Query(Atom::C_eqInt, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_div, lhs, rhs) <--
            grounded2Query(Atom::C_div, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_div, lhs, rhs) <--
            grounded2Query(Atom::C_div, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_modOp, lhs, rhs) <--
            grounded2Query(Atom::C_modOp, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_modOp, lhs, rhs) <--
            grounded2Query(Atom::C_modOp, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_le, lhs, rhs) <--
            grounded2Query(Atom::C_le, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_le, lhs, rhs) <--
            grounded2Query(Atom::C_le, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_gt, lhs, rhs) <--
            grounded2Query(Atom::C_gt, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_gt, lhs, rhs) <--
            grounded2Query(Atom::C_gt, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_ge, lhs, rhs) <--
            grounded2Query(Atom::C_ge, lhs, rhs),
            nonIntAtom(lhs);
        noGroundedCall3(Atom::C_ge, lhs, rhs) <--
            grounded2Query(Atom::C_ge, lhs, rhs),
            nonIntAtom(rhs);

        noGroundedCall3(Atom::C_concat, lhs, rhs) <--
            grounded2Query(Atom::C_concat, lhs, rhs),
            nonStringAtom(lhs);
        noGroundedCall3(Atom::C_concat, lhs, rhs) <--
            grounded2Query(Atom::C_concat, lhs, rhs),
            nonStringAtom(rhs);

        noGroundedCall2(Atom::C_length, arg) <--
            grounded1Query(Atom::C_length, arg),
            nonStringAtom(arg);
    },
}

fn token_name_from_atom(atom: &Atom) -> Option<String> {
    match atom {
        Atom::AVar(var) => match &var.0 {
            mettail_runtime::Var::Free(fv) => fv.pretty_name.clone(),
            _ => None,
        },
        _ => None,
    }
    // END HANDWRITTEN (premise backend logic)
}

fn pattern_var_name(atom: &Atom) -> Option<String> {
    let Atom::C_UserAtom(name_atom) = atom else {
        return None;
    };
    let name = extract_string_from_atom(name_atom)?;
    if name.starts_with('$') && name.len() > 1 {
        Some(name)
    } else {
        None
    }
}

fn match_pattern_atom(
    pattern: &Atom,
    value: &Atom,
    env: &mut std::collections::HashMap<String, Atom>,
) -> bool {
    if let Some(var_name) = pattern_var_name(pattern) {
        if let Some(bound) = env.get(&var_name) {
            return bound == value;
        }
        env.insert(var_name, value.clone());
        return true;
    }

    match (pattern, value) {
        (Atom::C_ACons(ph, pt), Atom::C_ACons(vh, vt)) => {
            match_pattern_atom(ph, vh, env) && match_pattern_atom(pt, vt, env)
        },
        (Atom::C_AEqEntry(ps, pd), Atom::C_AEqEntry(vs, vd))
        | (Atom::C_APEqEntry(ps, pd), Atom::C_APEqEntry(vs, vd))
        | (Atom::C_ATypeEntry(ps, pd), Atom::C_ATypeEntry(vs, vd)) => {
            match_pattern_atom(ps, vs, env) && match_pattern_atom(pd, vd, env)
        },
        (Atom::C_GInt(ps), Atom::C_GInt(vs))
        | (Atom::C_GString(ps), Atom::C_GString(vs))
        | (Atom::C_GStringVec(ps), Atom::C_GStringVec(vs))
        | (Atom::C_GStringCodes(ps), Atom::C_GStringCodes(vs))
        | (Atom::C_UserAtom(ps), Atom::C_UserAtom(vs)) => match_pattern_atom(ps, vs, env),
        _ => pattern == value,
    }
}

fn substitute_pattern_atom(expr: &Atom, env: &std::collections::HashMap<String, Atom>) -> Atom {
    if let Some(var_name) = pattern_var_name(expr) {
        return env.get(&var_name).cloned().unwrap_or_else(|| expr.clone());
    }

    match expr {
        Atom::C_ACons(head, tail) => Atom::C_ACons(
            Box::new(substitute_pattern_atom(head, env)),
            Box::new(substitute_pattern_atom(tail, env)),
        ),
        Atom::C_AEqEntry(src, dst) => Atom::C_AEqEntry(
            Box::new(substitute_pattern_atom(src, env)),
            Box::new(substitute_pattern_atom(dst, env)),
        ),
        Atom::C_APEqEntry(src, dst) => Atom::C_APEqEntry(
            Box::new(substitute_pattern_atom(src, env)),
            Box::new(substitute_pattern_atom(dst, env)),
        ),
        Atom::C_ATypeEntry(atom0, ty) => Atom::C_ATypeEntry(
            Box::new(substitute_pattern_atom(atom0, env)),
            Box::new(substitute_pattern_atom(ty, env)),
        ),
        Atom::C_GInt(tok) => Atom::C_GInt(Box::new(substitute_pattern_atom(tok, env))),
        Atom::C_GString(tok) => Atom::C_GString(Box::new(substitute_pattern_atom(tok, env))),
        Atom::C_GStringVec(chunks) => {
            Atom::C_GStringVec(Box::new(substitute_pattern_atom(chunks, env)))
        },
        Atom::C_GStringCodes(codes) => {
            Atom::C_GStringCodes(Box::new(substitute_pattern_atom(codes, env)))
        },
        Atom::C_UserAtom(name) => Atom::C_UserAtom(Box::new(substitute_pattern_atom(name, env))),
        _ => expr.clone(),
    }
}

fn match_apply_pattern_entry(src_pat: &Atom, dst_pat: &Atom, src: &Atom) -> Option<Atom> {
    let mut env = std::collections::HashMap::new();
    if !match_pattern_atom(src_pat, src, &mut env) {
        return None;
    }
    Some(substitute_pattern_atom(dst_pat, &env))
}

fn contains_pattern_var_atom_expr(atom: &Atom) -> bool {
    if pattern_var_name(atom).is_some() {
        return true;
    }
    match atom {
        Atom::C_ACons(head, tail)
        | Atom::C_AEqEntry(head, tail)
        | Atom::C_APEqEntry(head, tail)
        | Atom::C_ATypeEntry(head, tail) => {
            contains_pattern_var_atom_expr(head) || contains_pattern_var_atom_expr(tail)
        },
        Atom::C_GInt(tok)
        | Atom::C_GString(tok)
        | Atom::C_GStringVec(tok)
        | Atom::C_GStringCodes(tok)
        | Atom::C_UserAtom(tok) => contains_pattern_var_atom_expr(tok),
        _ => false,
    }
}

fn apply_space_eq_once(space: &Space, src: &Atom) -> Option<Atom> {
    // Try exact match first, then pattern match
    apply_space_exact_eq(space, src).or_else(|| apply_space_pattern_eq(space, src))
}

/// Try only exact (non-pattern) equation entries.
fn apply_space_exact_eq(space: &Space, src: &Atom) -> Option<Atom> {
    let Space::C_Space(ref eqs, _) = space else {
        return None;
    };
    let mut cur = eqs.as_ref();
    loop {
        match cur {
            Atom::C_ANil => return None,
            Atom::C_ACons(head, tail) => {
                if let Atom::C_AEqEntry(lhs, rhs) = head.as_ref() {
                    if lhs.as_ref() == src {
                        return Some(rhs.as_ref().clone());
                    }
                }
                cur = tail.as_ref();
            },
            _ => return None,
        }
    }
}

/// Try only pattern equation entries.
fn apply_space_pattern_eq(space: &Space, src: &Atom) -> Option<Atom> {
    let Space::C_Space(ref eqs, _) = space else {
        return None;
    };
    let mut cur = eqs.as_ref();
    loop {
        match cur {
            Atom::C_ANil => return None,
            Atom::C_ACons(head, tail) => {
                if let Atom::C_APEqEntry(lhs_pat, rhs_pat) = head.as_ref() {
                    if let Some(out) = match_apply_pattern_entry(lhs_pat, rhs_pat, src) {
                        return Some(out);
                    }
                }
                cur = tail.as_ref();
            },
            _ => return None,
        }
    }
}

fn atom_head_symbol(atom: &Atom) -> Option<String> {
    match atom {
        Atom::C_not => Some("not".to_string()),
        Atom::C_and => Some("and".to_string()),
        Atom::C_or => Some("or".to_string()),
        Atom::C_xor => Some("xor".to_string()),
        Atom::C_eqBool => Some("eq-bool".to_string()),
        Atom::C_add => Some("+".to_string()),
        Atom::C_sub => Some("-".to_string()),
        Atom::C_mul => Some("*".to_string()),
        Atom::C_div => Some("/".to_string()),
        Atom::C_modOp => Some("%".to_string()),
        Atom::C_lt => Some("<".to_string()),
        Atom::C_le => Some("<=".to_string()),
        Atom::C_gt => Some(">".to_string()),
        Atom::C_ge => Some(">=".to_string()),
        Atom::C_eqInt => Some("==".to_string()),
        Atom::C_concat => Some("concat".to_string()),
        Atom::C_length => Some("length".to_string()),
        Atom::C_UserAtom(name) => extract_string_from_atom(name),
        _ => None,
    }
}

fn decode_cons_list(atom: &Atom) -> Option<Vec<Atom>> {
    let mut items = Vec::new();
    let mut cur = atom;
    loop {
        match cur {
            Atom::C_ANil => return Some(items),
            Atom::C_ACons(head, tail) => {
                items.push(head.as_ref().clone());
                cur = tail.as_ref();
            },
            _ => return None,
        }
    }
}

fn encode_cons_list(items: &[Atom]) -> Atom {
    let mut out = Atom::C_ANil;
    for item in items.iter().rev() {
        out = Atom::C_ACons(Box::new(item.clone()), Box::new(out));
    }
    out
}

fn flatten_applied_head(head: &Atom, out: &mut Vec<Atom>) -> bool {
    let Some(items) = decode_cons_list(head) else {
        out.push(head.clone());
        return false;
    };
    let Some((nested_head, nested_args)) = items.split_first() else {
        out.push(head.clone());
        return false;
    };
    let _ = flatten_applied_head(nested_head, out);
    out.extend(nested_args.iter().cloned());
    true
}

fn flatten_application_items(items: &[Atom]) -> Vec<Atom> {
    let Some((head, args)) = items.split_first() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let changed = flatten_applied_head(head, &mut out);
    out.extend(args.iter().cloned());
    if changed {
        out
    } else {
        items.to_vec()
    }
}

fn eval_ground_call_core(space: &Space, src: &Atom) -> Option<Atom> {
    if !matches!(src, Atom::C_ACons(_, _)) || contains_pattern_var_atom_expr(src) {
        return None;
    }
    let Space::C_Space(eqs, _) = space else {
        return None;
    };

    static CORE_GROUND_EVAL_CACHE: OnceLock<
        Mutex<std::collections::HashMap<(Atom, Atom), Option<Atom>>>,
    > = OnceLock::new();
    let cache = CORE_GROUND_EVAL_CACHE.get_or_init(|| Mutex::new(std::collections::HashMap::new()));
    let key = (eqs.as_ref().clone(), src.clone());
    if let Ok(guard) = cache.lock() {
        if let Some(cached) = guard.get(&key) {
            return cached.clone();
        }
    }

    let mut memo = std::collections::HashMap::new();
    let mut in_progress = std::collections::HashSet::new();
    let out = eval_ground_call_core_inner(space, src, &mut memo, &mut in_progress, 0);
    if let Ok(mut guard) = cache.lock() {
        if guard.len() > 2048 {
            guard.clear();
        }
        guard.insert(key, out.clone());
    }
    out
}

fn eval_ground_call_core_inner(
    space: &Space,
    expr: &Atom,
    memo: &mut std::collections::HashMap<Atom, Atom>,
    in_progress: &mut std::collections::HashSet<Atom>,
    depth: usize,
) -> Option<Atom> {
    const MAX_CORE_GROUND_EVAL_DEPTH: usize = 4096;
    if depth > MAX_CORE_GROUND_EVAL_DEPTH || contains_pattern_var_atom_expr(expr) {
        return None;
    }
    if let Some(cached) = memo.get(expr) {
        return Some(cached.clone());
    }
    if !in_progress.insert(expr.clone()) {
        return None;
    }

    // Evaluation strategy: exact equations first, then reduce arguments,
    // then pattern equations, then builtins.
    //
    // This prevents pattern equations like (= (f $n) (f (- $n 1))) from
    // matching before arguments are reduced, which would cause infinite
    // nesting: (f 1) -> (f (- 1 1)) -> (f (- (- 1 1) 1)) -> ...
    let out = if let Some(next) = apply_space_exact_eq(space, expr) {
        // Exact equation match — recurse on result
        if &next == expr {
            Some(next)
        } else {
            eval_ground_call_core_inner(space, &next, memo, in_progress, depth + 1).or(Some(next))
        }
    } else if let Some(items) = decode_cons_list(expr) {
        let flat_items = flatten_application_items(&items);
        if flat_items != items {
            let flattened = encode_cons_list(&flat_items);
            eval_ground_call_core_inner(space, &flattened, memo, in_progress, depth + 1)
                .or(Some(flattened))
        } else {
            // Check if this is a lazy builtin (if) that must fire before arg reduction
            let is_lazy_builtin = items
                .first()
                .and_then(|h| atom_head_symbol(h))
                .map(|s| s == "if")
                .unwrap_or(false);

            if is_lazy_builtin {
                // Lazy builtins: try builtin first (handles short-circuit eval)
                if let Some(result) =
                    eval_ground_builtin_call(space, &items, memo, in_progress, depth + 1)
                {
                    Some(result)
                } else {
                    None
                }
            } else {
                // Normal evaluation order:
                // 1. Try reducing arguments (inside-out)
                // 2. Try builtins on original args
                // 3. Try pattern equations (only when args are stable)
                if let Some(result) =
                    eval_ground_call_with_reduced_args(space, &items, memo, in_progress, depth + 1)
                {
                    Some(result)
                } else if let Some(result) =
                    eval_ground_builtin_call(space, &items, memo, in_progress, depth + 1)
                {
                    Some(result)
                } else if let Some(next) = apply_space_pattern_eq(space, expr) {
                    if &next == expr {
                        Some(next)
                    } else {
                        eval_ground_call_core_inner(space, &next, memo, in_progress, depth + 1)
                            .or(Some(next))
                    }
                } else {
                    None
                }
            }
        }
    } else {
        Some(expr.clone())
    };

    in_progress.remove(expr);
    if let Some(ref result) = out {
        memo.insert(expr.clone(), result.clone());
    }
    out
}

fn eval_ground_call_with_reduced_args(
    space: &Space,
    items: &[Atom],
    memo: &mut std::collections::HashMap<Atom, Atom>,
    in_progress: &mut std::collections::HashSet<Atom>,
    depth: usize,
) -> Option<Atom> {
    let mut reduced_items = Vec::with_capacity(items.len());
    let mut changed = false;
    for (idx, item) in items.iter().enumerate() {
        if idx == 0 {
            // Keep operator head stable; flatten_application_items already normalized nested heads.
            reduced_items.push(item.clone());
            continue;
        }
        let next = eval_ground_call_core_inner(space, item, memo, in_progress, depth)?;
        changed |= next != *item;
        reduced_items.push(next);
    }
    if !changed {
        return None;
    }

    if let Some(result) = eval_ground_builtin_call(space, &reduced_items, memo, in_progress, depth)
    {
        return Some(result);
    }

    let reduced_expr = encode_cons_list(&reduced_items);
    if let Some(next) = apply_space_eq_once(space, &reduced_expr) {
        if next == reduced_expr {
            return Some(next);
        }
        return eval_ground_call_core_inner(space, &next, memo, in_progress, depth + 1)
            .or(Some(next));
    }

    eval_ground_call_core_inner(space, &reduced_expr, memo, in_progress, depth + 1)
        .or(Some(reduced_expr))
}

fn normalize_builtin_op(op: &str) -> &str {
    match op {
        "add" => "+",
        "sub" => "-",
        "mul" => "*",
        "div" => "/",
        "mod" | "modop" | "modOp" => "%",
        "lt" => "<",
        "le" => "<=",
        "gt" => ">",
        "ge" => ">=",
        "eq-int" => "==",
        _ => op,
    }
}

fn eval_ground_builtin_call(
    space: &Space,
    items: &[Atom],
    memo: &mut std::collections::HashMap<Atom, Atom>,
    in_progress: &mut std::collections::HashSet<Atom>,
    depth: usize,
) -> Option<Atom> {
    let (head, args) = items.split_first()?;
    let op = atom_head_symbol(head)?;
    let op = normalize_builtin_op(op.as_str());
    match (op, args) {
        ("if", [cond, then_v, else_v]) => {
            let cond_v = eval_ground_call_core_inner(space, cond, memo, in_progress, depth)?;
            match cond_v {
                Atom::C_GBoolTrue => {
                    eval_ground_call_core_inner(space, then_v, memo, in_progress, depth)
                },
                Atom::C_GBoolFalse => {
                    eval_ground_call_core_inner(space, else_v, memo, in_progress, depth)
                },
                _ => None,
            }
        },
        ("not", [arg]) => {
            match eval_ground_call_core_inner(space, arg, memo, in_progress, depth)? {
                Atom::C_GBoolTrue => Some(Atom::C_GBoolFalse),
                Atom::C_GBoolFalse => Some(Atom::C_GBoolTrue),
                _ => None,
            }
        },
        ("and", [lhs, rhs])
        | ("or", [lhs, rhs])
        | ("xor", [lhs, rhs])
        | ("eq-bool", [lhs, rhs]) => {
            let lv = eval_ground_call_core_inner(space, lhs, memo, in_progress, depth)?;
            let rv = eval_ground_call_core_inner(space, rhs, memo, in_progress, depth)?;
            let (lb, rb) = match (lv, rv) {
                (Atom::C_GBoolTrue, Atom::C_GBoolTrue) => (true, true),
                (Atom::C_GBoolTrue, Atom::C_GBoolFalse) => (true, false),
                (Atom::C_GBoolFalse, Atom::C_GBoolTrue) => (false, true),
                (Atom::C_GBoolFalse, Atom::C_GBoolFalse) => (false, false),
                _ => return None,
            };
            let out = match op {
                "and" => lb && rb,
                "or" => lb || rb,
                "xor" => lb ^ rb,
                "eq-bool" => lb == rb,
                _ => return None,
            };
            Some(if out {
                Atom::C_GBoolTrue
            } else {
                Atom::C_GBoolFalse
            })
        },
        ("+", [lhs, rhs])
        | ("-", [lhs, rhs])
        | ("*", [lhs, rhs])
        | ("/", [lhs, rhs])
        | ("%", [lhs, rhs])
        | ("<", [lhs, rhs])
        | ("<=", [lhs, rhs])
        | (">", [lhs, rhs])
        | (">=", [lhs, rhs])
        | ("==", [lhs, rhs]) => {
            let lv = eval_ground_call_core_inner(space, lhs, memo, in_progress, depth)?;
            let rv = eval_ground_call_core_inner(space, rhs, memo, in_progress, depth)?;
            let (ln, rn) = match (&lv, &rv) {
                (Atom::C_GInt(ltok), Atom::C_GInt(rtok)) => {
                    (parse_int_token(ltok.as_ref())?, parse_int_token(rtok.as_ref())?)
                },
                _ => return None,
            };
            match op {
                "+" => Some(make_int_atom(ln + rn)),
                "-" => Some(make_int_atom(ln - rn)),
                "*" => Some(make_int_atom(ln * rn)),
                "/" => (rn != 0).then(|| make_int_atom(ln / rn)),
                "%" => (rn != 0).then(|| make_int_atom(ln % rn)),
                "<" => Some(if ln < rn {
                    Atom::C_GBoolTrue
                } else {
                    Atom::C_GBoolFalse
                }),
                "<=" => Some(if ln <= rn {
                    Atom::C_GBoolTrue
                } else {
                    Atom::C_GBoolFalse
                }),
                ">" => Some(if ln > rn {
                    Atom::C_GBoolTrue
                } else {
                    Atom::C_GBoolFalse
                }),
                ">=" => Some(if ln >= rn {
                    Atom::C_GBoolTrue
                } else {
                    Atom::C_GBoolFalse
                }),
                "==" => Some(if ln == rn {
                    Atom::C_GBoolTrue
                } else {
                    Atom::C_GBoolFalse
                }),
                _ => None,
            }
        },
        ("concat", [lhs, rhs]) => {
            let lv = eval_ground_call_core_inner(space, lhs, memo, in_progress, depth)?;
            let rv = eval_ground_call_core_inner(space, rhs, memo, in_progress, depth)?;
            let ls = extract_string_from_atom(&lv)?;
            let rs = extract_string_from_atom(&rv)?;
            Some(make_string_atom(format!("{ls}{rs}")))
        },
        ("length", [arg]) => {
            let av = eval_ground_call_core_inner(space, arg, memo, in_progress, depth)?;
            let s = extract_string_from_atom(&av)?;
            Some(make_int_atom(s.len() as i64))
        },
        // === Collapse: collect all results into a list atom ===
        // Ref: PeTTa Answers.lean:44 — collapse = flatMap (list semantics).
        // For deterministic ground evaluation, collapse(expr) = (result).
        ("collapse", [expr]) => {
            let result = eval_ground_call_core_inner(space, expr, memo, in_progress, depth)?;
            Some(encode_cons_list(&[result]))
        },
        // === assertEqual: evaluate both sides, compare as multisets ===
        // Ref: HE stdlib.metta:1094 — evaluate both, compare_vec_no_order.
        // Uses coreGroundEval fast path for both sides (deterministic).
        ("assertEqual", [actual, expected]) => {
            let av = eval_ground_call_core_inner(space, actual, memo, in_progress, depth)?;
            let ev = eval_ground_call_core_inner(space, expected, memo, in_progress, depth)?;
            let actual_results = vec![av.clone()];
            let expected_results = vec![ev.clone()];
            if multiset_equal(&actual_results, &expected_results) {
                Some(Atom::C_ANil) // success: ()
            } else {
                let source = encode_cons_list(&[
                    make_user_atom("assertEqual"),
                    actual.clone(),
                    expected.clone(),
                ]);
                Some(make_assert_error(source, "assertion_failed"))
            }
        },
        // === assertEqualToResult: evaluate actual, compare to literal expected ===
        // Ref: HE stdlib.metta:1119 — actual is evaluated, expected is literal result list.
        ("assertEqualToResult", [actual, expected]) => {
            let av = eval_ground_call_core_inner(space, actual, memo, in_progress, depth)?;
            let expected_items = decode_cons_list(expected)?;
            let actual_results = vec![av.clone()];
            if multiset_equal(&actual_results, &expected_items) {
                Some(Atom::C_ANil) // success: ()
            } else {
                let source = encode_cons_list(&[
                    make_user_atom("assertEqualToResult"),
                    actual.clone(),
                    expected.clone(),
                ]);
                Some(make_assert_error(source, "assertion_failed"))
            }
        },
        _ => None,
    }
}

fn parse_int_token(atom: &Atom) -> Option<i64> {
    let tok = token_name_from_atom(atom)?;
    if let Some(rest) = tok.strip_prefix("C_neg_") {
        let mag = rest.parse::<i64>().ok()?;
        Some(-mag)
    } else if let Some(rest) = tok.strip_prefix("C_") {
        rest.parse::<i64>().ok()
    } else {
        tok.parse::<i64>().ok()
    }
}

fn parse_string_token(atom: &Atom) -> Option<String> {
    token_name_from_atom(atom)
}

fn make_token_atom(token: String) -> Atom {
    let fv = mettail_runtime::get_or_create_var(token);
    Atom::AVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)))
}

fn make_int_atom(n: i64) -> Atom {
    let token = if n < 0 {
        format!("C_neg_{}", n.unsigned_abs())
    } else {
        format!("C_{n}")
    };
    Atom::C_GInt(Box::new(make_token_atom(token)))
}

fn make_string_atom(s: String) -> Atom {
    Atom::C_GString(Box::new(make_token_atom(s)))
}

/// Extract a string from a C_GStringCodes(cons-list-of-char-codes) Atom.
fn decode_gstringcodes_atom(codes: &Atom) -> Option<String> {
    let mut chars = Vec::new();
    let mut cur = codes;
    loop {
        match cur {
            Atom::C_ANil => return Some(String::from_iter(chars)),
            Atom::C_ACons(ref head, ref tail) => {
                let code_str = token_name_from_atom(head)?;
                let code: u32 = if let Some(rest) = code_str.strip_prefix("C_") {
                    rest.parse().ok()?
                } else {
                    code_str.parse().ok()?
                };
                chars.push(char::from_u32(code)?);
                cur = tail;
            },
            _ => return None,
        }
    }
}

/// Extract a string from either C_GString(token) or C_GStringCodes(cons-list).
fn extract_string_from_atom(atom: &Atom) -> Option<String> {
    match atom {
        Atom::C_GString(ref tok) => parse_string_token(tok),
        Atom::C_GStringCodes(ref codes) => decode_gstringcodes_atom(codes),
        _ => None,
    }
}

/// Create a UserAtom from a string name.
fn make_user_atom(name: &str) -> Atom {
    Atom::C_UserAtom(Box::new(make_token_atom(name.to_string())))
}

/// Build a structured error atom: C_AError(source_expression, message).
fn make_assert_error(source: Atom, message: &str) -> Atom {
    Atom::C_AError(Box::new(source), Box::new(make_user_atom(message)))
}

/// Format an atom for error messages (best-effort human-readable).
#[allow(dead_code)]
fn format_core_atom(atom: &Atom) -> String {
    match atom {
        Atom::C_GInt(tok) => parse_int_token(tok)
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?int".to_string()),
        Atom::C_GBoolTrue => "True".to_string(),
        Atom::C_GBoolFalse => "False".to_string(),
        Atom::C_GString(_) | Atom::C_GStringCodes(_) => extract_string_from_atom(atom)
            .map(|s| format!("\"{}\"", s))
            .unwrap_or_else(|| "?str".to_string()),
        Atom::C_ANil => "()".to_string(),
        Atom::C_UserAtom(name) => {
            extract_string_from_atom(name).unwrap_or_else(|| "?atom".to_string())
        },
        Atom::C_AError(tag, msg) => {
            format!("(Error {} {})", format_core_atom(tag), format_core_atom(msg))
        },
        _ => {
            if let Some(items) = decode_cons_list(atom) {
                let parts: Vec<String> = items.iter().map(format_core_atom).collect();
                format!("({})", parts.join(" "))
            } else {
                format!("{:?}", atom)
            }
        },
    }
}

/// Multiset equality: order-insensitive, multiplicity-sensitive.
/// Matches HE's `compare_vec_no_order` from `hyperon-common/src/assert.rs`.
fn multiset_equal(a: &[Atom], b: &[Atom]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut used = vec![false; b.len()];
    for item in a {
        let mut found = false;
        for (i, other) in b.iter().enumerate() {
            if !used[i] && item == other {
                used[i] = true;
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

/// Relation-level snapshot helper for debugging large fixpoint runs.
pub fn relation_cardinality_snapshot(
    results: &mettail_runtime::AscentResults,
    names: &[&str],
) -> Vec<(String, usize)> {
    names
        .iter()
        .map(|name| {
            let card = results
                .custom_relations
                .get(*name)
                .map(|r| r.tuples.len())
                .unwrap_or(0);
            ((*name).to_string(), card)
        })
        .collect()
}
