//! MeTTa HE (Hyperon Experimental) language backend for MeTTaIL.
//!
//! Generated from Lean OSLF pipeline:
//!   HELanguageDef.lean  → types / terms / rewrites
//!   HEPremises.lean     → premise datalog rules + builtin function table
//!
//! IMPORTANT — macro field-name hygiene:
//! The `language!` proc macro generates parser functions whose internal
//! variables include `pos`, `lhs`, `rhs`, `value`, `result`, `tokens`,
//! `min_bp`, `stack`, and `cur_bp`.  If a term constructor's field name
//! collides with any of these, the generated parser silently shadows the
//! internal variable, producing confusing type errors like
//! "expected `&mut usize`, found `Atom`".
//!
//! Renames applied here to avoid collisions:
//!   C_BadArgType  : pos   → argpos
//!   C_EqAtom      : lhs   → left,  rhs → right
//!   C_GInt        : value  → intTok
//!   C_GString     : value  → strTok
//!   C_GBool       : value  → boolTok

#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

// ═══════════════════════════════════════════════════════════════════════════
// Helper functions used by the premise rules (builtins referenced in the
// generated logic{} section).  Each corresponds to a BuiltinFn declared in
// HEPremises.lean's PremiseProgram.
// ═══════════════════════════════════════════════════════════════════════════

fn token_name_from_atom(atom: &Atom) -> Option<String> {
    match atom {
        Atom::AVar(var) => match &var.0 {
            mettail_runtime::Var::Free(fv) => fv.pretty_name.clone(),
            _ => None,
        },
        _ => None,
    }
}

fn parse_int_token(atom: &Atom) -> Option<i64> {
    let tok = token_name_from_atom(atom)?;
    if let Some(rest) = tok.strip_prefix("C_neg_") {
        rest.parse::<i64>().ok().map(|n| -n)
    } else if let Some(rest) = tok.strip_prefix("C_") {
        rest.parse::<i64>().ok()
    } else {
        tok.parse::<i64>().ok()
    }
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

fn make_bool_atom(b: bool) -> Atom {
    Atom::C_GBool(Box::new(make_token_atom(
        if b { "True" } else { "False" }.to_string(),
    )))
}

// Decode an ExprCons/ExprNil list into a Vec
fn decode_expr_list(atom: &Atom) -> Option<Vec<Atom>> {
    let mut items = Vec::new();
    let mut cur = atom;
    loop {
        match cur {
            Atom::C_ExprNil => return Some(items),
            Atom::C_ExprCons(head, tail) => {
                items.push(head.as_ref().clone());
                cur = tail.as_ref();
            }
            _ => return None,
        }
    }
}

// Walk the space's atom list looking for entries matching a predicate.
fn walk_space_atoms<F, R>(sp: &Space, mut f: F) -> Option<R>
where
    F: FnMut(&Atom) -> Option<R>,
{
    let Space::C_Space(ref atoms) = sp else {
        return None;
    };
    let mut cur = atoms.as_ref();
    loop {
        match cur {
            Atom::C_ExprNil => return None,
            Atom::C_ExprCons(head, tail) => {
                if let Some(r) = f(head.as_ref()) {
                    return Some(r);
                }
                cur = tail.as_ref();
            }
            _ => return None,
        }
    }
}

// ═══ Builtin 1: is_executable_grounded ═══
// Checks if an atom is a known grounded operator.
fn is_executable_grounded(op: &Atom) -> Option<bool> {
    match op {
        Atom::C_OpAdd
        | Atom::C_OpSub
        | Atom::C_OpMul
        | Atom::C_OpDiv
        | Atom::C_OpMod
        | Atom::C_OpLt
        | Atom::C_OpGt
        | Atom::C_OpEq => Some(true),
        _ => None,
    }
}

// ═══ Builtin 2: find_type_annotation ═══
// Walks the space's atom list to find C_TypeAnnotation(atom, ty) where atom matches.
fn find_type_annotation(atoms: Atom, atom: Atom) -> Option<Atom> {
    let mut cur = &atoms;
    loop {
        match cur {
            Atom::C_ExprNil => return None,
            Atom::C_ExprCons(head, tail) => {
                if let Atom::C_TypeAnnotation(ref a, ref ty) = head.as_ref() {
                    if a.as_ref() == &atom {
                        return Some(ty.as_ref().clone());
                    }
                }
                cur = tail.as_ref();
            }
            _ => return None,
        }
    }
}

// ═══ Builtin 3: query_equations_all (nondeterministic) ═══
// Walks the space's atom list to find ALL C_EqAtom(lhs, rhs) where lhs
// pattern-matches the given atom.  Returns Vec<Atom> of substituted rhs values.
// This is the semantic primitive behind the `eqQueryResult` Ascent relation.
fn query_equations_all(atoms: Atom, atom: Atom) -> Vec<Atom> {
    let mut results = Vec::new();
    let mut cur = &atoms;
    loop {
        match cur {
            Atom::C_ExprNil => return results,
            Atom::C_ExprCons(head, tail) => {
                if let Atom::C_EqAtom(ref lhs, ref rhs) = head.as_ref() {
                    if let Some(bindings) = he_match(lhs.as_ref(), &atom) {
                        results.push(he_subst(rhs.as_ref(), &bindings));
                    }
                }
                cur = tail.as_ref();
            }
            _ => return results,
        }
    }
}

// Cheap existence check for `noEqQuery` — avoids allocating the full Vec.
fn has_equation_match(atoms: &Atom, atom: &Atom) -> bool {
    let mut cur = atoms;
    loop {
        match cur {
            Atom::C_ExprNil => return false,
            Atom::C_ExprCons(head, tail) => {
                if let Atom::C_EqAtom(ref lhs, _) = head.as_ref() {
                    if he_match(lhs.as_ref(), atom).is_some() {
                        return true;
                    }
                }
                cur = tail.as_ref();
            }
            _ => return false,
        }
    }
}

// ═══ Builtin 4: find_applicable_func_type ═══
// For an expression (op args...), check if op has an ArrowType annotation.
// Returns (opType, retType) packed as C_ExprCons(opType, retType).
fn find_applicable_func_type(sp: Space, atom: Atom, _type: Atom) -> Option<Atom> {
    // atom should be an expression; extract the head (operator)
    let Atom::C_ExprCons(ref head, _) = atom else {
        return None;
    };
    let op = head.as_ref();

    // Look for a type annotation on the operator that is an ArrowType
    walk_space_atoms(&sp, |entry| {
        if let Atom::C_TypeAnnotation(ref a, ref ty) = entry {
            if a.as_ref() == op {
                if let Atom::C_ArrowType(ref _arg_types, ref ret_type) = ty.as_ref() {
                    // Pack as ExprCons pair for the caller to destructure
                    return Some(Atom::C_ExprCons(
                        Box::new(ty.as_ref().clone()),
                        Box::new(ret_type.as_ref().clone()),
                    ));
                }
            }
        }
        None
    })
}

// Helper: find_applicable_func_type but returns a flat (opType, retType) tuple
fn find_applicable_func_type_pair(sp: Space, atom: Atom, _type: Atom) -> Option<(Atom, Atom)> {
    let packed = find_applicable_func_type(sp, atom, _type)?;
    if let Atom::C_ExprCons(ref op_type, ref ret_type) = packed {
        Some((op_type.as_ref().clone(), ret_type.as_ref().clone()))
    } else {
        None
    }
}

// ═══ Builtin 5: has_non_func_types ═══
// Checks if any type annotation for the head of expr is NOT an ArrowType.
fn has_non_func_types(sp: Space, atom: Atom) -> Option<bool> {
    let Atom::C_ExprCons(ref head, _) = atom else {
        return None;
    };
    let op = head.as_ref();

    walk_space_atoms(&sp, |entry| {
        if let Atom::C_TypeAnnotation(ref a, ref ty) = entry {
            if a.as_ref() == op {
                if !matches!(ty.as_ref(), Atom::C_ArrowType(_, _)) {
                    return Some(true);
                }
            }
        }
        None
    })
}

// ═══ Builtin 6: eval_interp_func ═══
// Pass-through: InterpFunc is a structural step.  All dispatch (grounded ops
// AND equation lookup) happens in MettaCall via rules R11 (groundedCallResult)
// and R12 (eqQueryResult).
fn eval_interp_func(_sp: Space, atom: Atom, _op_type: Atom, _ret_type: Atom) -> Option<Atom> {
    Some(atom)
}

// ═══ Builtin 7: eval_interp_tuple ═══
// Evaluate a tuple expression by interpreting each element.
fn eval_interp_tuple(_sp: Space, atom: Atom) -> Option<Atom> {
    // For a tuple, just return the expression as-is (it's not a function call)
    // In HE, tuples are expressions that aren't function applications.
    Some(atom)
}

// ═══ Builtin 8: eval_grounded_dispatch ═══
// Dispatches a grounded call: given op and argsTail (ExprCons list of args),
// computes the result.
fn eval_grounded_dispatch(op: Atom, args_tail: Atom) -> Option<Atom> {
    let args = decode_expr_list(&args_tail)?;
    eval_grounded_op(&op, &args)
}

// Combined check: is the atom a grounded call and can we dispatch it?
fn try_grounded_dispatch(atom: &Atom) -> Option<Atom> {
    let Atom::C_ExprCons(ref op, ref args_tail) = atom else {
        return None;
    };
    is_executable_grounded(op)?;
    eval_grounded_dispatch(op.as_ref().clone(), args_tail.as_ref().clone())
}

// Core grounded operation evaluator
fn eval_grounded_op(op: &Atom, args: &[Atom]) -> Option<Atom> {
    match (op, args) {
        // Binary arithmetic: Int × Int → Int
        (Atom::C_OpAdd, [lhs, rhs])
        | (Atom::C_OpSub, [lhs, rhs])
        | (Atom::C_OpMul, [lhs, rhs])
        | (Atom::C_OpDiv, [lhs, rhs])
        | (Atom::C_OpMod, [lhs, rhs]) => {
            let ln = extract_gint(lhs)?;
            let rn = extract_gint(rhs)?;
            let result = match op {
                Atom::C_OpAdd => ln.checked_add(rn)?,
                Atom::C_OpSub => ln.checked_sub(rn)?,
                Atom::C_OpMul => ln.checked_mul(rn)?,
                Atom::C_OpDiv => {
                    if rn == 0 {
                        return None;
                    }
                    ln.checked_div(rn)?
                }
                Atom::C_OpMod => {
                    if rn == 0 {
                        return None;
                    }
                    ln.checked_rem(rn)?
                }
                _ => unreachable!(),
            };
            Some(make_int_atom(result))
        }
        // Binary comparison: Int × Int → Bool
        (Atom::C_OpLt, [lhs, rhs])
        | (Atom::C_OpGt, [lhs, rhs])
        | (Atom::C_OpEq, [lhs, rhs]) => {
            let ln = extract_gint(lhs)?;
            let rn = extract_gint(rhs)?;
            let result = match op {
                Atom::C_OpLt => ln < rn,
                Atom::C_OpGt => ln > rn,
                Atom::C_OpEq => ln == rn,
                _ => unreachable!(),
            };
            Some(make_bool_atom(result))
        }
        _ => None,
    }
}

fn extract_gint(atom: &Atom) -> Option<i64> {
    if let Atom::C_GInt(ref tok) = atom {
        parse_int_token(tok)
    } else {
        None
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Pattern matching primitives for equation lookup (eqQueryResult builtin).
//
// These implement the core semantic primitive behind `eqQueryResult` in the
// HE premise program: pattern-match an equation LHS (with C_VarAtom pattern
// variables) against a concrete atom, then substitute the matched bindings
// into the RHS.
// ═══════════════════════════════════════════════════════════════════════════

/// Extract the variable name from a `C_VarAtom(name)` pattern variable.
fn he_pat_var_name(atom: &Atom) -> Option<String> {
    match atom {
        Atom::C_VarAtom(ref name) => {
            // name may be a bare AVar token or C_SymAtom(AVar(...))
            match name.as_ref() {
                Atom::C_SymAtom(ref tok) => token_name_from_atom(tok),
                other => token_name_from_atom(other),
            }
        }
        _ => None,
    }
}

/// Recursive pattern matcher: match `pattern` against `concrete`, accumulating
/// variable bindings.  Returns true on success.
fn he_match_rec(
    pattern: &Atom,
    concrete: &Atom,
    bindings: &mut Vec<(String, Atom)>,
) -> bool {
    // Variable pattern: bind or check consistency
    if let Some(var_name) = he_pat_var_name(pattern) {
        for (k, v) in bindings.iter() {
            if *k == var_name {
                return v == concrete;
            }
        }
        bindings.push((var_name, concrete.clone()));
        return true;
    }

    // Structural recursion on ExprCons
    match (pattern, concrete) {
        (Atom::C_ExprCons(ph, pt), Atom::C_ExprCons(ch, ct)) => {
            he_match_rec(ph, ch, bindings) && he_match_rec(pt, ct, bindings)
        }
        // Everything else: exact equality
        _ => pattern == concrete,
    }
}

/// Pattern-match `pattern` against `concrete`.
/// Returns `Some(bindings)` on success, `None` on failure.
fn he_match(pattern: &Atom, concrete: &Atom) -> Option<Vec<(String, Atom)>> {
    let mut bindings = Vec::new();
    if he_match_rec(pattern, concrete, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

/// Apply a substitution (from `he_match`) to an atom, replacing `C_VarAtom`
/// occurrences with their bound values.
fn he_subst(atom: &Atom, bindings: &[(String, Atom)]) -> Atom {
    if let Some(var_name) = he_pat_var_name(atom) {
        for (k, v) in bindings {
            if *k == var_name {
                return v.clone();
            }
        }
        return atom.clone();
    }
    match atom {
        Atom::C_ExprCons(h, t) => Atom::C_ExprCons(
            Box::new(he_subst(h, bindings)),
            Box::new(he_subst(t, bindings)),
        ),
        Atom::C_EqAtom(l, r) => Atom::C_EqAtom(
            Box::new(he_subst(l, bindings)),
            Box::new(he_subst(r, bindings)),
        ),
        _ => atom.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Generated language definition from Lean export
// (ExportMeTTaHE.lean → renderLanguageFull mettaHE mettaHEPremises)
// ═══════════════════════════════════════════════════════════════════════════


// Generated language block (kept separate for safe regeneration/diffing).
include!("generated/mettahe_language_working.rs");
