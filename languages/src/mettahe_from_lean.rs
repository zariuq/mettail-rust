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
use mettail_runtime::{
    metta_pattern_contains_var, metta_pattern_index_key, MettaBinaryKind, MettaEqEntry,
    MettaEqMatches, MettaFamilyListForm, MettaFamilyPattern, MettaFamilySpaceIndex,
    MettaFamilySpaceIndexCache, MettaTypeEntry,
};
use std::sync::{Arc, OnceLock};

#[cfg(feature = "mork-backend")]
use crate::mettahe_artifacts::{
    load_mettahe_lookup_artifact, load_mettahe_rewrite_ir_artifact,
    load_mettahe_transition_artifact, LookupArtifact, RewriteIRArtifact, TransitionArtifact,
};
#[cfg(feature = "mork-backend")]
use crate::mork_backend::{mork_eval, SExpr as MorkSExpr};
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, NativeTransitionContract, NativeTransitionRuleMeta,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{
    dispatch_ordered_rules, run_transition_graph, AscentResults, Language, MorkExecutionLimits,
    Term,
};
#[cfg(feature = "mork-backend")]
use std::collections::{HashMap, HashSet};
#[cfg(feature = "mork-backend")]
use std::time::Instant;

impl PartialEq<Atom> for &Atom {
    fn eq(&self, other: &Atom) -> bool {
        **self == *other
    }
}

impl PartialEq<&Atom> for Atom {
    fn eq(&self, other: &&Atom) -> bool {
        *self == **other
    }
}

impl AsRef<Atom> for Atom {
    fn as_ref(&self) -> &Atom {
        self
    }
}

impl MettaFamilyPattern for Atom {
    fn pattern_var_name(&self) -> Option<String> {
        he_pat_var_name(self)
    }

    fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)> {
        match self {
            Atom::C_ExprCons(head, tail) => Some((MettaBinaryKind::ExprCons, head, tail)),
            Atom::C_EqAtom(left, right) => Some((MettaBinaryKind::EqAtom, left, right)),
            _ => None,
        }
    }

    fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self {
        match kind {
            MettaBinaryKind::ExprCons => Atom::C_ExprCons(Box::new(left), Box::new(right)),
            MettaBinaryKind::EqAtom => Atom::C_EqAtom(Box::new(left), Box::new(right)),
        }
    }
}

impl MettaFamilyListForm for Atom {
    fn expr_cons_parts(&self) -> Option<(&Self, &Self)> {
        match self {
            Atom::C_ExprCons(head, tail) => Some((head, tail)),
            _ => None,
        }
    }

    fn is_expr_nil(&self) -> bool {
        matches!(self, Atom::C_ExprNil)
    }
}

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
    Atom::C_GBool(Box::new(make_token_atom(if b { "True" } else { "False" }.to_string())))
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
            },
            _ => return None,
        }
    }
}

type HeSpaceIndex = MettaFamilySpaceIndex<Atom>;
type HeSpaceIndexCache = MettaFamilySpaceIndexCache<Atom, HeSpaceIndex>;

fn build_he_space_index(atoms: &Atom) -> HeSpaceIndex {
    let mut eq_entries: Vec<MettaEqEntry<Atom>> = Vec::new();
    let mut ty_entries: Vec<MettaTypeEntry<Atom>> = Vec::new();

    let mut cur = atoms;
    loop {
        match cur {
            Atom::C_ExprNil => break,
            Atom::C_ExprCons(head, tail) => {
                match head.as_ref() {
                    Atom::C_EqAtom(lhs, rhs) => {
                        eq_entries.push(MettaEqEntry {
                            lhs: lhs.as_ref().clone(),
                            rhs: rhs.as_ref().clone(),
                            has_pattern_var: metta_pattern_contains_var(lhs.as_ref()),
                            pattern_key: metta_pattern_index_key(lhs.as_ref()),
                        });
                    },
                    Atom::C_TypeAnnotation(a, ty) => {
                        let op = a.as_ref().clone();
                        let ty_val = ty.as_ref().clone();
                        let (applicable_func_type, non_func_type) = match ty.as_ref() {
                            Atom::C_ArrowType(_, ret_type) => {
                                let payload = Atom::C_ExprCons(
                                    Box::new(ty_val.clone()),
                                    Box::new(ret_type.as_ref().clone()),
                                );
                                (Some(payload), false)
                            },
                            _ => (None, true),
                        };
                        ty_entries.push(MettaTypeEntry {
                            atom: op,
                            ty: ty_val,
                            applicable_func_type,
                            non_func_type,
                        });
                    },
                    _ => {},
                }
                cur = tail.as_ref();
            },
            _ => break,
        }
    }

    MettaFamilySpaceIndex::from_entries(eq_entries, ty_entries)
}

fn he_space_index_cache() -> &'static HeSpaceIndexCache {
    static CACHE: OnceLock<HeSpaceIndexCache> = OnceLock::new();
    CACHE.get_or_init(HeSpaceIndexCache::default)
}

fn he_space_index_for_atoms(atoms: &Atom) -> Arc<HeSpaceIndex> {
    he_space_index_cache().get_or_build_with(atoms, build_he_space_index)
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

fn is_not_executable_grounded(op: &Atom) -> Option<bool> {
    if is_executable_grounded(op).is_none() {
        Some(true)
    } else {
        None
    }
}

// ═══ Builtin 2: find_type_annotation ═══
// Uses cached space index to find C_TypeAnnotation(atom, ty) where atom matches.
fn find_type_annotation(atoms: Atom, atom: &Atom) -> Option<Atom> {
    he_space_index_for_atoms(&atoms)
        .type_lookup
        .exact_values(atom)
        .and_then(|tys| tys.first().cloned())
}

// ═══ Builtin 3: query_equations_all_ref (nondeterministic) ═══
// Uses shared MeTTa-family lookup-family index over cached space index.
fn query_equations_all_ref(atoms: &Atom, atom: &Atom) -> MettaEqMatches<Atom> {
    he_space_index_for_atoms(atoms).equation_matches(atom)
}

fn query_equations_in_space(sp: &Space, atom: &Atom) -> MettaEqMatches<Atom> {
    match sp {
        Space::C_Space(atoms) => query_equations_all_ref(atoms.as_ref(), atom),
        _ => MettaEqMatches::empty(atom.clone()),
    }
}

// ═══ Builtin 4: find_applicable_func_type ═══
// For an expression (op args...), check if op has an ArrowType annotation.
// Returns (opType, retType) packed as C_ExprCons(opType, retType).
fn find_applicable_func_type<T: AsRef<Atom>>(sp: &Space, atom: &Atom, _type: T) -> Option<Atom> {
    // atom should be an expression; extract the head (operator)
    let Atom::C_ExprCons(ref head, _) = atom else {
        return None;
    };
    let op = head.as_ref().clone();
    match sp {
        Space::C_Space(atoms) => he_space_index_for_atoms(atoms.as_ref())
            .first_applicable_func_type_by_op
            .get(&op)
            .cloned(),
        _ => None,
    }
}

// ═══ Builtin 5: has_non_func_types ═══
// Checks if any type annotation for the head of expr is NOT an ArrowType.
fn has_non_func_types(sp: &Space, atom: &Atom) -> Option<Atom> {
    let Atom::C_ExprCons(ref head, _) = atom else {
        return None;
    };
    let op = head.as_ref().clone();
    match sp {
        Space::C_Space(atoms) => he_space_index_for_atoms(atoms.as_ref())
            .first_non_func_type_by_op
            .get(&op)
            .cloned(),
        _ => None,
    }
}

// ═══ Builtin 8: eval_grounded_dispatch ═══
// Dispatches a grounded call: given op and argsTail (ExprCons list of args),
// computes the result.
fn eval_grounded_dispatch(op: Atom, args_tail: Atom) -> Option<Atom> {
    let args = decode_expr_list(&args_tail)?;
    eval_grounded_op(&op, &args)
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
                },
                Atom::C_OpMod => {
                    if rn == 0 {
                        return None;
                    }
                    ln.checked_rem(rn)?
                },
                _ => unreachable!(),
            };
            Some(make_int_atom(result))
        },
        // Binary comparison: Int × Int → Bool
        (Atom::C_OpLt, [lhs, rhs]) | (Atom::C_OpGt, [lhs, rhs]) | (Atom::C_OpEq, [lhs, rhs]) => {
            let ln = extract_gint(lhs)?;
            let rn = extract_gint(rhs)?;
            let result = match op {
                Atom::C_OpLt => ln < rn,
                Atom::C_OpGt => ln > rn,
                Atom::C_OpEq => ln == rn,
                _ => unreachable!(),
            };
            Some(make_bool_atom(result))
        },
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
        },
        _ => None,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Generated language definition from Lean export
// (ExportMeTTaHE.lean → renderLanguageFull mettaHE mettaHEPremises)
// ═══════════════════════════════════════════════════════════════════════════

// Generated language block (kept separate for safe regeneration/diffing).
include!("generated/mettahe_language_working.rs");

#[cfg(feature = "mork-backend")]
fn atom_symbol_name(atom: &Atom) -> Option<String> {
    match atom {
        Atom::C_SymAtom(name) => {
            atom_symbol_name(name.as_ref()).or_else(|| token_name_from_atom(name))
        },
        Atom::AVar(_) => token_name_from_atom(atom),
        Atom::C_True => Some("True".to_string()),
        Atom::C_False => Some("False".to_string()),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn atom_to_mork_sexpr(atom: &Atom) -> Result<MorkSExpr, String> {
    match atom {
        Atom::C_ExprNil => Ok(MorkSExpr::List(vec![])),
        Atom::C_ExprCons(_, _) => {
            let mut items = Vec::new();
            let mut cur = atom;
            loop {
                match cur {
                    Atom::C_ExprNil => break,
                    Atom::C_ExprCons(head, tail) => {
                        items.push(atom_to_mork_sexpr(head.as_ref())?);
                        cur = tail.as_ref();
                    },
                    _ => {
                        return Err(format!(
                            "cannot convert improper HE list atom to MORK SExpr: {}",
                            atom
                        ));
                    },
                }
            }
            Ok(MorkSExpr::List(items))
        },
        Atom::C_SymAtom(name) => {
            let symbol = atom_symbol_name(name.as_ref())
                .ok_or_else(|| format!("cannot decode HE symbol token from {}", atom))?;
            Ok(MorkSExpr::Atom(symbol))
        },
        Atom::C_VarAtom(name) => {
            let var_name = atom_symbol_name(name.as_ref())
                .or_else(|| token_name_from_atom(name))
                .ok_or_else(|| format!("cannot decode HE variable token from {}", atom))?;
            Ok(MorkSExpr::Atom(format!("${var_name}")))
        },
        Atom::C_GInt(tok) => {
            let n = parse_int_token(tok.as_ref())
                .ok_or_else(|| format!("cannot decode HE integer token from {}", atom))?;
            Ok(MorkSExpr::Atom(n.to_string()))
        },
        Atom::C_GString(tok) => {
            let s = atom_symbol_name(tok.as_ref())
                .or_else(|| token_name_from_atom(tok.as_ref()))
                .ok_or_else(|| format!("cannot decode HE string token from {}", atom))?;
            Ok(MorkSExpr::Atom(format!("\"{s}\"")))
        },
        Atom::C_GBool(tok) => {
            let b = atom_symbol_name(tok.as_ref())
                .or_else(|| token_name_from_atom(tok.as_ref()))
                .unwrap_or_else(|| "True".to_string());
            Ok(MorkSExpr::Atom(b))
        },
        Atom::C_True => Ok(MorkSExpr::Atom("True".to_string())),
        Atom::C_False => Ok(MorkSExpr::Atom("False".to_string())),
        Atom::C_OpAdd => Ok(MorkSExpr::Atom("+".to_string())),
        Atom::C_OpSub => Ok(MorkSExpr::Atom("-".to_string())),
        Atom::C_OpMul => Ok(MorkSExpr::Atom("*".to_string())),
        Atom::C_OpDiv => Ok(MorkSExpr::Atom("/".to_string())),
        Atom::C_OpMod => Ok(MorkSExpr::Atom("%".to_string())),
        Atom::C_OpLt => Ok(MorkSExpr::Atom("<".to_string())),
        Atom::C_OpGt => Ok(MorkSExpr::Atom(">".to_string())),
        Atom::C_OpEq => Ok(MorkSExpr::Atom("==".to_string())),
        Atom::C_AtomType => Ok(MorkSExpr::Atom("__he_atom_type".to_string())),
        Atom::C_SymbolType => Ok(MorkSExpr::Atom("__he_symbol_type".to_string())),
        Atom::C_VariableType => Ok(MorkSExpr::Atom("__he_variable_type".to_string())),
        Atom::C_ExpressionType => Ok(MorkSExpr::Atom("__he_expression_type".to_string())),
        Atom::C_GroundedType => Ok(MorkSExpr::Atom("__he_grounded_type".to_string())),
        Atom::C_UndefinedType => Ok(MorkSExpr::Atom("__he_undefined_type".to_string())),
        Atom::C_Empty => Ok(MorkSExpr::Atom("__he_empty".to_string())),
        Atom::C_StackOverflow => Ok(MorkSExpr::Atom("__he_stack_overflow".to_string())),
        Atom::C_NoReturn => Ok(MorkSExpr::Atom("__he_no_return".to_string())),
        Atom::C_IncorrectNumberOfArguments => {
            Ok(MorkSExpr::Atom("__he_incorrect_number_of_arguments".to_string()))
        },
        Atom::C_ErrorAtom(source, code) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_error_atom".to_string()),
            atom_to_mork_sexpr(source.as_ref())?,
            atom_to_mork_sexpr(code.as_ref())?,
        ])),
        Atom::C_BadType(expected, actual) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_bad_type".to_string()),
            atom_to_mork_sexpr(expected.as_ref())?,
            atom_to_mork_sexpr(actual.as_ref())?,
        ])),
        Atom::C_BadArgType(argpos, expected, actual) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_bad_arg_type".to_string()),
            atom_to_mork_sexpr(argpos.as_ref())?,
            atom_to_mork_sexpr(expected.as_ref())?,
            atom_to_mork_sexpr(actual.as_ref())?,
        ])),
        Atom::C_ArrowType(arg_type, ret_type) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_arrow_type".to_string()),
            atom_to_mork_sexpr(arg_type.as_ref())?,
            atom_to_mork_sexpr(ret_type.as_ref())?,
        ])),
        Atom::C_TypeAnnotation(atom, ty) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_type_annotation".to_string()),
            atom_to_mork_sexpr(atom.as_ref())?,
            atom_to_mork_sexpr(ty.as_ref())?,
        ])),
        Atom::C_EqAtom(left, right) => Ok(MorkSExpr::List(vec![
            MorkSExpr::Atom("__he_eq_atom".to_string()),
            atom_to_mork_sexpr(left.as_ref())?,
            atom_to_mork_sexpr(right.as_ref())?,
        ])),
        _ => Err(format!("unsupported HE atom for MORK translation: {}", atom)),
    }
}

#[cfg(feature = "mork-backend")]
fn mork_atom_to_he_atom(sexpr: &MorkSExpr) -> Atom {
    match sexpr {
        MorkSExpr::List(items) => {
            if let Some(MorkSExpr::Atom(tag)) = items.first() {
                match tag.as_str() {
                    "__he_error_atom" if items.len() == 3 => {
                        return Atom::C_ErrorAtom(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                        );
                    },
                    "__he_bad_type" if items.len() == 3 => {
                        return Atom::C_BadType(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                        );
                    },
                    "__he_bad_arg_type" if items.len() == 4 => {
                        return Atom::C_BadArgType(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                            Box::new(mork_atom_to_he_atom(&items[3])),
                        );
                    },
                    "__he_arrow_type" if items.len() == 3 => {
                        return Atom::C_ArrowType(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                        );
                    },
                    "__he_type_annotation" if items.len() == 3 => {
                        return Atom::C_TypeAnnotation(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                        );
                    },
                    "__he_eq_atom" if items.len() == 3 => {
                        return Atom::C_EqAtom(
                            Box::new(mork_atom_to_he_atom(&items[1])),
                            Box::new(mork_atom_to_he_atom(&items[2])),
                        );
                    },
                    _ => {},
                }
            }
            let mut tail = Atom::C_ExprNil;
            for item in items.iter().rev() {
                let head = mork_atom_to_he_atom(item);
                tail = Atom::C_ExprCons(Box::new(head), Box::new(tail));
            }
            tail
        },
        MorkSExpr::Atom(token) => match token.as_str() {
            "True" | "true" => Atom::C_True,
            "False" | "false" => Atom::C_False,
            "+" => Atom::C_OpAdd,
            "-" => Atom::C_OpSub,
            "*" => Atom::C_OpMul,
            "/" => Atom::C_OpDiv,
            "%" => Atom::C_OpMod,
            "<" => Atom::C_OpLt,
            ">" => Atom::C_OpGt,
            "==" => Atom::C_OpEq,
            "__he_atom_type" => Atom::C_AtomType,
            "__he_symbol_type" => Atom::C_SymbolType,
            "__he_variable_type" => Atom::C_VariableType,
            "__he_expression_type" => Atom::C_ExpressionType,
            "__he_grounded_type" => Atom::C_GroundedType,
            "__he_undefined_type" => Atom::C_UndefinedType,
            "__he_empty" => Atom::C_Empty,
            "__he_stack_overflow" => Atom::C_StackOverflow,
            "__he_no_return" => Atom::C_NoReturn,
            "__he_incorrect_number_of_arguments" => Atom::C_IncorrectNumberOfArguments,
            _ => {
                if let Ok(n) = token.parse::<i64>() {
                    return make_int_atom(n);
                }
                if let Some(name) = token.strip_prefix('$') {
                    return Atom::C_VarAtom(Box::new(make_token_atom(name.to_string())));
                }
                Atom::C_SymAtom(Box::new(make_token_atom(token.clone())))
            },
        },
    }
}

#[cfg(feature = "mork-backend")]
fn mk_state(instr: Instr, space: Space, out: Atom) -> State {
    State::C_State(Box::new(instr), Box::new(space), Box::new(out))
}

#[cfg(feature = "mork-backend")]
fn he_box(atom: Atom) -> Box<Atom> {
    Box::new(atom)
}

#[cfg(feature = "mork-backend")]
fn he_instr_metta(atom: Atom, ty: Atom) -> Instr {
    Instr::C_Metta(he_box(atom), he_box(ty))
}

#[cfg(feature = "mork-backend")]
fn he_instr_interp_expr(atom: Atom, ty: Atom) -> Instr {
    Instr::C_InterpExpr(he_box(atom), he_box(ty))
}

#[cfg(feature = "mork-backend")]
fn he_instr_interp_func(atom: Atom, op_type: Atom, ret_type: Atom) -> Instr {
    Instr::C_InterpFunc(he_box(atom), he_box(op_type), he_box(ret_type))
}

#[cfg(feature = "mork-backend")]
fn he_instr_interp_args(head: Atom, rest: Atom, types: Atom) -> Instr {
    Instr::C_InterpArgs(he_box(head), he_box(rest), he_box(types))
}

#[cfg(feature = "mork-backend")]
fn he_instr_interp_tuple(atom: Atom) -> Instr {
    Instr::C_InterpTuple(he_box(atom))
}

#[cfg(feature = "mork-backend")]
fn he_instr_metta_call(atom: Atom, ty: Atom) -> Instr {
    Instr::C_MettaCall(he_box(atom), he_box(ty))
}

#[cfg(feature = "mork-backend")]
fn he_instr_type_cast(atom: Atom, ty: Atom) -> Instr {
    Instr::C_TypeCast(he_box(atom), he_box(ty))
}

#[cfg(feature = "mork-backend")]
fn he_instr_return(atom: Atom) -> Instr {
    Instr::C_Return(he_box(atom))
}

#[cfg(feature = "mork-backend")]
fn he_is_empty(atom: &Atom) -> bool {
    matches!(atom, Atom::C_Empty)
}

#[cfg(feature = "mork-backend")]
fn he_is_error(atom: &Atom) -> bool {
    matches!(atom, Atom::C_ErrorAtom(_, _))
}

#[cfg(feature = "mork-backend")]
fn he_meta_type(atom: &Atom) -> Option<Atom> {
    match atom {
        Atom::C_SymAtom(_) => Some(Atom::C_SymbolType),
        Atom::C_VarAtom(_) => Some(Atom::C_VariableType),
        Atom::C_ExprCons(_, _) | Atom::C_ExprNil => Some(Atom::C_ExpressionType),
        Atom::C_GInt(_)
        | Atom::C_GString(_)
        | Atom::C_GBool(_)
        | Atom::C_OpAdd
        | Atom::C_OpSub
        | Atom::C_OpMul
        | Atom::C_OpDiv
        | Atom::C_OpMod
        | Atom::C_OpLt
        | Atom::C_OpGt
        | Atom::C_OpEq => Some(Atom::C_GroundedType),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn he_type_matches_meta_or_atom(atom: &Atom, ty: &Atom) -> bool {
    if *ty == Atom::C_AtomType {
        return true;
    }
    match he_meta_type(atom) {
        Some(mt) => mt == *ty || mt == Atom::C_VariableType,
        None => false,
    }
}

#[cfg(feature = "mork-backend")]
fn he_type_not_matches_meta_or_atom(atom: &Atom, ty: &Atom) -> bool {
    match he_meta_type(atom) {
        Some(mt) => *ty != Atom::C_AtomType && mt != Atom::C_VariableType && mt != *ty,
        None => false,
    }
}

#[cfg(feature = "mork-backend")]
fn he_needs_type_cast(atom: &Atom, ty: &Atom) -> bool {
    ((matches!(he_meta_type(atom), Some(Atom::C_SymbolType))
        || matches!(he_meta_type(atom), Some(Atom::C_GroundedType)))
        && he_type_not_matches_meta_or_atom(atom, ty))
        || (*atom == Atom::C_ExprNil && he_type_not_matches_meta_or_atom(atom, ty))
}

#[cfg(feature = "mork-backend")]
fn he_needs_interp_expr(atom: &Atom, ty: &Atom) -> bool {
    matches!(he_meta_type(atom), Some(Atom::C_ExpressionType))
        && he_type_not_matches_meta_or_atom(atom, ty)
}

#[cfg(feature = "mork-backend")]
fn he_not_expression(atom: &Atom) -> bool {
    matches!(he_meta_type(atom), Some(mt) if mt != Atom::C_ExpressionType)
}

#[cfg(feature = "mork-backend")]
fn he_func_arg_types(op_type: &Atom) -> Option<Atom> {
    match op_type {
        Atom::C_ArrowType(arg_types, _) => Some((**arg_types).clone()),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn he_type_of(space: &Space, atom: &Atom) -> Option<Atom> {
    match space {
        Space::C_Space(atoms) => find_type_annotation((**atoms).clone(), atom),
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn he_changed_to_empty(orig: &Atom, new: &Atom) -> bool {
    he_is_empty(new) && new != orig
}

#[cfg(feature = "mork-backend")]
fn he_changed_to_error(orig: &Atom, new: &Atom) -> bool {
    he_is_error(new) && new != orig
}

#[cfg(feature = "mork-backend")]
fn extract_space_equations(space: &Space) -> Result<Vec<(MorkSExpr, MorkSExpr)>, String> {
    let space_atoms = match space {
        Space::C_Space(space_atoms) => space_atoms,
        _ => {
            return Err(format!(
                "HE MORK backend expects C_Space(...) for state space, got: {}",
                space
            ));
        },
    };

    let mut equations: Vec<(MorkSExpr, MorkSExpr)> = Vec::new();
    let mut cur = space_atoms.as_ref();
    loop {
        match cur {
            Atom::C_ExprNil => break,
            Atom::C_ExprCons(head, tail) => {
                if let Atom::C_EqAtom(lhs, rhs) = head.as_ref() {
                    equations.push((
                        atom_to_mork_sexpr(lhs.as_ref())?,
                        atom_to_mork_sexpr(rhs.as_ref())?,
                    ));
                }
                cur = tail.as_ref();
            },
            _ => {
                return Err(format!(
                    "HE MORK backend expected C_Space to contain proper ExprCons/ExprNil list, got {}",
                    cur
                ));
            },
        }
    }
    Ok(equations)
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeRuleSemantics {
    MettaEmpty,
    MettaError,
    MettaTypeMatch,
    MettaTypeCast,
    MettaExpression,
    InterpExprFuncType,
    InterpExprTupleType,
    InterpExprNotExpr,
    InterpFuncStart,
    InterpFuncNil,
    InterpFuncNotExpr,
    ReturnAfterOpEmpty,
    ReturnAfterOpError,
    ReturnAfterOpNoArgs,
    ReturnAfterOpEvalArgs,
    ReturnAfterArgsEmpty,
    ReturnAfterArgsError,
    ReturnAfterArgsCall,
    InterpArgsTyped,
    InterpArgsUndef,
    ReturnArgHeadEmpty,
    ReturnArgHeadError,
    ReturnArgHeadRestNil,
    ReturnArgHeadRecurse,
    ReturnArgTailEmpty,
    ReturnArgTailError,
    ReturnArgTailCons,
    InterpTupleNil,
    InterpTupleStartCons,
    ReturnTupleHeadEmpty,
    ReturnTupleHeadError,
    ReturnTupleHeadTailNil,
    ReturnTupleHeadRecurse,
    ReturnTupleTailEmpty,
    ReturnTupleTailError,
    ReturnTupleTailCons,
    MettaCallError,
    MettaCallGrounded,
    MettaCallEquation,
    MettaCallNoMatch,
    TypeCastMatch,
    TypeCastMismatch,
    ReturnFinalize,
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone)]
struct HeRewriteIRRule {
    source_instr: String,
    priority: u64,
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Default, Clone)]
struct HeRewriteIRSpec {
    by_rule_id: HashMap<String, HeRewriteIRRule>,
}

#[cfg(feature = "mork-backend")]
impl HeRewriteIRSpec {
    fn rule(&self, rule_id: &str) -> Option<&HeRewriteIRRule> {
        self.by_rule_id.get(rule_id)
    }
}

#[cfg(feature = "mork-backend")]
#[derive(Debug)]
struct HeRewriteContract {
    transition: NativeTransitionContract,
    rewrite_ir: HeRewriteIRSpec,
}

#[cfg(feature = "mork-backend")]
fn is_rule_id(rule: &str) -> bool {
    let Some(rest) = rule.strip_prefix('R') else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

#[cfg(feature = "mork-backend")]
fn he_semantics_for(logical_transition_id: &str) -> Result<HeRuleSemantics, String> {
    match logical_transition_id {
        "C_Metta:M_Empty" => Ok(HeRuleSemantics::MettaEmpty),
        "C_Metta:M_Error" => Ok(HeRuleSemantics::MettaError),
        "C_Metta:M_TypeMatch" => Ok(HeRuleSemantics::MettaTypeMatch),
        "C_Metta:M_SymbolOrGrounded" => Ok(HeRuleSemantics::MettaTypeCast),
        "C_Metta:M_Expression" => Ok(HeRuleSemantics::MettaExpression),
        "C_InterpExpr:IE_FuncType" => Ok(HeRuleSemantics::InterpExprFuncType),
        "C_InterpExpr:IE_TupleType" => Ok(HeRuleSemantics::InterpExprTupleType),
        "C_InterpExpr:IE_NotExpr" => Ok(HeRuleSemantics::InterpExprNotExpr),
        "C_InterpFunc:IF_Start" => Ok(HeRuleSemantics::InterpFuncStart),
        "C_InterpFunc:IF_Nil" => Ok(HeRuleSemantics::InterpFuncNil),
        "C_InterpFunc:IF_NotExpr" => Ok(HeRuleSemantics::InterpFuncNotExpr),
        "C_Return:IF_AfterOp_Empty" => Ok(HeRuleSemantics::ReturnAfterOpEmpty),
        "C_Return:IF_AfterOp_Error" => Ok(HeRuleSemantics::ReturnAfterOpError),
        "C_Return:IF_AfterOp_NoArgs" => Ok(HeRuleSemantics::ReturnAfterOpNoArgs),
        "C_Return:IF_AfterOp_EvalArgs" => Ok(HeRuleSemantics::ReturnAfterOpEvalArgs),
        "C_Return:IF_AfterArgs_Empty" => Ok(HeRuleSemantics::ReturnAfterArgsEmpty),
        "C_Return:IF_AfterArgs_Error" => Ok(HeRuleSemantics::ReturnAfterArgsError),
        "C_Return:IF_AfterArgs_Call" => Ok(HeRuleSemantics::ReturnAfterArgsCall),
        "C_InterpArgs:IA_Start_Typed" => Ok(HeRuleSemantics::InterpArgsTyped),
        "C_InterpArgs:IA_Start_Undef" => Ok(HeRuleSemantics::InterpArgsUndef),
        "C_Return:IA_Head_Empty" => Ok(HeRuleSemantics::ReturnArgHeadEmpty),
        "C_Return:IA_Head_Error" => Ok(HeRuleSemantics::ReturnArgHeadError),
        "C_Return:IA_Head_RestNil" => Ok(HeRuleSemantics::ReturnArgHeadRestNil),
        "C_Return:IA_Head_Recurse" => Ok(HeRuleSemantics::ReturnArgHeadRecurse),
        "C_Return:IA_Tail_Empty" => Ok(HeRuleSemantics::ReturnArgTailEmpty),
        "C_Return:IA_Tail_Error" => Ok(HeRuleSemantics::ReturnArgTailError),
        "C_Return:IA_Tail_Cons" => Ok(HeRuleSemantics::ReturnArgTailCons),
        "C_InterpTuple:IT_Nil" => Ok(HeRuleSemantics::InterpTupleNil),
        "C_InterpTuple:IT_StartCons" => Ok(HeRuleSemantics::InterpTupleStartCons),
        "C_Return:IT_Head_Empty" => Ok(HeRuleSemantics::ReturnTupleHeadEmpty),
        "C_Return:IT_Head_Error" => Ok(HeRuleSemantics::ReturnTupleHeadError),
        "C_Return:IT_Head_TailNil" => Ok(HeRuleSemantics::ReturnTupleHeadTailNil),
        "C_Return:IT_Head_Recurse" => Ok(HeRuleSemantics::ReturnTupleHeadRecurse),
        "C_Return:IT_Tail_Empty" => Ok(HeRuleSemantics::ReturnTupleTailEmpty),
        "C_Return:IT_Tail_Error" => Ok(HeRuleSemantics::ReturnTupleTailError),
        "C_Return:IT_Tail_Cons" => Ok(HeRuleSemantics::ReturnTupleTailCons),
        "C_MettaCall:MC_Error" => Ok(HeRuleSemantics::MettaCallError),
        "C_MettaCall:MC_Grounded" => Ok(HeRuleSemantics::MettaCallGrounded),
        "C_MettaCall:MC_Equation" => Ok(HeRuleSemantics::MettaCallEquation),
        "C_MettaCall:MC_NoMatch" => Ok(HeRuleSemantics::MettaCallNoMatch),
        "C_TypeCast:TC_Match" => Ok(HeRuleSemantics::TypeCastMatch),
        "C_TypeCast:TC_Mismatch" => Ok(HeRuleSemantics::TypeCastMismatch),
        "C_Return:R_Done" => Ok(HeRuleSemantics::ReturnFinalize),
        _ => Err(format!(
            "unknown HE logical transition id '{}' in transition artifact",
            logical_transition_id
        )),
    }
}

#[cfg(feature = "mork-backend")]
fn validate_he_transition_artifact(artifact: &TransitionArtifact) -> Result<(), String> {
    let mut seen_transition_ids: HashSet<&str> = HashSet::new();
    let mut seen_rule_sources: HashMap<String, String> = HashMap::new();
    for rule in &artifact.rules {
        if rule.logical_transition_id.trim().is_empty() {
            return Err(
                "invalid HE transition spec: logical_transition_id must be non-empty".to_string()
            );
        }
        if !seen_transition_ids.insert(rule.logical_transition_id.as_str()) {
            return Err(format!(
                "invalid HE transition spec: duplicate logical_transition_id '{}'",
                rule.logical_transition_id
            ));
        }
        if rule.source_instr.trim().is_empty() || rule.source_label.trim().is_empty() {
            return Err(format!(
                "invalid HE transition spec: rule '{}' has empty source_instr/source_label",
                rule.logical_transition_id
            ));
        }
        if !rule.source_instr.starts_with("C_") {
            return Err(format!(
                "invalid HE transition spec: rule '{}' source_instr '{}' must start with C_",
                rule.logical_transition_id, rule.source_instr
            ));
        }
        if !is_rule_id(&rule.rule_id) {
            return Err(format!(
                "invalid HE transition spec: rule '{}' has invalid rule_id '{}'",
                rule.logical_transition_id, rule.rule_id
            ));
        }
        if rule.sem_key.source_instr_class.trim().is_empty()
            || rule.sem_key.transition_kind.trim().is_empty()
            || rule.sem_key.guard_family.trim().is_empty()
            || rule.sem_key.effect_kind.trim().is_empty()
        {
            return Err(format!(
                "invalid HE transition spec: rule '{}' has incomplete sem_key",
                rule.logical_transition_id
            ));
        }
        if rule.sem_key.contracts.is_empty() {
            return Err(format!(
                "invalid HE transition spec: rule '{}' sem_key.contracts cannot be empty",
                rule.logical_transition_id
            ));
        }
        let mut seen_contracts: HashSet<&str> = HashSet::new();
        for contract in &rule.sem_key.contracts {
            if contract.trim().is_empty() {
                return Err(format!(
                    "invalid HE transition spec: rule '{}' has empty sem_key contract",
                    rule.logical_transition_id
                ));
            }
            if !seen_contracts.insert(contract.as_str()) {
                return Err(format!(
                    "invalid HE transition spec: rule '{}' has duplicate sem_key contract '{}'",
                    rule.logical_transition_id, contract
                ));
            }
        }
        if rule
            .sem_key
            .dialect_ext
            .as_ref()
            .is_some_and(|s| s.trim().is_empty())
        {
            return Err(format!(
                "invalid HE transition spec: rule '{}' has empty sem_key.dialect_ext",
                rule.logical_transition_id
            ));
        }
        let _ = he_semantics_for(&rule.logical_transition_id)?;
        if let Some(prev_source) =
            seen_rule_sources.insert(rule.rule_id.clone(), rule.source_instr.clone())
        {
            if prev_source != rule.source_instr {
                return Err(format!(
                    "invalid HE transition spec: rule_id '{}' mapped to multiple sources ('{}', '{}')",
                    rule.rule_id, prev_source, rule.source_instr
                ));
            }
        }
    }

    let mut seen_source_instrs: HashSet<&str> = HashSet::new();
    for source in &artifact.sources {
        if source.source_instr.trim().is_empty() || source.source_label.trim().is_empty() {
            return Err("invalid HE transition spec: source_instr/source_label must be non-empty"
                .to_string());
        }
        if !source.source_instr.starts_with("C_") {
            return Err(format!(
                "invalid HE transition spec: source_instr '{}' must start with C_",
                source.source_instr
            ));
        }
        if source.ordered_rules.is_empty() {
            return Err(format!(
                "invalid HE transition spec: '{}' must have at least one ordered rule",
                source.source_instr
            ));
        }
        let mut seen_rules: HashSet<&str> = HashSet::new();
        for rule in &source.ordered_rules {
            if !is_rule_id(rule) {
                return Err(format!(
                    "invalid HE transition spec: '{}' includes invalid rule id '{}'",
                    source.source_instr, rule
                ));
            }
            if !seen_rules.insert(rule.as_str()) {
                return Err(format!(
                    "invalid HE transition spec: '{}' has duplicate rule '{}'",
                    source.source_instr, rule
                ));
            }
            match seen_rule_sources.get(rule) {
                Some(mapped_source) if mapped_source == &source.source_instr => {},
                Some(mapped_source) => {
                    return Err(format!(
                        "invalid HE transition spec: '{}' lists rule '{}' but semantic rule source is '{}'",
                        source.source_instr, rule, mapped_source
                    ));
                },
                None => {
                    return Err(format!(
                        "invalid HE transition spec: '{}' lists unknown rule '{}' (missing from rules[])",
                        source.source_instr, rule
                    ));
                },
            }
        }
        if !seen_source_instrs.insert(source.source_instr.as_str()) {
            return Err(format!(
                "invalid HE transition spec: duplicate source_instr '{}'",
                source.source_instr
            ));
        }
    }

    for required in [
        "C_Metta",
        "C_InterpExpr",
        "C_InterpFunc",
        "C_InterpArgs",
        "C_InterpTuple",
        "C_MettaCall",
        "C_TypeCast",
        "C_Return",
    ] {
        if !seen_source_instrs.contains(required) {
            return Err(format!(
                "invalid HE transition spec: missing required source '{}'",
                required
            ));
        }
    }
    Ok(())
}

#[cfg(feature = "mork-backend")]
fn validate_and_index_rewrite_ir_artifact(
    artifact: RewriteIRArtifact,
) -> Result<HeRewriteIRSpec, String> {
    let mut by_rule_id: HashMap<String, HeRewriteIRRule> = HashMap::new();
    for rule in artifact.rules {
        if !is_rule_id(&rule.rule_id) {
            return Err(format!("invalid HE rewrite-ir: invalid rule_id '{}'", rule.rule_id));
        }
        if rule.rule_name.trim().is_empty() {
            return Err(format!(
                "invalid HE rewrite-ir: rule '{}' has empty rule_name",
                rule.rule_id
            ));
        }
        if !rule.source_instr.starts_with("C_") {
            return Err(format!(
                "invalid HE rewrite-ir: rule '{}' source_instr '{}' must start with C_",
                rule.rule_id, rule.source_instr
            ));
        }
        if rule.source_label.trim().is_empty() {
            return Err(format!(
                "invalid HE rewrite-ir: rule '{}' has empty source_label",
                rule.rule_id
            ));
        }
        if rule.left_repr.trim().is_empty() || rule.right_repr.trim().is_empty() {
            return Err(format!(
                "invalid HE rewrite-ir: rule '{}' has empty left_repr/right_repr",
                rule.rule_id
            ));
        }
        let mut seen_premises: HashSet<&str> = HashSet::new();
        for rel in &rule.premise_relations {
            if rel.trim().is_empty() {
                return Err(format!(
                    "invalid HE rewrite-ir: rule '{}' has empty premise relation",
                    rule.rule_id
                ));
            }
            if !seen_premises.insert(rel.as_str()) {
                return Err(format!(
                    "invalid HE rewrite-ir: rule '{}' has duplicate premise relation '{}'",
                    rule.rule_id, rel
                ));
            }
        }

        let indexed = HeRewriteIRRule {
            source_instr: rule.source_instr,
            priority: rule.priority,
        };
        if by_rule_id.insert(rule.rule_id.clone(), indexed).is_some() {
            return Err(format!("invalid HE rewrite-ir: duplicate rule_id '{}'", rule.rule_id));
        }
    }

    Ok(HeRewriteIRSpec { by_rule_id })
}

#[cfg(feature = "mork-backend")]
fn validate_transition_rewrite_alignment(
    transition: &NativeTransitionContract,
    rewrite_ir: &HeRewriteIRSpec,
) -> Result<(), String> {
    for (source_instr, ordered_rules) in transition.ordered_rule_map() {
        for rule_id in ordered_rules {
            let Some(meta) = rewrite_ir.rule(rule_id) else {
                return Err(format!(
                    "HE rewrite contract mismatch: transition source '{}' references missing rewrite_ir rule '{}'",
                    source_instr, rule_id
                ));
            };
            if meta.source_instr != *source_instr {
                return Err(format!(
                    "HE rewrite contract mismatch: transition source '{}' references rule '{}' but rewrite_ir maps it to '{}'",
                    source_instr, rule_id, meta.source_instr
                ));
            }
        }
    }

    let mut by_source_from_ir: HashMap<String, Vec<(u64, String)>> = HashMap::new();
    for (rule_id, meta) in &rewrite_ir.by_rule_id {
        by_source_from_ir
            .entry(meta.source_instr.clone())
            .or_default()
            .push((meta.priority, rule_id.clone()));
    }
    for rules in by_source_from_ir.values_mut() {
        rules.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    }

    for (source_instr, ordered_rules) in transition.ordered_rule_map() {
        let ir_rules = by_source_from_ir.get(source_instr).ok_or_else(|| {
            format!(
                "HE rewrite contract mismatch: transition source '{}' missing from rewrite_ir",
                source_instr
            )
        })?;
        let ir_ordered: Vec<String> = ir_rules.iter().map(|(_, rid)| rid.clone()).collect();
        if ir_ordered != *ordered_rules {
            return Err(format!(
                "HE rewrite contract mismatch: ordered rules differ for '{}': transition={:?} rewrite_ir={:?}",
                source_instr, ordered_rules, ir_ordered
            ));
        }
    }
    Ok(())
}

#[cfg(feature = "mork-backend")]
fn load_he_rewrite_contract_from_artifacts() -> Result<HeRewriteContract, String> {
    let transition_artifact = load_mettahe_transition_artifact()?;
    validate_he_transition_artifact(&transition_artifact)?;
    let lookup_artifact = load_mettahe_lookup_artifact()?;
    let rewrite_ir_artifact = load_mettahe_rewrite_ir_artifact()?;
    let rewrite_ir = validate_and_index_rewrite_ir_artifact(rewrite_ir_artifact.clone())?;
    let transition = build_native_transition_contract(
        "MeTTaHE",
        transition_artifact,
        lookup_artifact,
        rewrite_ir_artifact,
        |lookup| {
            let Some(eq_query) = lookup.families.iter().find(|f| f.family == "eqQuery") else {
                return Err("HE lookup-plan missing required eqQuery family".to_string());
            };
            if eq_query.raw_relation != "eqQueryRaw"
                || eq_query.has_relation != "eqQueryHas"
                || eq_query.result_relation.as_deref() != Some("eqQueryResult")
            {
                return Err(format!(
                    "HE lookup-plan eqQuery family has unexpected relation names: raw='{}' has='{}' result={:?}",
                    eq_query.raw_relation, eq_query.has_relation, eq_query.result_relation
                ));
            }
            if !eq_query.contracts.no_false_negatives
                || !eq_query.contracts.stratified_negation_safe
            {
                return Err(
                    "HE lookup-plan eqQuery family must be no-false-negatives and stratified-negation-safe"
                        .to_string(),
                );
            }
            Ok(())
        },
    )?;
    validate_transition_rewrite_alignment(&transition, &rewrite_ir)?;
    Ok(HeRewriteContract { transition, rewrite_ir })
}

#[cfg(feature = "mork-backend")]
fn he_rewrite_contract() -> Result<&'static HeRewriteContract, String> {
    static CONTRACT: OnceLock<Result<HeRewriteContract, String>> = OnceLock::new();
    match CONTRACT.get_or_init(load_he_rewrite_contract_from_artifacts) {
        Ok(contract) => Ok(contract),
        Err(err) => Err(err.clone()),
    }
}

#[cfg(feature = "mork-backend")]
pub fn he_transition_artifact_rule_ids() -> Result<Vec<String>, String> {
    let contract = he_rewrite_contract()?;
    let mut ids: Vec<String> = contract
        .transition
        .ordered_rule_map()
        .values()
        .flat_map(|rules| rules.iter().cloned())
        .collect();
    ids.sort();
    ids.dedup();
    Ok(ids)
}

#[cfg(feature = "mork-backend")]
fn he_instr_transition_tag(instr: &Instr) -> &'static str {
    match instr {
        Instr::C_Metta(_, _) => "C_Metta",
        Instr::C_InterpExpr(_, _) => "C_InterpExpr",
        Instr::C_InterpFunc(_, _, _) => "C_InterpFunc",
        Instr::C_InterpArgs(_, _, _) => "C_InterpArgs",
        Instr::C_InterpTuple(_) => "C_InterpTuple",
        Instr::C_MettaCall(_, _) => "C_MettaCall",
        Instr::C_TypeCast(_, _) => "C_TypeCast",
        Instr::C_Return(_) => "C_Return",
        Instr::C_Done => "C_Done",
        _ => "C_Unknown",
    }
}

#[cfg(feature = "mork-backend")]
pub fn run_mettahe_mork_backend(term: &dyn Term) -> Result<AscentResults, String> {
    run_mettahe_mork_backend_with_limits(term, MorkExecutionLimits::default())
}

#[cfg(feature = "mork-backend")]
fn he_native_step_state(
    state: &State,
    limits: MorkExecutionLimits,
    mork_eval_ms: &mut f64,
) -> Result<Vec<(String, State)>, String> {
    struct HeStepContext<'a> {
        instr: &'a Instr,
        space: &'a Space,
        out: &'a Atom,
    }

    impl HeStepContext<'_> {
        fn mk_state(&self, instr: Instr, out: Atom) -> State {
            mk_state(instr, self.space.clone(), out)
        }
    }

    fn he_rule_metta_empty(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Metta(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_is_empty(atom) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_error(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Metta(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_is_error(atom) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_type_match(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Metta(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_type_matches_meta_or_atom(atom, ty) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_type_cast(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Metta(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_needs_type_cast(atom, ty) {
            return Ok(vec![ctx.mk_state(
                he_instr_type_cast((**atom).clone(), (**ty).clone()),
                ctx.out.clone(),
            )]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_expression(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Metta(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_needs_interp_expr(atom, ty) {
            return Ok(vec![ctx.mk_state(
                he_instr_interp_expr((**atom).clone(), (**ty).clone()),
                ctx.out.clone(),
            )]);
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_expr_func_type(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpExpr(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Some(op_type_ret_type) = find_applicable_func_type(ctx.space, atom, ty) {
            if let Atom::C_ExprCons(op_type, ret_type) = op_type_ret_type {
                return Ok(vec![ctx.mk_state(
                    he_instr_interp_func((**atom).clone(), (*op_type).clone(), (*ret_type).clone()),
                    ctx.out.clone(),
                )]);
            }
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_expr_tuple_type(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpExpr(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Some(non_func_ty) = has_non_func_types(ctx.space, atom) {
            if find_applicable_func_type(ctx.space, atom, &non_func_ty).is_none() {
                return Ok(vec![ctx.mk_state(
                    he_instr_interp_tuple((**atom).clone()),
                    ctx.out.clone(),
                )]);
            }
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_expr_not_expr(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpExpr(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_not_expression(atom) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_func_start(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpFunc(atom, op_type, ret_type) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Atom::C_ExprCons(op, args_tail) = atom.as_ref() {
            return Ok(vec![ctx.mk_state(
                he_instr_metta((**op).clone(), (**op_type).clone()),
                Atom::C_KAfterOp(
                    args_tail.clone(),
                    Box::new((**op_type).clone()),
                    Box::new((**ret_type).clone()),
                    Box::new(ctx.out.clone()),
                ),
            )]);
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_func_nil(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpFunc(atom, _, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if atom.as_ref() == &Atom::C_ExprNil {
            return Ok(vec![ctx.mk_state(he_instr_return(Atom::C_ExprNil), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_interp_func_not_expr(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_InterpFunc(atom, _, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_not_expression(atom) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_call_error(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_MettaCall(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_is_error(atom) {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_call_grounded(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_MettaCall(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Atom::C_ExprCons(op, args_tail) = atom.as_ref() {
            if ty.as_ref() != &Atom::C_AtomType && is_executable_grounded(op.as_ref()).is_some() {
                if let Some(result) = eval_grounded_dispatch((**op).clone(), (**args_tail).clone())
                {
                    return Ok(vec![ctx.mk_state(
                        he_instr_metta(result, (**ty).clone()),
                        ctx.out.clone(),
                    )]);
                }
            }
        }
        Ok(Vec::new())
    }

    fn he_rule_metta_call_equation(
        ctx: &HeStepContext<'_>,
        limits: MorkExecutionLimits,
        mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let Instr::C_MettaCall(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if is_not_executable_grounded(atom).is_none() {
            return Ok(Vec::new());
        }
        let equations = extract_space_equations(ctx.space)?;
        let query = atom_to_mork_sexpr(atom)?;
        let eval_started = Instant::now();
        let mork_results = mork_eval::run_mork_query_with_limits(&equations, &query, limits)?;
        *mork_eval_ms += eval_started.elapsed().as_secs_f64() * 1000.0;

        Ok(mork_results
            .into_iter()
            .map(|rhs| {
                ctx.mk_state(
                    he_instr_metta(mork_atom_to_he_atom(&rhs), (**ty).clone()),
                    ctx.out.clone(),
                )
            })
            .collect())
    }

    fn he_rule_metta_call_no_match(
        ctx: &HeStepContext<'_>,
        limits: MorkExecutionLimits,
        mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let Instr::C_MettaCall(atom, _) = ctx.instr else {
            return Ok(Vec::new());
        };
        if is_not_executable_grounded(atom).is_none() {
            return Ok(Vec::new());
        }
        let equations = extract_space_equations(ctx.space)?;
        let query = atom_to_mork_sexpr(atom)?;
        let eval_started = Instant::now();
        let mork_results = mork_eval::run_mork_query_with_limits(&equations, &query, limits)?;
        *mork_eval_ms += eval_started.elapsed().as_secs_f64() * 1000.0;
        if mork_results.is_empty() {
            return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_type_cast_match(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_TypeCast(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Some(actual) = he_type_of(ctx.space, atom) {
            if actual == **ty {
                return Ok(vec![ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone())]);
            }
        }
        Ok(Vec::new())
    }

    fn he_rule_type_cast_mismatch(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_TypeCast(atom, ty) = ctx.instr else {
            return Ok(Vec::new());
        };
        if let Some(actual) = he_type_of(ctx.space, atom) {
            if actual != **ty {
                return Ok(vec![ctx.mk_state(
                    he_instr_return(Atom::C_ErrorAtom(
                        Box::new((**atom).clone()),
                        Box::new(Atom::C_BadType(Box::new((**ty).clone()), Box::new(actual))),
                    )),
                    ctx.out.clone(),
                )]);
            }
        }
        Ok(Vec::new())
    }

    fn he_rule_return_finalize(ctx: &HeStepContext<'_>) -> Result<Vec<State>, String> {
        let Instr::C_Return(result) = ctx.instr else {
            return Ok(Vec::new());
        };
        if he_is_empty(ctx.out) {
            return Ok(vec![ctx.mk_state(Instr::C_Done, (**result).clone())]);
        }
        Ok(Vec::new())
    }

    fn he_rule_group_interp_args(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_InterpArgs(head, rest, types) = ctx.instr else {
            return Ok(out);
        };
        match (rule, types.as_ref()) {
            ("R18", Atom::C_ExprCons(ty, type_rest)) => out.push(ctx.mk_state(
                he_instr_metta((**head).clone(), (**ty).clone()),
                Atom::C_KArgTail(
                    Box::new((**head).clone()),
                    Box::new((**rest).clone()),
                    Box::new((**type_rest).clone()),
                    Box::new(ctx.out.clone()),
                ),
            )),
            ("R19", Atom::C_ExprNil) => out.push(ctx.mk_state(
                he_instr_metta((**head).clone(), Atom::C_UndefinedType),
                Atom::C_KArgTail(
                    Box::new((**head).clone()),
                    Box::new((**rest).clone()),
                    Box::new(Atom::C_ExprNil),
                    Box::new(ctx.out.clone()),
                ),
            )),
            _ => {},
        }
        Ok(out)
    }

    fn he_rule_group_interp_tuple(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_InterpTuple(atom) = ctx.instr else {
            return Ok(out);
        };
        match (rule, atom.as_ref()) {
            ("R27", Atom::C_ExprNil) => {
                out.push(ctx.mk_state(he_instr_return(Atom::C_ExprNil), ctx.out.clone()))
            },
            ("R28", Atom::C_ExprCons(head, tail)) => out.push(ctx.mk_state(
                he_instr_metta((**head).clone(), Atom::C_UndefinedType),
                Atom::C_KTupleTail(Box::new((**tail).clone()), Box::new(ctx.out.clone())),
            )),
            _ => {},
        }
        Ok(out)
    }

    fn he_rule_group_return(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_Return(result) = ctx.instr else {
            return Ok(out);
        };

        match rule {
            "R42" if he_is_empty(ctx.out) => {
                out.push(ctx.mk_state(Instr::C_Done, (**result).clone()));
            },
            "R11" | "R12" | "R13" | "R14" => {
                if let Atom::C_KAfterOp(args_tail, op_type, ret_type, k) = ctx.out {
                    match rule {
                        "R11" if he_is_empty(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R12" if he_is_error(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R13"
                            if he_meta_type(result).is_some()
                                && args_tail.as_ref() == &Atom::C_ExprNil =>
                        {
                            out.push(ctx.mk_state(
                                he_instr_metta_call(
                                    Atom::C_ExprCons(
                                        Box::new((**result).clone()),
                                        Box::new(Atom::C_ExprNil),
                                    ),
                                    (**ret_type).clone(),
                                ),
                                (**k).clone(),
                            ));
                        },
                        "R14" => {
                            if let Atom::C_ExprCons(arg_head, arg_rest) = args_tail.as_ref() {
                                if he_meta_type(result).is_some() {
                                    if let Some(arg_types) = he_func_arg_types(op_type.as_ref()) {
                                        out.push(ctx.mk_state(
                                            he_instr_interp_args(
                                                (**arg_head).clone(),
                                                (**arg_rest).clone(),
                                                arg_types,
                                            ),
                                            Atom::C_KAfterArgs(
                                                Box::new((**result).clone()),
                                                Box::new((**ret_type).clone()),
                                                Box::new((**k).clone()),
                                            ),
                                        ));
                                    }
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            "R15" | "R16" | "R17" => {
                if let Atom::C_KAfterArgs(h, ret_type, k) = ctx.out {
                    match rule {
                        "R15" if he_is_empty(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R16" if he_is_error(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R17" if he_meta_type(result).is_some() => {
                            out.push(ctx.mk_state(
                                he_instr_metta_call(
                                    Atom::C_ExprCons(
                                        Box::new((**h).clone()),
                                        Box::new((**result).clone()),
                                    ),
                                    (**ret_type).clone(),
                                ),
                                (**k).clone(),
                            ));
                        },
                        _ => {},
                    }
                }
            },
            "R20" | "R21" | "R22" | "R23" => {
                if let Atom::C_KArgTail(orig_head, rest, types, k) = ctx.out {
                    match rule {
                        "R20" if he_changed_to_empty(orig_head, result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R21" if he_changed_to_error(orig_head, result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R22"
                            if he_meta_type(result).is_some()
                                && rest.as_ref() == &Atom::C_ExprNil =>
                        {
                            out.push(ctx.mk_state(
                                he_instr_return(Atom::C_ExprCons(
                                    Box::new((**result).clone()),
                                    Box::new(Atom::C_ExprNil),
                                )),
                                (**k).clone(),
                            ));
                        },
                        "R23" => {
                            if let Atom::C_ExprCons(next_arg, next_rest) = rest.as_ref() {
                                if he_meta_type(result).is_some() {
                                    out.push(ctx.mk_state(
                                        he_instr_interp_args(
                                            (**next_arg).clone(),
                                            (**next_rest).clone(),
                                            (**types).clone(),
                                        ),
                                        Atom::C_KArgCons(
                                            Box::new((**result).clone()),
                                            Box::new((**k).clone()),
                                        ),
                                    ));
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            "R24" | "R25" | "R26" => {
                if let Atom::C_KArgCons(h, k) = ctx.out {
                    match rule {
                        "R24" if he_is_empty(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R25" if he_is_error(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R26" if he_meta_type(result).is_some() => {
                            out.push(ctx.mk_state(
                                he_instr_return(Atom::C_ExprCons(
                                    Box::new((**h).clone()),
                                    Box::new((**result).clone()),
                                )),
                                (**k).clone(),
                            ));
                        },
                        _ => {},
                    }
                }
            },
            "R29" | "R30" | "R31" | "R32" => {
                if let Atom::C_KTupleTail(tail, k) = ctx.out {
                    match rule {
                        "R29" if he_is_empty(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R30" if he_is_error(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R31"
                            if he_meta_type(result).is_some()
                                && tail.as_ref() == &Atom::C_ExprNil =>
                        {
                            out.push(ctx.mk_state(
                                he_instr_return(Atom::C_ExprCons(
                                    Box::new((**result).clone()),
                                    Box::new(Atom::C_ExprNil),
                                )),
                                (**k).clone(),
                            ));
                        },
                        "R32" => {
                            if let Atom::C_ExprCons(t_head, t_tail) = tail.as_ref() {
                                if he_meta_type(result).is_some() {
                                    out.push(ctx.mk_state(
                                        he_instr_interp_tuple(Atom::C_ExprCons(
                                            Box::new((**t_head).clone()),
                                            Box::new((**t_tail).clone()),
                                        )),
                                        Atom::C_KTupleCons(
                                            Box::new((**result).clone()),
                                            Box::new((**k).clone()),
                                        ),
                                    ));
                                }
                            }
                        },
                        _ => {},
                    }
                }
            },
            "R33" | "R34" | "R35" => {
                if let Atom::C_KTupleCons(h, k) = ctx.out {
                    match rule {
                        "R33" if he_is_empty(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R34" if he_is_error(result) => {
                            out.push(
                                ctx.mk_state(he_instr_return((**result).clone()), (**k).clone()),
                            );
                        },
                        "R35" if he_meta_type(result).is_some() => {
                            out.push(ctx.mk_state(
                                he_instr_return(Atom::C_ExprCons(
                                    Box::new((**h).clone()),
                                    Box::new((**result).clone()),
                                )),
                                (**k).clone(),
                            ));
                        },
                        _ => {},
                    }
                }
            },
            _ => {},
        }

        Ok(out)
    }

    fn he_apply_rule_semantics(
        meta: &NativeTransitionRuleMeta,
        ctx: &HeStepContext<'_>,
        limits: MorkExecutionLimits,
        mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        match he_semantics_for(&meta.logical_transition_id)? {
            HeRuleSemantics::MettaEmpty => he_rule_metta_empty(ctx),
            HeRuleSemantics::MettaError => he_rule_metta_error(ctx),
            HeRuleSemantics::MettaTypeMatch => he_rule_metta_type_match(ctx),
            HeRuleSemantics::MettaTypeCast => he_rule_metta_type_cast(ctx),
            HeRuleSemantics::MettaExpression => he_rule_metta_expression(ctx),
            HeRuleSemantics::InterpExprFuncType => he_rule_interp_expr_func_type(ctx),
            HeRuleSemantics::InterpExprTupleType => he_rule_interp_expr_tuple_type(ctx),
            HeRuleSemantics::InterpExprNotExpr => he_rule_interp_expr_not_expr(ctx),
            HeRuleSemantics::InterpFuncStart => he_rule_interp_func_start(ctx),
            HeRuleSemantics::InterpFuncNil => he_rule_interp_func_nil(ctx),
            HeRuleSemantics::InterpFuncNotExpr => he_rule_interp_func_not_expr(ctx),
            HeRuleSemantics::ReturnAfterOpEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterOpError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterOpNoArgs => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterOpEvalArgs => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterArgsEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterArgsError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnAfterArgsCall => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::InterpArgsTyped => {
                he_rule_group_interp_args(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::InterpArgsUndef => {
                he_rule_group_interp_args(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgHeadEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgHeadError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgHeadRestNil => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgHeadRecurse => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgTailEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgTailError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnArgTailCons => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::InterpTupleNil => {
                he_rule_group_interp_tuple(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::InterpTupleStartCons => {
                he_rule_group_interp_tuple(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleHeadEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleHeadError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleHeadTailNil => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleHeadRecurse => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleTailEmpty => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleTailError => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::ReturnTupleTailCons => {
                he_rule_group_return(meta.rule_id.as_str(), ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::MettaCallError => he_rule_metta_call_error(ctx),
            HeRuleSemantics::MettaCallGrounded => he_rule_metta_call_grounded(ctx),
            HeRuleSemantics::MettaCallEquation => {
                he_rule_metta_call_equation(ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::MettaCallNoMatch => {
                he_rule_metta_call_no_match(ctx, limits, mork_eval_ms)
            },
            HeRuleSemantics::TypeCastMatch => he_rule_type_cast_match(ctx),
            HeRuleSemantics::TypeCastMismatch => he_rule_type_cast_mismatch(ctx),
            HeRuleSemantics::ReturnFinalize => he_rule_return_finalize(ctx),
        }
    }

    let (instr, space, out) = match state {
        State::C_State(instr, space, out) => (instr.as_ref(), space.as_ref(), out.as_ref()),
        _ => {
            return Err(format!(
                "HE MORK native state machine expects C_State(...), got {}",
                state
            ));
        },
    };
    let source_tag = he_instr_transition_tag(instr);
    if source_tag == "C_Done" {
        return Ok(Vec::new());
    }

    let contract = he_rewrite_contract()?;
    let ordered_rules = contract
        .transition
        .ordered_rules_for(source_tag)
        .ok_or_else(|| {
            format!(
            "HE MORK transition spec missing source instruction '{}' from Lean-generated artifact",
            source_tag
        )
        })?;

    let ctx = HeStepContext { instr, space, out };
    dispatch_ordered_rules(
        ordered_rules,
        |rule| {
            let transition_meta = contract.transition.rule(rule).cloned().ok_or_else(|| {
                format!("HE transition-spec is missing rule metadata for '{}'", rule)
            })?;
            if transition_meta.source_instr != source_tag {
                return Err(format!(
                    "HE transition-spec mismatch: rule '{}' maps to '{}' but active source is '{}'",
                    rule, transition_meta.source_instr, source_tag
                ));
            }

            let rewrite_meta = contract.rewrite_ir.rule(rule).ok_or_else(|| {
                format!("HE rewrite-ir is missing rule '{}' required by transition spec", rule)
            })?;
            if rewrite_meta.source_instr != source_tag {
                return Err(format!(
                    "HE rewrite-ir mismatch: rule '{}' maps to '{}' but active source is '{}'",
                    rule, rewrite_meta.source_instr, source_tag
                ));
            }
            Ok(transition_meta)
        },
        |_rule, meta| he_apply_rule_semantics(meta, &ctx, limits, mork_eval_ms),
    )
}

#[cfg(feature = "mork-backend")]
fn run_mettahe_native_state_graph(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let wrapped = term.as_any().downcast_ref::<MeTTaHETerm>().ok_or_else(|| {
        "HE MORK backend expects MeTTaHE parsed core term wrapper (MeTTaHETerm)".to_string()
    })?;
    let start_state = match &wrapped.0 {
        MeTTaHETermInner::State(state) => state.clone(),
        _ => {
            return Err(format!(
                "HE MORK backend expects top-level State term, got wrapper variant: {}",
                wrapped
            ));
        },
    };

    let start_display = format!("{}", term);
    let start_id = term.term_id();

    let mut mork_eval_ms = 0.0f64;
    let mut results =
        run_transition_graph(start_state, &start_display, start_id, limits, |state| {
            he_native_step_state(state, limits, &mut mork_eval_ms)
        })?;
    results
        .phase_timings_ms
        .insert("mork_eval_ms".to_string(), mork_eval_ms);
    Ok(results)
}

#[cfg(feature = "mork-backend")]
pub fn run_mettahe_mork_backend_with_limits(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let started = Instant::now();
    let mut results = run_mettahe_native_state_graph(term, limits)?;
    results
        .phase_timings_ms
        .insert("mork_native_state_ms".to_string(), started.elapsed().as_secs_f64() * 1000.0);
    Ok(results)
}

#[cfg(all(test, feature = "mork-backend"))]
mod tests {
    use super::*;

    #[test]
    fn he_rewrite_transition_spec_tracks_generated_rule_sources() {
        let contract =
            he_rewrite_contract().expect("rewrite contract should parse from Lean exports");
        let spec = &contract.transition;
        assert_eq!(
            spec.ordered_rules_for("C_Metta")
                .expect("C_Metta rules should be present")
                .first()
                .map(String::as_str),
            Some("R0")
        );
        assert!(spec
            .ordered_rules_for("C_InterpExpr")
            .expect("C_InterpExpr rules should be present")
            .contains(&"R5".to_string()));
        assert!(spec
            .ordered_rules_for("C_MettaCall")
            .expect("C_MettaCall rules should be present")
            .contains(&"R38".to_string()));
        assert!(spec
            .ordered_rules_for("C_Return")
            .expect("C_Return rules should be present")
            .contains(&"R42".to_string()));
        let metta_call_rules = spec
            .ordered_rules_for("C_MettaCall")
            .expect("C_MettaCall rules should be present");
        assert_eq!(
            metta_call_rules,
            &["R36".to_string(), "R37".to_string(), "R38".to_string(), "R39".to_string()]
        );
        assert!(
            !spec
                .ordered_rules_for("C_Metta")
                .expect("C_Metta rules should be present")
                .contains(&"R38".to_string()),
            "C_MettaCall-only rule should not be allowed for C_Metta source states"
        );
        let r38 = contract
            .rewrite_ir
            .rule("R38")
            .expect("rewrite-ir should include rule R38");
        assert_eq!(r38.source_instr, "C_MettaCall");
    }
}
