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
    metta_pattern_contains_var, metta_pattern_index_key, MettaBinaryKind,
    MettaEqEntry, MettaEqMatches, MettaFamilyListForm, MettaFamilyPattern, MettaFamilySpaceIndex,
    MettaFamilySpaceIndexCache, MettaTypeEntry,
};
use std::sync::{Arc, OnceLock};

#[cfg(feature = "mork-backend")]
use crate::mork_backend::{mork_eval, SExpr as MorkSExpr};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{AscentResults, Language, MorkExecutionLimits, Rewrite, Term, TermInfo};
#[cfg(feature = "mork-backend")]
use serde::Deserialize;
#[cfg(feature = "mork-backend")]
use std::collections::{HashMap, HashSet, VecDeque};
#[cfg(feature = "mork-backend")]
use std::fs;
#[cfg(feature = "mork-backend")]
use std::hash::{Hash, Hasher};
#[cfg(feature = "mork-backend")]
use std::path::{Path, PathBuf};
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
fn hash_display_id(display: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    display.hash(&mut hasher);
    hasher.finish()
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
#[derive(Debug, Default)]
struct HeRewriteTransitionSpec {
    by_source_instr: HashMap<String, Vec<String>>,
}

#[cfg(feature = "mork-backend")]
impl HeRewriteTransitionSpec {
    fn ordered_rules_for(&self, source_instr: &str) -> Option<&[String]> {
        self.by_source_instr
            .get(source_instr)
            .map(|rules| rules.as_slice())
    }
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeTransitionSourceArtifact {
    source_instr: String,
    source_label: String,
    ordered_rules: Vec<String>,
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeTransitionSemKeyArtifact {
    source_instr_class: String,
    transition_kind: String,
    guard_family: String,
    effect_kind: String,
    dialect_ext: Option<String>,
    contracts: Vec<String>,
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeTransitionRuleArtifact {
    logical_transition_id: String,
    source_instr: String,
    source_label: String,
    rule_id: String,
    sem_key: HeTransitionSemKeyArtifact,
    priority: u64,
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct HeTransitionSpecArtifact {
    schema_version: u64,
    dialect: String,
    sources: Vec<HeTransitionSourceArtifact>,
    rules: Vec<HeTransitionRuleArtifact>,
}

#[cfg(feature = "mork-backend")]
const EXPECTED_HE_TRANSITION_SCHEMA_VERSION: u64 = 2;

#[cfg(feature = "mork-backend")]
fn fnv1a64(text: &str) -> u64 {
    const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV64_PRIME: u64 = 1_099_511_628_211;
    text.bytes()
        .fold(FNV64_OFFSET, |h, b| (h ^ (b as u64)).wrapping_mul(FNV64_PRIME))
}

#[cfg(feature = "mork-backend")]
fn transition_spec_paths(base_dir: &Path) -> (PathBuf, PathBuf) {
    (
        base_dir.join("he.transition_spec.json"),
        base_dir.join("he.transition_spec.checksum"),
    )
}

#[cfg(feature = "mork-backend")]
fn candidate_transition_spec_dirs() -> Vec<PathBuf> {
    if let Ok(from_env) = std::env::var("METTAIL_TRANSITION_SPEC_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    let mut dirs = Vec::new();
    dirs.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/transition"));
    dirs.push(PathBuf::from("artifacts/transition"));
    for prefix in ["..", "../..", "../../.."] {
        dirs.push(PathBuf::from(prefix).join("lean-projects/mettapedia/artifacts/transition"));
    }
    dirs.push(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/mettapedia/artifacts/transition"),
    );
    dirs
}

#[cfg(feature = "mork-backend")]
fn is_rule_id(rule: &str) -> bool {
    let Some(rest) = rule.strip_prefix('R') else {
        return false;
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

#[cfg(feature = "mork-backend")]
fn validate_and_index_transition_artifact(
    artifact: HeTransitionSpecArtifact,
    json_path: &Path,
) -> Result<HeRewriteTransitionSpec, String> {
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        return Err(format!(
            "invalid HE transition spec at {}: expected dialect 'he', got '{}'",
            json_path.display(),
            artifact.dialect
        ));
    }
    if artifact.sources.is_empty() {
        return Err(format!(
            "invalid HE transition spec at {}: sources cannot be empty",
            json_path.display()
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!(
            "invalid HE transition spec at {}: rules cannot be empty",
            json_path.display()
        ));
    }

    let mut rule_to_source: HashMap<String, String> = HashMap::new();
    let mut seen_transition_ids: HashSet<&str> = HashSet::new();
    for rule in &artifact.rules {
        if rule.logical_transition_id.trim().is_empty() {
            return Err(format!(
                "invalid HE transition spec at {}: logical_transition_id must be non-empty",
                json_path.display()
            ));
        }
        if !seen_transition_ids.insert(rule.logical_transition_id.as_str()) {
            return Err(format!(
                "invalid HE transition spec at {}: duplicate logical_transition_id '{}'",
                json_path.display(),
                rule.logical_transition_id
            ));
        }
        if rule.source_instr.trim().is_empty() || rule.source_label.trim().is_empty() {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' has empty source_instr/source_label",
                json_path.display(),
                rule.logical_transition_id
            ));
        }
        if !rule.source_instr.starts_with("C_") {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' source_instr '{}' must start with C_",
                json_path.display(),
                rule.logical_transition_id,
                rule.source_instr
            ));
        }
        if !is_rule_id(&rule.rule_id) {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' has invalid rule_id '{}'",
                json_path.display(),
                rule.logical_transition_id,
                rule.rule_id
            ));
        }
        if rule.sem_key.source_instr_class.trim().is_empty()
            || rule.sem_key.transition_kind.trim().is_empty()
            || rule.sem_key.guard_family.trim().is_empty()
            || rule.sem_key.effect_kind.trim().is_empty()
        {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' has incomplete sem_key",
                json_path.display(),
                rule.logical_transition_id
            ));
        }
        if rule.sem_key.contracts.is_empty() {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' sem_key.contracts cannot be empty",
                json_path.display(),
                rule.logical_transition_id
            ));
        }
        let mut seen_contracts: HashSet<&str> = HashSet::new();
        for contract in &rule.sem_key.contracts {
            if contract.trim().is_empty() {
                return Err(format!(
                    "invalid HE transition spec at {}: rule '{}' has empty sem_key contract",
                    json_path.display(),
                    rule.logical_transition_id
                ));
            }
            if !seen_contracts.insert(contract.as_str()) {
                return Err(format!(
                    "invalid HE transition spec at {}: rule '{}' has duplicate sem_key contract '{}'",
                    json_path.display(),
                    rule.logical_transition_id,
                    contract
                ));
            }
        }
        // Present for schema compatibility; allow null or a non-empty string.
        if rule
            .sem_key
            .dialect_ext
            .as_ref()
            .is_some_and(|s| s.trim().is_empty())
        {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' has empty sem_key.dialect_ext",
                json_path.display(),
                rule.logical_transition_id
            ));
        }
        let _priority = rule.priority;
        if let Some(prev_source) =
            rule_to_source.insert(rule.rule_id.clone(), rule.source_instr.clone())
        {
            if prev_source != rule.source_instr {
                return Err(format!(
                    "invalid HE transition spec at {}: rule_id '{}' mapped to multiple sources ('{}', '{}')",
                    json_path.display(),
                    rule.rule_id,
                    prev_source,
                    rule.source_instr
                ));
            }
        }
    }

    let mut by_source_instr: HashMap<String, Vec<String>> = HashMap::new();
    for source in artifact.sources {
        if source.source_instr.trim().is_empty() || source.source_label.trim().is_empty() {
            return Err(format!(
                "invalid HE transition spec at {}: source_instr/source_label must be non-empty",
                json_path.display()
            ));
        }
        if !source.source_instr.starts_with("C_") {
            return Err(format!(
                "invalid HE transition spec at {}: source_instr '{}' must start with C_",
                json_path.display(),
                source.source_instr
            ));
        }
        if source.ordered_rules.is_empty() {
            return Err(format!(
                "invalid HE transition spec at {}: '{}' must have at least one ordered rule",
                json_path.display(),
                source.source_instr
            ));
        }
        let mut seen_rules: HashSet<&str> = HashSet::new();
        for rule in &source.ordered_rules {
            if !is_rule_id(rule) {
                return Err(format!(
                    "invalid HE transition spec at {}: '{}' includes invalid rule id '{}'",
                    json_path.display(),
                    source.source_instr,
                    rule
                ));
            }
            if !seen_rules.insert(rule.as_str()) {
                return Err(format!(
                    "invalid HE transition spec at {}: '{}' has duplicate rule '{}'",
                    json_path.display(),
                    source.source_instr,
                    rule
                ));
            }
            match rule_to_source.get(rule) {
                Some(mapped_source) if mapped_source == &source.source_instr => {},
                Some(mapped_source) => {
                    return Err(format!(
                        "invalid HE transition spec at {}: '{}' lists rule '{}' but semantic rule source is '{}'",
                        json_path.display(),
                        source.source_instr,
                        rule,
                        mapped_source
                    ));
                },
                None => {
                    return Err(format!(
                        "invalid HE transition spec at {}: '{}' lists unknown rule '{}' (missing from rules[])",
                        json_path.display(),
                        source.source_instr,
                        rule
                    ));
                },
            }
        }
        if by_source_instr
            .insert(source.source_instr.clone(), source.ordered_rules)
            .is_some()
        {
            return Err(format!(
                "invalid HE transition spec at {}: duplicate source_instr '{}'",
                json_path.display(),
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
        if !by_source_instr.contains_key(required) {
            return Err(format!(
                "invalid HE transition spec at {}: missing required source '{}'",
                json_path.display(),
                required
            ));
        }
    }
    for (rule_id, source_instr) in &rule_to_source {
        let Some(ordered) = by_source_instr.get(source_instr) else {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' points to missing source '{}'",
                json_path.display(),
                rule_id,
                source_instr
            ));
        };
        if !ordered.contains(rule_id) {
            return Err(format!(
                "invalid HE transition spec at {}: rule '{}' is not referenced in ordered_rules for '{}'",
                json_path.display(),
                rule_id,
                source_instr
            ));
        }
    }

    Ok(HeRewriteTransitionSpec { by_source_instr })
}

#[cfg(feature = "mork-backend")]
fn load_transition_spec_from_paths(
    json_path: &Path,
    checksum_path: &Path,
) -> Result<HeRewriteTransitionSpec, String> {
    let json_text_raw = fs::read_to_string(json_path).map_err(|e| {
        format!("failed reading HE transition spec json {}: {}", json_path.display(), e)
    })?;
    let checksum_text_raw = fs::read_to_string(checksum_path).map_err(|e| {
        format!("failed reading HE transition spec checksum {}: {}", checksum_path.display(), e)
    })?;
    let json_text = json_text_raw.trim();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().map_err(|e| {
        format!(
            "invalid HE transition spec checksum '{}' at {}: {}",
            checksum_text,
            checksum_path.display(),
            e
        )
    })?;
    let actual_checksum = fnv1a64(json_text);
    if actual_checksum != expected_checksum {
        return Err(format!(
            "HE transition spec checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }

    let artifact: HeTransitionSpecArtifact = serde_json::from_str(json_text).map_err(|e| {
        format!("invalid HE transition spec json payload at {}: {}", json_path.display(), e)
    })?;
    if artifact.schema_version != EXPECTED_HE_TRANSITION_SCHEMA_VERSION {
        return Err(format!(
            "unsupported HE transition spec schema_version {} at {} (expected {})",
            artifact.schema_version,
            json_path.display(),
            EXPECTED_HE_TRANSITION_SCHEMA_VERSION
        ));
    }
    validate_and_index_transition_artifact(artifact, json_path)
}

#[cfg(feature = "mork-backend")]
fn load_he_rewrite_transition_spec_from_artifacts() -> Result<HeRewriteTransitionSpec, String> {
    let mut first_error: Option<String> = None;
    for dir in candidate_transition_spec_dirs() {
        let (json_path, checksum_path) = transition_spec_paths(&dir);
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_transition_spec_from_paths(&json_path, &checksum_path) {
            Ok(spec) => return Ok(spec),
            Err(err) => {
                if first_error.is_none() {
                    first_error = Some(err);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => Err(
            "missing HE transition-spec artifact: expected he.transition_spec.json/checksum (set METTAIL_TRANSITION_SPEC_DIR or run `lake env lean --run Mettapedia/Languages/MeTTa/HE/TransitionSpec.lean export <out-dir>`)"
                .to_string(),
        ),
    }
}

#[cfg(feature = "mork-backend")]
fn he_rewrite_transition_spec() -> Result<&'static HeRewriteTransitionSpec, String> {
    static SPEC: OnceLock<Result<HeRewriteTransitionSpec, String>> = OnceLock::new();
    match SPEC.get_or_init(load_he_rewrite_transition_spec_from_artifacts) {
        Ok(spec) => Ok(spec),
        Err(err) => Err(err.clone()),
    }
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

    type HeRuleHandler =
        fn(&HeStepContext<'_>, MorkExecutionLimits, &mut f64) -> Result<Vec<State>, String>;

    fn he_rule_group_metta(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_Metta(atom, ty) = ctx.instr else {
            return Ok(out);
        };
        match rule {
            "R0" if he_is_empty(atom) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            "R1" if he_is_error(atom) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            "R2" if he_type_matches_meta_or_atom(atom, ty) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            "R3" if he_needs_type_cast(atom, ty) => out.push(
                ctx.mk_state(he_instr_type_cast((**atom).clone(), (**ty).clone()), ctx.out.clone()),
            ),
            "R4" if he_needs_interp_expr(atom, ty) => {
                out.push(ctx.mk_state(
                    he_instr_interp_expr((**atom).clone(), (**ty).clone()),
                    ctx.out.clone(),
                ))
            },
            _ => {},
        }
        Ok(out)
    }

    fn he_rule_group_interp_expr(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_InterpExpr(atom, ty) = ctx.instr else {
            return Ok(out);
        };
        match rule {
            "R5" => {
                if let Some(op_type_ret_type) = find_applicable_func_type(ctx.space, atom, ty) {
                    if let Atom::C_ExprCons(op_type, ret_type) = op_type_ret_type {
                        out.push(ctx.mk_state(
                            he_instr_interp_func(
                                (**atom).clone(),
                                (*op_type).clone(),
                                (*ret_type).clone(),
                            ),
                            ctx.out.clone(),
                        ));
                    }
                }
            },
            "R6" => {
                if let Some(non_func_ty) = has_non_func_types(ctx.space, atom) {
                    if find_applicable_func_type(ctx.space, atom, &non_func_ty).is_none() {
                        out.push(
                            ctx.mk_state(he_instr_interp_tuple((**atom).clone()), ctx.out.clone()),
                        );
                    }
                }
            },
            "R7" if he_not_expression(atom) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            _ => {},
        }
        Ok(out)
    }

    fn he_rule_group_interp_func(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_InterpFunc(atom, op_type, ret_type) = ctx.instr else {
            return Ok(out);
        };
        match rule {
            "R8" => {
                if let Atom::C_ExprCons(op, args_tail) = atom.as_ref() {
                    out.push(ctx.mk_state(
                        he_instr_metta((**op).clone(), (**op_type).clone()),
                        Atom::C_KAfterOp(
                            args_tail.clone(),
                            Box::new((**op_type).clone()),
                            Box::new((**ret_type).clone()),
                            Box::new(ctx.out.clone()),
                        ),
                    ));
                }
            },
            "R9" if atom.as_ref() == &Atom::C_ExprNil => {
                out.push(ctx.mk_state(he_instr_return(Atom::C_ExprNil), ctx.out.clone()))
            },
            "R10" if he_not_expression(atom) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            _ => {},
        }
        Ok(out)
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

    fn he_rule_group_metta_call(
        rule: &str,
        ctx: &HeStepContext<'_>,
        limits: MorkExecutionLimits,
        mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_MettaCall(atom, ty) = ctx.instr else {
            return Ok(out);
        };
        match rule {
            "R36" if he_is_error(atom) => {
                out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
            },
            "R37" => {
                if let Atom::C_ExprCons(op, args_tail) = atom.as_ref() {
                    if ty.as_ref() != &Atom::C_AtomType
                        && is_executable_grounded(op.as_ref()).is_some()
                    {
                        if let Some(result) =
                            eval_grounded_dispatch((**op).clone(), (**args_tail).clone())
                        {
                            out.push(
                                ctx.mk_state(
                                    he_instr_metta(result, (**ty).clone()),
                                    ctx.out.clone(),
                                ),
                            );
                        }
                    }
                }
            },
            "R38" | "R39" => {
                if is_not_executable_grounded(atom).is_some() {
                    let equations = extract_space_equations(ctx.space)?;
                    let query = atom_to_mork_sexpr(atom)?;
                    let eval_started = Instant::now();
                    let mork_results =
                        mork_eval::run_mork_query_with_limits(&equations, &query, limits)?;
                    *mork_eval_ms += eval_started.elapsed().as_secs_f64() * 1000.0;

                    if rule == "R39" && mork_results.is_empty() {
                        out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()));
                    }
                    if rule == "R38" {
                        for rhs in mork_results {
                            out.push(ctx.mk_state(
                                he_instr_metta(mork_atom_to_he_atom(&rhs), (**ty).clone()),
                                ctx.out.clone(),
                            ));
                        }
                    }
                }
            },
            _ => {},
        }
        Ok(out)
    }

    fn he_rule_group_type_cast(
        rule: &str,
        ctx: &HeStepContext<'_>,
        _limits: MorkExecutionLimits,
        _mork_eval_ms: &mut f64,
    ) -> Result<Vec<State>, String> {
        let mut out = Vec::new();
        let Instr::C_TypeCast(atom, ty) = ctx.instr else {
            return Ok(out);
        };
        if let Some(actual) = he_type_of(ctx.space, atom) {
            match rule {
                "R40" if actual == **ty => {
                    out.push(ctx.mk_state(he_instr_return((**atom).clone()), ctx.out.clone()))
                },
                "R41" if actual != **ty => out.push(ctx.mk_state(
                    he_instr_return(Atom::C_ErrorAtom(
                        Box::new((**atom).clone()),
                        Box::new(Atom::C_BadType(Box::new((**ty).clone()), Box::new(actual))),
                    )),
                    ctx.out.clone(),
                )),
                _ => {},
            }
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

    macro_rules! he_rule_wrapper {
        ($name:ident, $group:ident, $rule:literal) => {
            fn $name(
                ctx: &HeStepContext<'_>,
                limits: MorkExecutionLimits,
                mork_eval_ms: &mut f64,
            ) -> Result<Vec<State>, String> {
                $group($rule, ctx, limits, mork_eval_ms)
            }
        };
    }

    he_rule_wrapper!(he_rule_r0, he_rule_group_metta, "R0");
    he_rule_wrapper!(he_rule_r1, he_rule_group_metta, "R1");
    he_rule_wrapper!(he_rule_r2, he_rule_group_metta, "R2");
    he_rule_wrapper!(he_rule_r3, he_rule_group_metta, "R3");
    he_rule_wrapper!(he_rule_r4, he_rule_group_metta, "R4");
    he_rule_wrapper!(he_rule_r5, he_rule_group_interp_expr, "R5");
    he_rule_wrapper!(he_rule_r6, he_rule_group_interp_expr, "R6");
    he_rule_wrapper!(he_rule_r7, he_rule_group_interp_expr, "R7");
    he_rule_wrapper!(he_rule_r8, he_rule_group_interp_func, "R8");
    he_rule_wrapper!(he_rule_r9, he_rule_group_interp_func, "R9");
    he_rule_wrapper!(he_rule_r10, he_rule_group_interp_func, "R10");
    he_rule_wrapper!(he_rule_r11, he_rule_group_return, "R11");
    he_rule_wrapper!(he_rule_r12, he_rule_group_return, "R12");
    he_rule_wrapper!(he_rule_r13, he_rule_group_return, "R13");
    he_rule_wrapper!(he_rule_r14, he_rule_group_return, "R14");
    he_rule_wrapper!(he_rule_r15, he_rule_group_return, "R15");
    he_rule_wrapper!(he_rule_r16, he_rule_group_return, "R16");
    he_rule_wrapper!(he_rule_r17, he_rule_group_return, "R17");
    he_rule_wrapper!(he_rule_r18, he_rule_group_interp_args, "R18");
    he_rule_wrapper!(he_rule_r19, he_rule_group_interp_args, "R19");
    he_rule_wrapper!(he_rule_r20, he_rule_group_return, "R20");
    he_rule_wrapper!(he_rule_r21, he_rule_group_return, "R21");
    he_rule_wrapper!(he_rule_r22, he_rule_group_return, "R22");
    he_rule_wrapper!(he_rule_r23, he_rule_group_return, "R23");
    he_rule_wrapper!(he_rule_r24, he_rule_group_return, "R24");
    he_rule_wrapper!(he_rule_r25, he_rule_group_return, "R25");
    he_rule_wrapper!(he_rule_r26, he_rule_group_return, "R26");
    he_rule_wrapper!(he_rule_r27, he_rule_group_interp_tuple, "R27");
    he_rule_wrapper!(he_rule_r28, he_rule_group_interp_tuple, "R28");
    he_rule_wrapper!(he_rule_r29, he_rule_group_return, "R29");
    he_rule_wrapper!(he_rule_r30, he_rule_group_return, "R30");
    he_rule_wrapper!(he_rule_r31, he_rule_group_return, "R31");
    he_rule_wrapper!(he_rule_r32, he_rule_group_return, "R32");
    he_rule_wrapper!(he_rule_r33, he_rule_group_return, "R33");
    he_rule_wrapper!(he_rule_r34, he_rule_group_return, "R34");
    he_rule_wrapper!(he_rule_r35, he_rule_group_return, "R35");
    he_rule_wrapper!(he_rule_r36, he_rule_group_metta_call, "R36");
    he_rule_wrapper!(he_rule_r37, he_rule_group_metta_call, "R37");
    he_rule_wrapper!(he_rule_r38, he_rule_group_metta_call, "R38");
    he_rule_wrapper!(he_rule_r39, he_rule_group_metta_call, "R39");
    he_rule_wrapper!(he_rule_r40, he_rule_group_type_cast, "R40");
    he_rule_wrapper!(he_rule_r41, he_rule_group_type_cast, "R41");
    he_rule_wrapper!(he_rule_r42, he_rule_group_return, "R42");

    fn he_rule_handler_table() -> &'static HashMap<&'static str, HeRuleHandler> {
        static TABLE: OnceLock<HashMap<&'static str, HeRuleHandler>> = OnceLock::new();
        TABLE.get_or_init(|| {
            let mut m: HashMap<&'static str, HeRuleHandler> = HashMap::new();
            m.insert("R0", he_rule_r0 as HeRuleHandler);
            m.insert("R1", he_rule_r1 as HeRuleHandler);
            m.insert("R2", he_rule_r2 as HeRuleHandler);
            m.insert("R3", he_rule_r3 as HeRuleHandler);
            m.insert("R4", he_rule_r4 as HeRuleHandler);
            m.insert("R5", he_rule_r5 as HeRuleHandler);
            m.insert("R6", he_rule_r6 as HeRuleHandler);
            m.insert("R7", he_rule_r7 as HeRuleHandler);
            m.insert("R8", he_rule_r8 as HeRuleHandler);
            m.insert("R9", he_rule_r9 as HeRuleHandler);
            m.insert("R10", he_rule_r10 as HeRuleHandler);
            m.insert("R11", he_rule_r11 as HeRuleHandler);
            m.insert("R12", he_rule_r12 as HeRuleHandler);
            m.insert("R13", he_rule_r13 as HeRuleHandler);
            m.insert("R14", he_rule_r14 as HeRuleHandler);
            m.insert("R15", he_rule_r15 as HeRuleHandler);
            m.insert("R16", he_rule_r16 as HeRuleHandler);
            m.insert("R17", he_rule_r17 as HeRuleHandler);
            m.insert("R18", he_rule_r18 as HeRuleHandler);
            m.insert("R19", he_rule_r19 as HeRuleHandler);
            m.insert("R20", he_rule_r20 as HeRuleHandler);
            m.insert("R21", he_rule_r21 as HeRuleHandler);
            m.insert("R22", he_rule_r22 as HeRuleHandler);
            m.insert("R23", he_rule_r23 as HeRuleHandler);
            m.insert("R24", he_rule_r24 as HeRuleHandler);
            m.insert("R25", he_rule_r25 as HeRuleHandler);
            m.insert("R26", he_rule_r26 as HeRuleHandler);
            m.insert("R27", he_rule_r27 as HeRuleHandler);
            m.insert("R28", he_rule_r28 as HeRuleHandler);
            m.insert("R29", he_rule_r29 as HeRuleHandler);
            m.insert("R30", he_rule_r30 as HeRuleHandler);
            m.insert("R31", he_rule_r31 as HeRuleHandler);
            m.insert("R32", he_rule_r32 as HeRuleHandler);
            m.insert("R33", he_rule_r33 as HeRuleHandler);
            m.insert("R34", he_rule_r34 as HeRuleHandler);
            m.insert("R35", he_rule_r35 as HeRuleHandler);
            m.insert("R36", he_rule_r36 as HeRuleHandler);
            m.insert("R37", he_rule_r37 as HeRuleHandler);
            m.insert("R38", he_rule_r38 as HeRuleHandler);
            m.insert("R39", he_rule_r39 as HeRuleHandler);
            m.insert("R40", he_rule_r40 as HeRuleHandler);
            m.insert("R41", he_rule_r41 as HeRuleHandler);
            m.insert("R42", he_rule_r42 as HeRuleHandler);
            m
        })
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

    let spec = he_rewrite_transition_spec()?;
    let ordered_rules = spec.ordered_rules_for(source_tag).ok_or_else(|| {
        format!(
            "HE MORK transition spec missing source instruction '{}' from Lean-generated artifact",
            source_tag
        )
    })?;

    let handlers = he_rule_handler_table();
    let ctx = HeStepContext { instr, space, out };
    let mut dedup: HashSet<(String, String)> = HashSet::new();
    let mut next: Vec<(String, State)> = Vec::new();

    for rule in ordered_rules {
        let handler = handlers.get(rule.as_str()).ok_or_else(|| {
            format!(
                "HE MORK transition handler table missing rule '{}' required by Lean artifact",
                rule
            )
        })?;
        for st in handler(&ctx, limits, mork_eval_ms)? {
            if dedup.insert((rule.clone(), format!("{}", st))) {
                next.push((rule.clone(), st));
            }
        }
    }

    Ok(next)
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

    let mut results = AscentResults::empty();
    results.all_terms.push(TermInfo {
        term_id: start_id,
        display: start_display.clone(),
        is_normal_form: false,
    });

    let mut ids_by_display: HashMap<String, u64> = HashMap::new();
    ids_by_display.insert(start_display.clone(), start_id);

    let mut queue: VecDeque<State> = VecDeque::new();
    queue.push_back(start_state);
    let mut processed: HashSet<String> = HashSet::new();
    let mut steps = 0usize;
    let mut mork_eval_ms = 0.0f64;

    while let Some(cur_state) = queue.pop_front() {
        if steps >= limits.max_steps {
            break;
        }
        let cur_display = format!("{}", cur_state);
        if !processed.insert(cur_display.clone()) {
            continue;
        }
        let cur_id = *ids_by_display
            .entry(cur_display.clone())
            .or_insert_with(|| hash_display_id(&cur_display));

        steps = steps.saturating_add(1);
        let transitions = he_native_step_state(&cur_state, limits, &mut mork_eval_ms)?;
        for (rule_name, next_state) in transitions {
            let next_display = format!("{}", next_state);
            let next_id = *ids_by_display
                .entry(next_display.clone())
                .or_insert_with(|| hash_display_id(&next_display));

            results.rewrites.push(Rewrite {
                from_id: cur_id,
                to_id: next_id,
                rule_name: Some(rule_name),
            });

            if results.all_terms.iter().all(|t| t.term_id != next_id) {
                results.all_terms.push(TermInfo {
                    term_id: next_id,
                    display: next_display.clone(),
                    is_normal_form: false,
                });
            }

            if !processed.contains(&next_display) {
                queue.push_back(next_state);
            }
        }
    }

    let mut outgoing: HashSet<u64> = HashSet::new();
    for rw in &results.rewrites {
        outgoing.insert(rw.from_id);
    }
    for term_info in &mut results.all_terms {
        term_info.is_normal_form = !outgoing.contains(&term_info.term_id);
    }

    results
        .phase_timings_ms
        .insert("mork_native_steps".to_string(), steps as f64);
    results
        .phase_timings_ms
        .insert("mork_eval_ms".to_string(), mork_eval_ms);
    if steps >= limits.max_steps {
        results
            .phase_timings_ms
            .insert("mork_native_step_cap_hit".to_string(), 1.0);
    }

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
        let spec =
            he_rewrite_transition_spec().expect("transition spec should parse from Lean export");
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
    }
}
