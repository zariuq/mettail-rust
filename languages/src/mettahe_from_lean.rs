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
use mettail_runtime::Language;
use mettail_runtime::{
    metta_bubble_changed_to_empty_if, metta_bubble_changed_to_error_if,
    metta_bubble_empty_to_continuation_if, metta_bubble_error_to_continuation_if,
    metta_continue_to_state_if_meta_result, metta_continue_with_expr_nil_tail_if_meta_result,
    metta_continue_with_expr_tail_if_meta_result, metta_eval_grounded_dispatch,
    metta_func_arg_types, metta_has_meta_type, metta_is_empty, metta_is_error,
    metta_is_executable_grounded, metta_make_bad_type_error, metta_needs_interp_expr,
    metta_needs_type_cast, metta_not_expression, metta_pattern_contains_var,
    metta_pattern_index_key, metta_return_cons_expr_to_continuation_if_meta_result,
    metta_return_singleton_expr_to_continuation_if_meta_result,
    metta_return_singleton_expr_to_continuation_if_meta_result_and_nil_tail,
    metta_return_to_out_if, metta_step_expr_cons_head_rest_to_state, metta_step_expr_nil_to_state,
    metta_step_head_rest_to_state, metta_step_to_same_out_state, metta_step_to_same_out_state_if,
    metta_step_to_same_out_state_if_some, metta_type_matches_meta_or_atom, MettaBinaryKind,
    MettaEqEntry, MettaEqMatches, MettaFamilyControl, MettaFamilyGrounded, MettaFamilyListForm,
    MettaFamilyPattern, MettaFamilySpaceContainer, MettaFamilySpaceIndex,
    MettaFamilySpaceIndexCache, MettaFamilyTyping, MettaGroundedOpKind, MettaTypeEntry,
    MettaTypeLookupService,
};
use std::sync::{Arc, OnceLock};

use crate::artifact_contract::PatternNode;
use crate::rewrite_template::{parse_runtime_term, CPrefixConstructorCodec, ConstructorCodec};

#[cfg(feature = "mork-backend")]
use crate::mettahe_artifacts::{
    load_mettahe_lookup_artifact, load_mettahe_rewrite_ir_artifact,
    load_mettahe_transition_artifact, LookupArtifact, RewriteIRArtifact, TransitionArtifact,
};
#[cfg(feature = "mork-backend")]
use crate::artifact_contract::RewriteIRRule;
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, cached_contract_result, dispatch_active_source_step,
    NativeTransitionContract, NativeTransitionRuleMeta,
};
#[cfg(feature = "mork-backend")]
use crate::rewrite_template::{
    bind_var, execute_rule_to_patterns, resolve_query_arg, ResolvedQueryArg,
    RewritePremiseEvaluator, TemplateBindings,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{
    hash_display_id, metta_match, metta_subst, run_native_term_graph_with_timing,
    run_transition_graph, AscentResults, MorkExecutionLimits, Term,
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

impl MettaFamilyGrounded for Atom {
    fn token_name(&self) -> Option<String> {
        token_name_from_atom(self)
    }

    fn make_token_atom(token: String) -> Self {
        let fv = mettail_runtime::get_or_create_var(token);
        Atom::AVar(mettail_runtime::OrdVar(mettail_runtime::Var::Free(fv)))
    }

    fn make_grounded_int(token: Self) -> Self {
        Atom::C_GInt(Box::new(token))
    }

    fn make_grounded_bool(token: Self) -> Self {
        Atom::C_GBool(Box::new(token))
    }

    fn grounded_int_token(&self) -> Option<&Self> {
        match self {
            Atom::C_GInt(tok) => Some(tok.as_ref()),
            _ => None,
        }
    }

    fn executable_grounded_kind(&self) -> Option<MettaGroundedOpKind> {
        match self {
            Atom::C_OpAdd => Some(MettaGroundedOpKind::Add),
            Atom::C_OpSub => Some(MettaGroundedOpKind::Sub),
            Atom::C_OpMul => Some(MettaGroundedOpKind::Mul),
            Atom::C_OpDiv => Some(MettaGroundedOpKind::Div),
            Atom::C_OpMod => Some(MettaGroundedOpKind::Mod),
            Atom::C_OpLt => Some(MettaGroundedOpKind::Lt),
            Atom::C_OpGt => Some(MettaGroundedOpKind::Gt),
            Atom::C_OpEq => Some(MettaGroundedOpKind::Eq),
            _ => None,
        }
    }
}

impl MettaFamilyTyping for Atom {
    fn meta_type(&self) -> Option<Self> {
        match self {
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

    fn atom_type() -> Self {
        Atom::C_AtomType
    }

    fn variable_type() -> Self {
        Atom::C_VariableType
    }

    fn expression_type() -> Self {
        Atom::C_ExpressionType
    }

    fn symbol_type() -> Self {
        Atom::C_SymbolType
    }

    fn grounded_type() -> Self {
        Atom::C_GroundedType
    }

    fn arrow_arg_types(&self) -> Option<Self> {
        match self {
            Atom::C_ArrowType(arg_types, _) => Some((**arg_types).clone()),
            _ => None,
        }
    }
}

impl MettaFamilyControl for Atom {
    fn is_empty_atom(&self) -> bool {
        matches!(self, Atom::C_Empty)
    }

    fn is_error_atom(&self) -> bool {
        matches!(self, Atom::C_ErrorAtom(_, _))
    }

    fn make_bad_type_error(atom: Self, expected: Self, actual: Self) -> Self {
        Atom::C_ErrorAtom(
            Box::new(atom),
            Box::new(Atom::C_BadType(Box::new(expected), Box::new(actual))),
        )
    }
}

impl MettaFamilySpaceContainer<Atom> for Space {
    fn space_atoms(&self) -> Option<&Atom> {
        match self {
            Space::C_Space(atoms) => Some(atoms.as_ref()),
            _ => None,
        }
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

fn he_type_lookup_service_for_atoms(atoms: &Atom) -> MettaTypeLookupService<Atom> {
    he_space_index_cache().type_lookup_service_with(atoms, build_he_space_index)
}

// ═══ Builtin 1: is_executable_grounded ═══
// Checks if an atom is a known grounded operator.
fn is_executable_grounded(op: &Atom) -> Option<bool> {
    metta_is_executable_grounded(op).then_some(true)
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
    he_type_lookup_service_for_atoms(&atoms).find_type_annotation(atom)
}

fn query_equations_in_space(sp: &Space, atom: &Atom) -> MettaEqMatches<Atom> {
    he_space_index_cache().equation_matches_in_space(sp, atom, build_he_space_index)
}

// ═══ Builtin 4: find_applicable_func_type ═══
// For an expression (op args...), check if op has an ArrowType annotation.
// Returns (opType, retType) packed as C_ExprCons(opType, retType).
fn find_applicable_func_type<T: AsRef<Atom>>(sp: &Space, atom: &Atom, _type: T) -> Option<Atom> {
    he_space_index_cache().first_applicable_func_type_for_expr_in_space(
        sp,
        atom,
        build_he_space_index,
    )
}

// ═══ Builtin 5: has_non_func_types ═══
// Checks if any type annotation for the head of expr is NOT an ArrowType.
fn has_non_func_types(sp: &Space, atom: &Atom) -> Option<Atom> {
    he_space_index_cache().first_non_func_type_for_expr_in_space(sp, atom, build_he_space_index)
}

// ═══ Builtin 6: check_no_type_at_all ═══
// Succeeds when an expression head has no explicit type annotation in the current space.
fn check_no_type_at_all(sp: &Space, atom: &Atom) -> Option<()> {
    match atom {
        Atom::C_ExprCons(op, _) if he_type_of(sp, op.as_ref()).is_none() => Some(()),
        _ => None,
    }
}

// ═══ Builtin 8: eval_grounded_dispatch ═══
// Dispatches a grounded call: given op and argsTail (ExprCons list of args),
// computes the result.
fn eval_grounded_dispatch(op: Atom, args_tail: Atom) -> Option<Atom> {
    metta_eval_grounded_dispatch(op, args_tail)
}

fn parseSwitchMinimalCallArgs(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let (scrutinee, raw_cases) = he_pattern_parse_switch_minimal(&node)?;
    Some(Atom::C_ExprCons(
        Box::new(he_pattern_node_to_atom(&scrutinee).ok()?),
        Box::new(he_pattern_node_to_atom(&raw_cases).ok()?),
    ))
}

fn parseCaseCallArgs(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let (scrutinee, raw_cases) = he_pattern_parse_case(&node)?;
    Some(Atom::C_ExprCons(
        Box::new(he_pattern_node_to_atom(&scrutinee).ok()?),
        Box::new(he_pattern_node_to_atom(&raw_cases).ok()?),
    ))
}

fn parseAssertCallArg(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let asserted = he_pattern_parse_assert(&node)?;
    he_pattern_node_to_atom(&asserted).ok()
}

fn selectSwitchTemplate(scrutinee: &Atom, rawCases: &Atom) -> Vec<Atom> {
    let scrutinee_node = match he_atom_to_pattern_node(scrutinee) {
        Ok(node) => node,
        Err(_) => return Vec::new(),
    };
    let raw_cases_node = match he_atom_to_pattern_node(rawCases) {
        Ok(node) => node,
        Err(_) => return Vec::new(),
    };
    he_pattern_select_switch_templates(&scrutinee_node, &raw_cases_node)
        .into_iter()
        .filter_map(|tmpl| he_pattern_node_to_atom(&tmpl).ok())
        .collect()
}

fn checkIsReducible(atom: &Atom) -> Option<()> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    if he_pattern_sym_name(&node) != Some("NotReducible")
        && !matches!(
            node,
            PatternNode::Apply { ref ctor, ref args }
                if ctor == "SymAtom" && args.len() == 1
                    && matches!(
                        &args[0],
                        PatternNode::Apply { ctor: n, args: a } if a.is_empty() && n == "NotReducible"
                    )
        )
    {
        Some(())
    } else {
        None
    }
}

fn checkIsNotReducible(atom: &Atom) -> Option<()> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    if matches!(
        node,
        PatternNode::Apply { ref ctor, ref args }
            if ctor == "SymAtom" && args.len() == 1
                && matches!(
                    &args[0],
                    PatternNode::Apply { ctor: n, args: a } if a.is_empty() && n == "NotReducible"
                )
    ) {
        Some(())
    } else {
        None
    }
}

fn buildAssertError(asserted: &Atom, assertedVal: &Atom) -> Option<Atom> {
    let asserted_node = he_atom_to_pattern_node(asserted).ok()?;
    let asserted_val_node = he_atom_to_pattern_node(assertedVal).ok()?;
    let err = he_pattern_mk_assert_error(&asserted_node, &asserted_val_node);
    he_pattern_node_to_atom(&err).ok()
}

fn parseSuperposElements(atom: &Atom) -> Vec<Atom> {
    let node = match he_atom_to_pattern_node(atom) {
        Ok(node) => node,
        Err(_) => return Vec::new(),
    };
    he_pattern_parse_superpose_elements(&node)
        .unwrap_or_default()
        .into_iter()
        .filter_map(|elem| he_pattern_node_to_atom(&elem).ok())
        .collect()
}

fn checkSuperposeEmpty(atom: &Atom) -> Option<()> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    he_pattern_is_superpose_empty(&node).then_some(())
}

fn parseMatchCallArgs(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let (pattern, template) = he_pattern_parse_match_call(&node)?;
    Some(Atom::C_ExprCons(
        Box::new(he_pattern_node_to_atom(&pattern).ok()?),
        Box::new(he_pattern_node_to_atom(&template).ok()?),
    ))
}

fn spacePatternQuery(pattern: &Atom, template: &Atom) -> Vec<Atom> {
    let _ = pattern;
    let _ = template;
    // The generated Ascent path does not currently thread the active Space
    // through this builtin. MORK uses the explicit template-premise evaluator.
    Vec::new()
}

fn checkSpaceNoMatch(pattern: &Atom) -> Option<()> {
    let _ = pattern;
    None
}

fn parseUnifyCallArgs(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let (target, pattern, success, failure) = he_pattern_parse_unify_call(&node)?;
    Some(Atom::C_ExprCons(
        Box::new(he_pattern_node_to_atom(&target).ok()?),
        Box::new(Atom::C_ExprCons(
            Box::new(he_pattern_node_to_atom(&pattern).ok()?),
            Box::new(Atom::C_ExprCons(
                Box::new(he_pattern_node_to_atom(&success).ok()?),
                Box::new(he_pattern_node_to_atom(&failure).ok()?),
            )),
        )),
    ))
}

fn localPatternMatch(target: &Atom, pattern: &Atom, success: &Atom) -> Option<Atom> {
    let target_node = he_atom_to_pattern_node(target).ok()?;
    let pattern_node = he_atom_to_pattern_node(pattern).ok()?;
    let success_node = he_atom_to_pattern_node(success).ok()?;
    let bindings = he_pattern_match(&pattern_node, &target_node)?;
    let result = he_pattern_subst(&success_node, &bindings);
    he_pattern_node_to_atom(&result).ok()
}

fn checkLocalNoMatch(target: &Atom, pattern: &Atom) -> Option<()> {
    let target_node = he_atom_to_pattern_node(target).ok()?;
    let pattern_node = he_atom_to_pattern_node(pattern).ok()?;
    he_pattern_match(&pattern_node, &target_node).is_none().then_some(())
}

fn parseCollapseCallArg(atom: &Atom) -> Option<Atom> {
    let node = he_atom_to_pattern_node(atom).ok()?;
    let expr = he_pattern_parse_collapse_call(&node)?;
    he_pattern_node_to_atom(&expr).ok()
}

fn evalCollapseBind(expr: &Atom, _ty: &Atom) -> Option<Atom> {
    let _ = expr;
    // The generated Ascent path does not currently thread the active Space
    // and execution limits through this builtin. MORK uses the explicit
    // template-premise evaluator with nested graph execution.
    None
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

fn he_type_of(space: &Space, atom: &Atom) -> Option<Atom> {
    he_space_index_cache().find_type_annotation_in_space(space, atom, build_he_space_index)
}

#[cfg(feature = "mork-backend")]
#[derive(Debug, Default, Clone)]
struct HeRewriteIRSpec {
    by_rule_id: HashMap<String, RewriteIRRule>,
}

#[cfg(feature = "mork-backend")]
impl HeRewriteIRSpec {
    fn rule(&self, rule_id: &str) -> Option<&RewriteIRRule> {
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
fn is_known_he_logical_transition_id(logical_transition_id: &str) -> bool {
    matches!(
        logical_transition_id,
        "C_Metta:M_Empty"
            | "C_Metta:M_Error"
            | "C_Metta:M_TypeMatch"
            | "C_Metta:M_SymbolOrGrounded"
            | "C_Metta:M_Expression"
            | "C_InterpExpr:IE_FuncType"
            | "C_InterpExpr:IE_TupleType"
            | "C_InterpExpr:IE_NoType"
            | "C_InterpExpr:IE_NotExpr"
            | "C_InterpFunc:IF_Start"
            | "C_InterpFunc:IF_Nil"
            | "C_InterpFunc:IF_NotExpr"
            | "C_Return:IF_AfterOp_Empty"
            | "C_Return:IF_AfterOp_Error"
            | "C_Return:IF_AfterOp_NoArgs"
            | "C_Return:IF_AfterOp_EvalArgs"
            | "C_Return:IF_AfterArgs_Empty"
            | "C_Return:IF_AfterArgs_Error"
            | "C_Return:IF_AfterArgs_Call"
            | "C_InterpArgs:IA_Start_Typed"
            | "C_InterpArgs:IA_Start_Undef"
            | "C_Return:IA_Head_Empty"
            | "C_Return:IA_Head_Error"
            | "C_Return:IA_Head_RestNil"
            | "C_Return:IA_Head_Recurse"
            | "C_Return:IA_Tail_Empty"
            | "C_Return:IA_Tail_Error"
            | "C_Return:IA_Tail_Cons"
            | "C_InterpTuple:IT_Nil"
            | "C_InterpTuple:IT_StartCons"
            | "C_Return:IT_Head_Empty"
            | "C_Return:IT_Head_Error"
            | "C_Return:IT_Head_TailNil"
            | "C_Return:IT_Head_Recurse"
            | "C_Return:IT_Tail_Empty"
            | "C_Return:IT_Tail_Error"
            | "C_Return:IT_Tail_Cons"
            | "C_MettaCall:MC_Error"
            | "C_MettaCall:MC_Grounded"
            | "C_MettaCall:MC_Equation"
            | "C_MettaCall:MC_NoMatch"
            | "C_TypeCast:TC_Match"
            | "C_TypeCast:TC_Mismatch"
            | "C_Return:R_Done"
            | "C_MettaCall:MC_SwitchMinimal_Start"
            | "C_MettaCall:MC_Assert_Start"
            | "C_MettaCall:MC_Case_Start"
            | "C_Return:MC_SwitchMinimal_Match"
            | "C_Return:MC_SwitchMinimal_NoMatch"
            | "C_Return:MC_Assert_True"
            | "C_Return:MC_Assert_NotTrue"
            // Minimal instructions
            | "C_MettaCall:MC_Superpose"
            | "C_MettaCall:MC_Superpose_Empty"
            | "C_MettaCall:MC_Match"
            | "C_MettaCall:MC_Match_Empty"
            | "C_MettaCall:MC_Unify_Match"
            | "C_MettaCall:MC_Unify_NoMatch"
            | "C_MettaCall:MC_Collapse"
    )
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
        if !is_known_he_logical_transition_id(&rule.logical_transition_id) {
            return Err(format!(
                "unknown HE logical transition id '{}' in transition artifact",
                rule.logical_transition_id
            ));
        }
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
    let mut by_rule_id: HashMap<String, RewriteIRRule> = HashMap::new();
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
        if rule.lhs.is_none() || rule.rhs.is_none() {
            return Err(format!(
                "invalid HE rewrite-ir: rule '{}' missing structured lhs/rhs in schema v2",
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

        let rule_id = rule.rule_id.clone();
        if by_rule_id.insert(rule_id.clone(), rule).is_some() {
            return Err(format!("invalid HE rewrite-ir: duplicate rule_id '{}'", rule_id));
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

// ═══ Control-flow premise helpers (PatternNode level) ═══

/// Check if a PatternNode is an executable grounded op head.
/// This checks the HEAD of an ExprCons, not the whole expression.
#[cfg(feature = "mork-backend")]
fn he_pattern_head_is_executable(node: &PatternNode) -> bool {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "ExprCons" && args.len() == 2 => {
            he_pattern_is_grounded_op(&args[0])
        },
        _ => false,
    }
}

/// Check if a PatternNode is a minimal instruction keyword (superpose, match, unify,
/// collapse, case, assert). These have dedicated MC_* template rules and must NOT
/// fall through to MC_Equation / MC_NoMatch.
#[cfg(feature = "mork-backend")]
fn he_pattern_head_is_minimal_instruction(node: &PatternNode) -> bool {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "ExprCons" && args.len() == 2 => {
            he_pattern_is_minimal_instruction_keyword(&args[0])
        },
        _ => false,
    }
}

#[cfg(feature = "mork-backend")]
fn he_pattern_is_minimal_instruction_keyword(node: &PatternNode) -> bool {
    if let Some(name) = he_pattern_sym_name(node) {
        matches!(name,
            "superpose" | "symhex_7375706572706f7365"
            | "match" | "symhex_6d61746368"
            | "unify" | "symhex_756e696679"
            | "collapse" | "symhex_636f6c6c61707365"
            | "case" | "symhex_63617365"
            | "assert" | "symhex_617373657274"
        )
    } else {
        false
    }
}

/// Check if a PatternNode is a known grounded op atom.
#[cfg(feature = "mork-backend")]
fn he_pattern_is_grounded_op(node: &PatternNode) -> bool {
    matches!(
        node,
        PatternNode::Apply { ctor, args }
            if args.is_empty() && matches!(ctor.as_str(),
                "OpAdd" | "OpSub" | "OpMul" | "OpDiv" | "OpMod" | "OpLt" | "OpGt" | "OpEq"
            )
    )
}

/// Extract the head symbol name from a SymAtom PatternNode.
fn he_pattern_sym_name(node: &PatternNode) -> Option<&str> {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "SymAtom" && args.len() == 1 => {
            match &args[0] {
                PatternNode::Apply { ctor: name, args: inner } if inner.is_empty() => Some(name.as_str()),
                _ => None,
            }
        },
        _ => None,
    }
}

/// Collect ExprCons list into Vec<PatternNode>.
fn he_pattern_collect_list(node: &PatternNode) -> Vec<PatternNode> {
    let mut items = Vec::new();
    let mut cur = node;
    loop {
        match cur {
            PatternNode::Apply { ctor, args } if ctor == "ExprCons" && args.len() == 2 => {
                items.push(args[0].clone());
                cur = &args[1];
            },
            PatternNode::Apply { ctor, args } if ctor == "ExprNil" && args.is_empty() => break,
            _ => {
                items.push(cur.clone());
                break;
            },
        }
    }
    items
}

/// Build an ExprCons list from a slice of PatternNodes.
fn he_pattern_build_list(items: &[PatternNode]) -> PatternNode {
    let mut acc = he_atom_ctor("ExprNil");
    for item in items.iter().rev() {
        acc = PatternNode::Apply {
            ctor: "ExprCons".to_string(),
            args: vec![item.clone(), acc],
        };
    }
    acc
}

/// Run nested sub-evaluation for `collapseBind` oracle premise.
///
/// Builds a start state `State(Metta(expr, ty), space, Empty)`, runs the
/// transition graph with scoped fuel (parent_remaining / 2), collects all
/// terminal Done states, and packs their result values as a list.
#[cfg(feature = "mork-backend")]
fn he_collapse_bind_nested(
    expr_node: &PatternNode,
    ty_node: &PatternNode,
    space: &Space,
    parent_limits: MorkExecutionLimits,
) -> Result<PatternNode, String> {
    let expr_atom = he_pattern_node_to_atom(expr_node)?;
    let ty_atom = he_pattern_node_to_atom(ty_node)?;
    let start = mk_state(
        he_instr_metta(expr_atom, ty_atom),
        space.clone(),
        Atom::C_Empty,
    );
    let child_limits = MorkExecutionLimits {
        rule_copies: parent_limits.rule_copies,
        max_steps: parent_limits.max_steps / 2,
    };
    let start_display = format!("{}", start);
    let start_id = hash_display_id(&start_display);
    let mut child_eval_ms = 0.0f64;
    let results = run_transition_graph(
        start,
        &start_display,
        start_id,
        child_limits,
        |st| he_native_step_state(st, child_limits, &mut child_eval_ms),
    )?;
    // Collect result values from terminal Done states
    let lang = MeTTaHELanguage;
    let mut values = Vec::new();
    for term_info in &results.all_terms {
        if !term_info.is_normal_form || !term_info.display.contains("C_Done") {
            continue;
        }
        let parsed = lang.parse_term_for_env(&term_info.display).map_err(|e| {
            format!("collapseBind: failed to reparse Done state '{}': {}", term_info.display, e)
        })?;
        let wrapped = parsed.as_any().downcast_ref::<MeTTaHETerm>().ok_or_else(|| {
            format!("collapseBind: reparsed state is not MeTTaHETerm")
        })?;
        if let MeTTaHETermInner::State(State::C_State(instr, _, out)) = &wrapped.0 {
            if matches!(instr.as_ref(), Instr::C_Done) {
                let val_node = he_atom_to_pattern_node(out)?;
                values.push(val_node);
            }
        }
    }
    Ok(he_pattern_build_list(&values))
}

/// Check if a PatternNode matches the True atom (C_True or C_SymAtom(True)).
#[cfg(feature = "mork-backend")]
fn he_pattern_is_true(node: &PatternNode) -> bool {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "True" && args.is_empty() => true,
        _ => he_pattern_sym_name(node) == Some("True"),
    }
}

/// Parse switch-minimal/switch call: (switch-minimal scrutinee rawCases) or (switch s c).
/// Returns (scrutinee, rawCases) if matched.
fn he_pattern_parse_switch_minimal(node: &PatternNode) -> Option<(PatternNode, PatternNode)> {
    let items = he_pattern_collect_list(node);
    if items.len() == 3 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "switch-minimal" || head_name == "switch" || head_name == "symhex_7377697463682d6d696e696d616c" || head_name == "symhex_737769746368" {
            return Some((items[1].clone(), items[2].clone()));
        }
    }
    None
}

/// Parse case call: (case scrutinee rawCases). Returns (scrutinee, rawCases).
fn he_pattern_parse_case(node: &PatternNode) -> Option<(PatternNode, PatternNode)> {
    let items = he_pattern_collect_list(node);
    if items.len() == 3 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "case" || head_name == "symhex_63617365" {
            return Some((items[1].clone(), items[2].clone()));
        }
    }
    None
}

/// Parse assert call: (assert asserted). Returns asserted.
fn he_pattern_parse_assert(node: &PatternNode) -> Option<PatternNode> {
    let items = he_pattern_collect_list(node);
    if items.len() == 2 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "assert" || head_name == "symhex_617373657274" {
            return Some(items[1].clone());
        }
    }
    None
}

/// Parse (superpose (e1 e2 ...)) → Some(vec![e1, e2, ...]).
/// Returns None if not a superpose expression or wrong arity.
fn he_pattern_parse_superpose_elements(node: &PatternNode) -> Option<Vec<PatternNode>> {
    let items = he_pattern_collect_list(node);
    if items.len() == 2 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "superpose" || head_name == "symhex_7375706572706f7365" {
            let elements = he_pattern_collect_list(&items[1]);
            if !elements.is_empty() {
                return Some(elements);
            }
        }
    }
    None
}

/// Check if (superpose ()) — empty superpose.
fn he_pattern_is_superpose_empty(node: &PatternNode) -> bool {
    let items = he_pattern_collect_list(node);
    if items.len() == 2 {
        let head_name = he_pattern_sym_name(&items[0]);
        if head_name == Some("superpose") || head_name == Some("symhex_7375706572706f7365") {
            // Check if arg is ExprNil (empty list)
            return matches!(&items[1], PatternNode::Apply { ctor, args } if ctor == "ExprNil" && args.is_empty());
        }
    }
    false
}

/// Parse (match spaceRef pattern template) → Some((pattern, template)).
/// spaceRef is checked but not returned (evaluator uses runtime space).
fn he_pattern_parse_match_call(node: &PatternNode) -> Option<(PatternNode, PatternNode)> {
    let items = he_pattern_collect_list(node);
    if items.len() == 4 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "match" || head_name == "symhex_6d61746368" {
            return Some((items[2].clone(), items[3].clone()));
        }
    }
    None
}

/// Parse (unify target pattern success failure) → Some((target, pattern, success, failure)).
fn he_pattern_parse_unify_call(node: &PatternNode) -> Option<(PatternNode, PatternNode, PatternNode, PatternNode)> {
    let items = he_pattern_collect_list(node);
    if items.len() == 5 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "unify" || head_name == "symhex_756e696679" {
            return Some((items[1].clone(), items[2].clone(), items[3].clone(), items[4].clone()));
        }
    }
    None
}

/// Parse (collapse expr) → Some(expr).
fn he_pattern_parse_collapse_call(node: &PatternNode) -> Option<PatternNode> {
    let items = he_pattern_collect_list(node);
    if items.len() == 2 {
        let head_name = he_pattern_sym_name(&items[0])?;
        if head_name == "collapse" || head_name == "symhex_636f6c6c61707365" {
            return Some(items[1].clone());
        }
    }
    None
}

/// Collect space atoms as PatternNodes.
/// Converts the runtime Space (Atom-level) to PatternNode-level list elements.
#[cfg(feature = "mork-backend")]
fn he_pattern_space_atoms(space: &Space) -> Vec<PatternNode> {
    match space {
        Space::C_Space(atoms) => {
            let atom_list = he_collect_list_atom(atoms);
            atom_list.iter().filter_map(|a| he_atom_to_pattern_node(a).ok()).collect()
        },
        _ => Vec::new(),
    }
}

/// Collect list at Atom level (same as he_collect_list but accessible here).
#[cfg(feature = "mork-backend")]
fn he_collect_list_atom(atom: &Atom) -> Vec<Atom> {
    let mut items = Vec::new();
    let mut cur = atom;
    loop {
        match cur {
            Atom::C_ExprCons(head, tail) => {
                items.push((**head).clone());
                cur = tail;
            },
            Atom::C_ExprNil => break,
            _ => {
                items.push(cur.clone());
                break;
            },
        }
    }
    items
}

/// Select matching case template: pattern-match scrutinee against rawCases.
/// rawCases is a list of (pattern body) pairs. Returns matching templates.
fn he_pattern_select_switch_templates(
    scrutinee: &PatternNode,
    raw_cases: &PatternNode,
) -> Vec<PatternNode> {
    let cases = he_pattern_collect_list(raw_cases);
    let mut templates = Vec::new();
    for case_branch in &cases {
        let pair = he_pattern_collect_list(case_branch);
        if pair.len() == 2 {
            let pattern = &pair[0];
            let body = &pair[1];
            if let Some(bindings) = he_pattern_match(pattern, scrutinee) {
                let result = he_pattern_subst(body, &bindings);
                templates.push(result);
            }
        }
    }
    if templates.is_empty() {
        // No match → NotReducible sentinel
        templates.push(PatternNode::Apply {
            ctor: "SymAtom".to_string(),
            args: vec![he_atom_ctor("NotReducible")],
        });
    }
    templates
}

/// Simple pattern matching for PatternNode (used by switch/case).
/// VarAtom matches anything, SymAtom matches same symbol.
fn he_pattern_match(
    pattern: &PatternNode,
    target: &PatternNode,
) -> Option<Vec<(String, PatternNode)>> {
    let mut bindings = Vec::new();
    if he_pattern_match_inner(pattern, target, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

fn he_pattern_match_inner(
    pattern: &PatternNode,
    target: &PatternNode,
    bindings: &mut Vec<(String, PatternNode)>,
) -> bool {
    match pattern {
        PatternNode::Apply { ctor: pc, args: pargs } if pc == "VarAtom" && pargs.len() == 1 => {
            if let PatternNode::Apply { ctor: name, args: inner } = &pargs[0] {
                if inner.is_empty() {
                    bindings.push((name.clone(), target.clone()));
                    return true;
                }
            }
            false
        },
        PatternNode::Apply { ctor: pc, args: pargs } if pc == "ExprCons" && pargs.len() == 2 => {
            if let PatternNode::Apply { ctor: tc, args: targs } = target {
                if tc == "ExprCons" && targs.len() == 2 {
                    return he_pattern_match_inner(&pargs[0], &targs[0], bindings)
                        && he_pattern_match_inner(&pargs[1], &targs[1], bindings);
                }
            }
            false
        },
        _ => pattern == target,
    }
}

/// Apply bindings from pattern match to a template.
fn he_pattern_subst(template: &PatternNode, bindings: &[(String, PatternNode)]) -> PatternNode {
    match template {
        PatternNode::Apply { ctor, args } if ctor == "VarAtom" && args.len() == 1 => {
            if let PatternNode::Apply { ctor: name, args: inner } = &args[0] {
                if inner.is_empty() {
                    for (bname, bval) in bindings {
                        if bname == name {
                            return bval.clone();
                        }
                    }
                }
            }
            template.clone()
        },
        PatternNode::Apply { ctor, args } => PatternNode::Apply {
            ctor: ctor.clone(),
            args: args.iter().map(|a| he_pattern_subst(a, bindings)).collect(),
        },
        _ => template.clone(),
    }
}

/// Build assert error atom: ErrorAtom(ExprCons(SymAtom(assert), ExprCons(asserted, ExprNil)),
///                                      ExprCons(SymAtom(assertedVal), ExprCons(SymAtom("not"), ExprCons(SymAtom("True"), ExprNil))))
/// Simplified: ErrorAtom(assertExpr, badValueMsg)
fn he_pattern_mk_assert_error(asserted: &PatternNode, asserted_val: &PatternNode) -> PatternNode {
    let assert_sym = PatternNode::Apply {
        ctor: "SymAtom".to_string(),
        args: vec![he_atom_ctor("assert")],
    };
    let assert_expr = he_pattern_build_list(&[assert_sym, asserted.clone()]);

    let not_sym = PatternNode::Apply {
        ctor: "SymAtom".to_string(),
        args: vec![he_atom_ctor("not")],
    };
    let true_sym = PatternNode::Apply {
        ctor: "SymAtom".to_string(),
        args: vec![he_atom_ctor("True")],
    };
    let error_msg = he_pattern_build_list(&[asserted_val.clone(), not_sym, true_sym]);

    PatternNode::Apply {
        ctor: "ErrorAtom".to_string(),
        args: vec![assert_expr, error_msg],
    }
}

#[cfg(feature = "mork-backend")]
struct HeTemplatePremiseEvaluator<'a> {
    space: &'a Space,
    limits: MorkExecutionLimits,
}

#[cfg(feature = "mork-backend")]
impl RewritePremiseEvaluator for HeTemplatePremiseEvaluator<'_> {
    fn eval_relation_query(
        &self,
        relation: &str,
        args: &[crate::artifact_contract::PatternNode],
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        match relation {
            "isEmpty" => he_eval_unary_predicate(relation, args, env, he_pattern_is_empty),
            "isError" => he_eval_unary_predicate(relation, args, env, he_pattern_is_error),
            "notExpression" => he_eval_unary_predicate(relation, args, env, |arg| {
                !matches!(he_pattern_meta_type(arg), Some(PatternNode::Apply { ctor, args }) if ctor == "ExpressionType" && args.is_empty())
            }),
            "metaType" => he_eval_meta_type(args, env),
            "funcArgTypes" => he_eval_func_arg_types(args, env),
            "typeMatchesMetaOrAtom" => {
                he_eval_binary_predicate(relation, args, env, he_pattern_type_matches_meta_or_atom)
            },
            "needsTypeCast" => {
                he_eval_binary_predicate(relation, args, env, he_pattern_needs_type_cast)
            },
            "needsInterpExpr" => {
                he_eval_binary_predicate(relation, args, env, he_pattern_needs_interp_expr)
            },
            "changedToEmpty" => {
                he_eval_binary_predicate(relation, args, env, he_pattern_changed_to_empty)
            },
            "changedToError" => {
                he_eval_binary_predicate(relation, args, env, he_pattern_changed_to_error)
            },
            "typeOf" => he_eval_type_of(self.space, args, env),
            "typeMismatch" => he_eval_type_mismatch(self.space, args, env),
            "applicableFuncType" => he_eval_applicable_func_type(self.space, args, env),
            "needsTupleInterp" => he_eval_needs_tuple_interp(self.space, args, env),
            "noTypeAtAll" => he_eval_no_type_at_all(self.space, args, env),

            // ═══ Control-flow premises ═══
            "notExecutable" => he_eval_unary_predicate(relation, args, env, |arg| {
                !he_pattern_head_is_executable(arg) && !he_pattern_is_grounded_op(arg)
            }),
            "isExecutable" => he_eval_unary_predicate(relation, args, env, |arg| {
                he_pattern_head_is_executable(arg) || he_pattern_is_grounded_op(arg)
            }),
            "parseSwitchMinimalCall" => {
                if args.len() != 3 {
                    return Err(format!("parseSwitchMinimalCall expects 3 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some((scrutinee, raw_cases)) = he_pattern_parse_switch_minimal(&atom) else {
                    return Ok(Vec::new());
                };
                let envs = he_bind_relation_result(env, &args[1], scrutinee)?;
                let mut results = Vec::new();
                for e in &envs {
                    results.extend(he_bind_relation_result(e, &args[2], raw_cases.clone())?);
                }
                Ok(results)
            },
            "parseCaseCall" => {
                if args.len() != 3 {
                    return Err(format!("parseCaseCall expects 3 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some((scrutinee, raw_cases)) = he_pattern_parse_case(&atom) else {
                    return Ok(Vec::new());
                };
                let envs = he_bind_relation_result(env, &args[1], scrutinee)?;
                let mut results = Vec::new();
                for e in &envs {
                    results.extend(he_bind_relation_result(e, &args[2], raw_cases.clone())?);
                }
                Ok(results)
            },
            "parseAssertCall" => {
                if args.len() != 2 {
                    return Err(format!("parseAssertCall expects 2 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some(asserted) = he_pattern_parse_assert(&atom) else {
                    return Ok(Vec::new());
                };
                he_bind_relation_result(env, &args[1], asserted)
            },
            "selectSwitchResult" => {
                if args.len() != 3 {
                    return Err(format!("selectSwitchResult expects 3 args, got {}", args.len()));
                }
                let scrutinee = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let raw_cases = he_expect_ground_arg(relation, 1, &args[1], env)?;
                let templates = he_pattern_select_switch_templates(&scrutinee, &raw_cases);
                let mut results = Vec::new();
                for tmpl in templates {
                    results.extend(he_bind_relation_result(env, &args[2], tmpl)?);
                }
                Ok(results)
            },
            "isReducible" => he_eval_unary_predicate(relation, args, env, |arg| {
                he_pattern_sym_name(arg) != Some("NotReducible")
                    && !matches!(arg, PatternNode::Apply { ctor, args } if ctor == "SymAtom" && args.len() == 1
                        && matches!(&args[0], PatternNode::Apply { ctor: n, args: a } if a.is_empty() && n == "NotReducible"))
            }),
            "isNotReducible" => he_eval_unary_predicate(relation, args, env, |arg| {
                matches!(arg, PatternNode::Apply { ctor, args } if ctor == "SymAtom" && args.len() == 1
                    && matches!(&args[0], PatternNode::Apply { ctor: n, args: a } if a.is_empty() && n == "NotReducible"))
            }),
            "assertMatchesTrue" => he_eval_unary_predicate(relation, args, env, he_pattern_is_true),
            "assertNotTrue" => he_eval_unary_predicate(relation, args, env, |arg| !he_pattern_is_true(arg)),
            "mkAssertError" => {
                if args.len() != 3 {
                    return Err(format!("mkAssertError expects 3 args, got {}", args.len()));
                }
                let asserted = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let asserted_val = he_expect_ground_arg(relation, 1, &args[1], env)?;
                let err_atom = he_pattern_mk_assert_error(&asserted, &asserted_val);
                he_bind_relation_result(env, &args[2], err_atom)
            },

            // ═══ Minimal instruction premises ═══

            "parseSuperpose" => {
                // Multi-result: (superpose (e1 e2 ...)) → one binding per element
                if args.len() != 2 {
                    return Err(format!("parseSuperpose expects 2 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some(elems) = he_pattern_parse_superpose_elements(&atom) else {
                    return Ok(Vec::new());
                };
                let mut results = Vec::new();
                for elem in elems {
                    results.extend(he_bind_relation_result(env, &args[1], elem)?);
                }
                Ok(results)
            },
            "isSuperpose_empty" => {
                // Predicate: (superpose ()) → true
                he_eval_unary_predicate(relation, args, env, |arg| {
                    he_pattern_is_superpose_empty(arg)
                })
            },
            "parseMatchCall" => {
                // (match spaceRef pattern template) → bind pattern + template
                if args.len() != 3 {
                    return Err(format!("parseMatchCall expects 3 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some((pattern, template)) = he_pattern_parse_match_call(&atom) else {
                    return Ok(Vec::new());
                };
                let envs = he_bind_relation_result(env, &args[1], pattern)?;
                let mut results = Vec::new();
                for e in &envs {
                    results.extend(he_bind_relation_result(e, &args[2], template.clone())?);
                }
                Ok(results)
            },
            "spaceQueryMatch" => {
                // Multi-result: iterate space atoms, match pattern, subst template
                if args.len() != 3 {
                    return Err(format!("spaceQueryMatch expects 3 args, got {}", args.len()));
                }
                let pattern = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let template = he_expect_ground_arg(relation, 1, &args[1], env)?;
                let space_atoms = he_pattern_space_atoms(self.space);
                let mut results = Vec::new();
                for space_atom in &space_atoms {
                    if let Some(bindings) = he_pattern_match(&pattern, space_atom) {
                        let result = he_pattern_subst(&template, &bindings);
                        results.extend(he_bind_relation_result(env, &args[2], result)?);
                    }
                }
                Ok(results)
            },
            "spaceQueryNoMatch" => {
                // Predicate: no space atom matches pattern
                if args.len() != 1 {
                    return Err(format!("spaceQueryNoMatch expects 1 arg, got {}", args.len()));
                }
                let pattern = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let space_atoms = he_pattern_space_atoms(self.space);
                let has_match = space_atoms.iter().any(|sa| he_pattern_match(&pattern, sa).is_some());
                if has_match {
                    Ok(Vec::new())
                } else {
                    Ok(vec![env.clone()])
                }
            },
            "parseUnifyCall" => {
                // (unify target pattern success failure) → bind all four
                if args.len() != 5 {
                    return Err(format!("parseUnifyCall expects 5 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some((target, pattern, success, failure)) = he_pattern_parse_unify_call(&atom) else {
                    return Ok(Vec::new());
                };
                let envs = he_bind_relation_result(env, &args[1], target)?;
                let mut r2 = Vec::new();
                for e in &envs {
                    r2.extend(he_bind_relation_result(e, &args[2], pattern.clone())?);
                }
                let mut r3 = Vec::new();
                for e in &r2 {
                    r3.extend(he_bind_relation_result(e, &args[3], success.clone())?);
                }
                let mut r4 = Vec::new();
                for e in &r3 {
                    r4.extend(he_bind_relation_result(e, &args[4], failure.clone())?);
                }
                Ok(r4)
            },
            "localMatch" => {
                // metta_match(pattern, target) + metta_subst(success, bindings)
                if args.len() != 4 {
                    return Err(format!("localMatch expects 4 args, got {}", args.len()));
                }
                let target = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let pattern = he_expect_ground_arg(relation, 1, &args[1], env)?;
                let success = he_expect_ground_arg(relation, 2, &args[2], env)?;
                let Some(bindings) = he_pattern_match(&pattern, &target) else {
                    return Ok(Vec::new());
                };
                let result = he_pattern_subst(&success, &bindings);
                he_bind_relation_result(env, &args[3], result)
            },
            "localNoMatch" => {
                // Predicate: metta_match(pattern, target) returns None
                if args.len() != 2 {
                    return Err(format!("localNoMatch expects 2 args, got {}", args.len()));
                }
                let target = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let pattern = he_expect_ground_arg(relation, 1, &args[1], env)?;
                if he_pattern_match(&pattern, &target).is_none() {
                    Ok(vec![env.clone()])
                } else {
                    Ok(Vec::new())
                }
            },
            "parseCollapseCall" => {
                // (collapse expr) → bind expr
                if args.len() != 2 {
                    return Err(format!("parseCollapseCall expects 2 args, got {}", args.len()));
                }
                let atom = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let Some(expr) = he_pattern_parse_collapse_call(&atom) else {
                    return Ok(Vec::new());
                };
                he_bind_relation_result(env, &args[1], expr)
            },
            "collapseBind" => {
                // Oracle premise: run nested sub-evaluation, collect terminal
                // results, pack as a MeTTa list.
                if args.len() != 3 {
                    return Err(format!("collapseBind expects 3 args, got {}", args.len()));
                }
                let expr_node = he_expect_ground_arg(relation, 0, &args[0], env)?;
                let ty_node = he_expect_ground_arg(relation, 1, &args[1], env)?;
                let packed = he_collapse_bind_nested(
                    &expr_node, &ty_node, self.space, self.limits,
                )?;
                he_bind_relation_result(env, &args[2], packed)
            },

            // ═══ Equation / grounded call premises (MC_Equation, MC_Grounded, MC_NoMatch) ═══

            "groundedCallResult" => {
                // groundedCallResult(space, atom, result): if atom is (groundedOp args...),
                // dispatch the grounded call and bind result.
                // Guard: ty != AtomType — when ty=AtomType, the atom is returned as-is
                // (MettaCall with AtomType shouldn't normally occur; M_TypeMatch handles it
                // at the Metta level. This guard matches Ascent backend behavior.)
                if args.len() != 3 {
                    return Err(format!("groundedCallResult expects 3 args, got {}", args.len()));
                }
                if let Some(ty_node) = env.get("ty") {
                    if matches!(ty_node, PatternNode::Apply { ctor, args: a } if ctor == "AtomType" && a.is_empty()) {
                        return Ok(Vec::new());
                    }
                }
                let atom_node = he_expect_ground_arg(relation, 0, &args[1], env)?;
                let atom_val = he_pattern_node_to_atom(&atom_node)?;
                // Extract (op argsTail) from ExprCons
                let Atom::C_ExprCons(op, args_tail) = &atom_val else {
                    return Ok(Vec::new());
                };
                // Must be an executable grounded op
                if is_executable_grounded(op.as_ref()).is_none() {
                    return Ok(Vec::new());
                }
                let Some(result) = eval_grounded_dispatch((**op).clone(), (**args_tail).clone()) else {
                    return Ok(Vec::new());
                };
                let result_node = he_atom_to_pattern_node(&result)?;
                he_bind_relation_result(env, &args[2], result_node)
            },
            "eqQueryResult" => {
                // eqQueryResult(space, atom, rhs): multi-result — pattern-match atom
                // against equation LHS in space, substitute into RHS.
                // Guard: skip for minimal instruction heads (they have dedicated MC_* rules).
                if args.len() != 3 {
                    return Err(format!("eqQueryResult expects 3 args, got {}", args.len()));
                }
                let atom_node = he_expect_ground_arg(relation, 1, &args[1], env)?;
                if he_pattern_head_is_minimal_instruction(&atom_node) {
                    return Ok(Vec::new());
                }
                let atom_val = he_pattern_node_to_atom(&atom_node)?;
                let query_results = match self.space {
                    Space::C_Space(atoms) => he_space_index_cache().query_equation_results_with(
                        atoms.as_ref(),
                        &atom_val,
                        build_he_space_index,
                    ),
                    _ => Arc::new(Vec::new()),
                };
                let mut results = Vec::new();
                for rhs in query_results.iter() {
                    let rhs_node = he_atom_to_pattern_node(rhs)?;
                    results.extend(he_bind_relation_result(env, &args[2], rhs_node)?);
                }
                Ok(results)
            },
            "noEqQuery" => {
                // noEqQuery(space, atom): predicate — no equation in space matches atom.
                // Guard: skip for minimal instruction heads (they have dedicated MC_* rules).
                if args.len() != 2 {
                    return Err(format!("noEqQuery expects 2 args, got {}", args.len()));
                }
                let atom_node = he_expect_ground_arg(relation, 1, &args[1], env)?;
                if he_pattern_head_is_minimal_instruction(&atom_node) {
                    return Ok(Vec::new());
                }
                let atom_val = he_pattern_node_to_atom(&atom_node)?;
                let has_match = he_space_index_cache().equation_has_match_in_space(
                    self.space,
                    &atom_val,
                    build_he_space_index,
                );
                if has_match {
                    Ok(Vec::new())
                } else {
                    Ok(vec![env.clone()])
                }
            },

            _ => Err(format!(
                "HE generic template execution does not yet support relation premise '{}'",
                relation
            )),
        }
    }
}

#[cfg(feature = "mork-backend")]
fn he_template_rule_enabled(logical_transition_id: &str) -> bool {
    matches!(
        logical_transition_id,
        "C_Metta:M_Empty"
            | "C_Metta:M_Error"
            | "C_Metta:M_TypeMatch"
            | "C_Metta:M_SymbolOrGrounded"
            | "C_Metta:M_Expression"
            | "C_InterpExpr:IE_NotExpr"
            | "C_InterpFunc:IF_Start"
            | "C_InterpFunc:IF_Nil"
            | "C_InterpFunc:IF_NotExpr"
            | "C_InterpArgs:IA_Start_Typed"
            | "C_InterpArgs:IA_Start_Undef"
            | "C_InterpTuple:IT_Nil"
            | "C_InterpTuple:IT_StartCons"
            | "C_Return:IF_AfterOp_Empty"
            | "C_Return:IF_AfterOp_Error"
            | "C_Return:IF_AfterOp_NoArgs"
            | "C_Return:IF_AfterOp_EvalArgs"
            | "C_Return:IF_AfterArgs_Empty"
            | "C_Return:IF_AfterArgs_Error"
            | "C_Return:IF_AfterArgs_Call"
            | "C_Return:IA_Head_Empty"
            | "C_Return:IA_Head_Error"
            | "C_Return:IA_Head_RestNil"
            | "C_Return:IA_Head_Recurse"
            | "C_Return:IA_Tail_Empty"
            | "C_Return:IA_Tail_Error"
            | "C_Return:IA_Tail_Cons"
            | "C_Return:IT_Head_Empty"
            | "C_Return:IT_Head_Error"
            | "C_Return:IT_Head_TailNil"
            | "C_Return:IT_Head_Recurse"
            | "C_Return:IT_Tail_Empty"
            | "C_Return:IT_Tail_Error"
            | "C_Return:IT_Tail_Cons"
            | "C_Return:R_Done"
            | "C_MettaCall:MC_Error"
            | "C_InterpExpr:IE_FuncType"
            | "C_InterpExpr:IE_TupleType"
            | "C_InterpExpr:IE_NoType"
            | "C_TypeCast:TC_Match"
            | "C_TypeCast:TC_Mismatch"
            | "C_MettaCall:MC_SwitchMinimal_Start"
            | "C_MettaCall:MC_Assert_Start"
            | "C_MettaCall:MC_Case_Start"
            | "C_Return:MC_SwitchMinimal_Match"
            | "C_Return:MC_SwitchMinimal_NoMatch"
            | "C_Return:MC_Assert_True"
            | "C_Return:MC_Assert_NotTrue"
            // Equation / grounded dispatch (formerly handwritten)
            | "C_MettaCall:MC_Grounded"
            | "C_MettaCall:MC_Equation"
            | "C_MettaCall:MC_NoMatch"
            // Minimal instructions
            | "C_MettaCall:MC_Superpose"
            | "C_MettaCall:MC_Superpose_Empty"
            | "C_MettaCall:MC_Match"
            | "C_MettaCall:MC_Match_Empty"
            | "C_MettaCall:MC_Unify_Match"
            | "C_MettaCall:MC_Unify_NoMatch"
            | "C_MettaCall:MC_Collapse"
    )
}

#[cfg(feature = "mork-backend")]
fn he_expect_ground_arg(
    relation: &str,
    idx: usize,
    arg: &PatternNode,
    env: &TemplateBindings,
) -> Result<PatternNode, String> {
    match resolve_query_arg(arg, env)? {
        ResolvedQueryArg::Ground(value) => Ok(value),
        ResolvedQueryArg::UnboundVar(name) => Err(format!(
            "HE relation '{}' requires argument {} to be ground, got unbound variable '{}'",
            relation, idx, name
        )),
    }
}

#[cfg(feature = "mork-backend")]
fn he_bind_relation_result(
    env: &TemplateBindings,
    arg: &PatternNode,
    value: PatternNode,
) -> Result<Vec<TemplateBindings>, String> {
    match resolve_query_arg(arg, env)? {
        ResolvedQueryArg::Ground(existing) => {
            if existing == value {
                Ok(vec![env.clone()])
            } else {
                Ok(Vec::new())
            }
        },
        ResolvedQueryArg::UnboundVar(name) => {
            let mut next = env.clone();
            bind_var(&mut next, &name, value)?;
            Ok(vec![next])
        },
    }
}

#[cfg(feature = "mork-backend")]
fn he_eval_unary_predicate(
    relation: &str,
    args: &[PatternNode],
    env: &TemplateBindings,
    pred: impl Fn(&PatternNode) -> bool,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 1 {
        return Err(format!(
            "HE relation '{}' expects 1 arg, got {}",
            relation,
            args.len()
        ));
    }
    let arg = he_expect_ground_arg(relation, 0, &args[0], env)?;
    if pred(&arg) {
        Ok(vec![env.clone()])
    } else {
        Ok(Vec::new())
    }
}

#[cfg(feature = "mork-backend")]
fn he_eval_binary_predicate(
    relation: &str,
    args: &[PatternNode],
    env: &TemplateBindings,
    pred: impl Fn(&PatternNode, &PatternNode) -> bool,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 2 {
        return Err(format!(
            "HE relation '{}' expects 2 args, got {}",
            relation,
            args.len()
        ));
    }
    let lhs = he_expect_ground_arg(relation, 0, &args[0], env)?;
    let rhs = he_expect_ground_arg(relation, 1, &args[1], env)?;
    if pred(&lhs, &rhs) {
        Ok(vec![env.clone()])
    } else {
        Ok(Vec::new())
    }
}

#[cfg(feature = "mork-backend")]
fn he_eval_meta_type(args: &[PatternNode], env: &TemplateBindings) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 2 {
        return Err(format!("HE relation 'metaType' expects 2 args, got {}", args.len()));
    }
    let atom = he_expect_ground_arg("metaType", 0, &args[0], env)?;
    let Some(mt) = he_pattern_meta_type(&atom) else {
        return Ok(Vec::new());
    };
    he_bind_relation_result(env, &args[1], mt)
}

#[cfg(feature = "mork-backend")]
fn he_eval_func_arg_types(
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 2 {
        return Err(format!(
            "HE relation 'funcArgTypes' expects 2 args, got {}",
            args.len()
        ));
    }
    let op_type = he_expect_ground_arg("funcArgTypes", 0, &args[0], env)?;
    let Some(arg_types) = he_pattern_func_arg_types(&op_type) else {
        return Ok(Vec::new());
    };
    he_bind_relation_result(env, &args[1], arg_types)
}

// ═══ PatternNode ↔ Atom conversion for space-accessing premises ═══

fn he_pattern_node_to_atom(node: &PatternNode) -> Result<Atom, String> {
    let text = render_he_runtime_term(node)?;
    let lang = MeTTaHELanguage;
    let parsed = lang.parse_term_for_env(&text)?;
    let wrapped = parsed.as_any().downcast_ref::<MeTTaHETerm>().ok_or_else(|| {
        format!("HE premise evaluator: expected MeTTaHETerm after parsing '{}'", text)
    })?;
    match &wrapped.0 {
        MeTTaHETermInner::Atom(a) => Ok(a.clone()),
        _ => Err(format!(
            "HE premise evaluator: parsed non-Atom wrapper from '{}' (got {:?})",
            text, std::mem::discriminant(&wrapped.0)
        )),
    }
}

fn he_atom_to_pattern_node(atom: &Atom) -> Result<PatternNode, String> {
    let text = format!("{}", atom);
    parse_runtime_term(&CPrefixConstructorCodec, &text)
}

// ═══ Space-accessing premise evaluators ═══

/// typeOf(space, atom, ty): look up type annotation in space.
/// Implements HE spec getAtomTypes + matchTypes:
///   - If atom has no annotation, its type defaults to %Undefined%
///   - matchTypes succeeds when either side is %Undefined% or Atom
#[cfg(feature = "mork-backend")]
fn he_eval_type_of(
    space: &Space,
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 3 {
        return Err(format!("HE relation 'typeOf' expects 3 args, got {}", args.len()));
    }
    // args[0] = space (ignored, use runtime space directly)
    let atom_node = he_expect_ground_arg("typeOf", 1, &args[1], env)?;
    let atom_val = he_pattern_node_to_atom(&atom_node)?;
    // HE spec: getAtomTypes defaults to [%Undefined%] when no annotation
    let actual_type = he_type_of(space, &atom_val)
        .unwrap_or(Atom::C_UndefinedType);
    let actual_node = he_atom_to_pattern_node(&actual_type)?;

    // Check if the expected type (args[2]) is already bound
    match resolve_query_arg(&args[2], env)? {
        ResolvedQueryArg::UnboundVar(_) => {
            // Bind the actual type to the output variable
            he_bind_relation_result(env, &args[2], actual_node)
        },
        ResolvedQueryArg::Ground(expected_node) => {
            // HE spec matchTypes: succeed if either side is %Undefined% or Atom
            let is_undef = |n: &PatternNode| matches!(n,
                PatternNode::Apply { ctor, args } if (ctor == "UndefinedType" || ctor == "AtomType") && args.is_empty());
            let is_var = |n: &PatternNode| matches!(n, PatternNode::Apply { ctor, .. } if ctor == "VarAtom");
            if actual_node == expected_node
                || is_undef(&actual_node)
                || is_undef(&expected_node)
                || is_var(&expected_node)
            {
                Ok(vec![env.clone()])
            } else {
                Ok(Vec::new())
            }
        },
    }
}

/// typeMismatch(space, atom, ty, actual): look up type, succeed when actual ≠ ty.
/// Uses HE spec matchTypes semantics: %Undefined%/Atom/variable types always match.
#[cfg(feature = "mork-backend")]
fn he_eval_type_mismatch(
    space: &Space,
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 4 {
        return Err(format!("HE relation 'typeMismatch' expects 4 args, got {}", args.len()));
    }
    let atom_node = he_expect_ground_arg("typeMismatch", 1, &args[1], env)?;
    let ty_node = he_expect_ground_arg("typeMismatch", 2, &args[2], env)?;
    let atom_val = he_pattern_node_to_atom(&atom_node)?;
    let ty_val = he_pattern_node_to_atom(&ty_node)?;
    // HE spec: getAtomTypes defaults to [%Undefined%]
    let actual_type = he_type_of(space, &atom_val)
        .unwrap_or(Atom::C_UndefinedType);
    // HE spec matchTypes: %Undefined%/Atom/variable → always match (no mismatch)
    let is_wildcard_type = |a: &Atom| matches!(a, Atom::C_UndefinedType | Atom::C_AtomType);
    let is_var_type = |a: &Atom| matches!(a, Atom::C_VarAtom(_));
    if actual_type == ty_val
        || is_wildcard_type(&actual_type)
        || is_wildcard_type(&ty_val)
        || is_var_type(&ty_val)
    {
        return Ok(Vec::new()); // types match → mismatch premise fails
    }
    let actual_node = he_atom_to_pattern_node(&actual_type)?;
    he_bind_relation_result(env, &args[3], actual_node)
}

/// applicableFuncType(space, atom, ty, opType, retType): find arrow type for expr.
#[cfg(feature = "mork-backend")]
fn he_eval_applicable_func_type(
    space: &Space,
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 5 {
        return Err(format!(
            "HE relation 'applicableFuncType' expects 5 args, got {}",
            args.len()
        ));
    }
    let atom_node = he_expect_ground_arg("applicableFuncType", 1, &args[1], env)?;
    let ty_node = he_expect_ground_arg("applicableFuncType", 2, &args[2], env)?;
    let atom_val = he_pattern_node_to_atom(&atom_node)?;
    let ty_val = he_pattern_node_to_atom(&ty_node)?;
    let Some(payload) = find_applicable_func_type(space, &atom_val, &ty_val) else {
        return Ok(Vec::new());
    };
    let Atom::C_ExprCons(op_type, ret_type) = payload else {
        return Err(format!(
            "HE applicableFuncType: expected C_ExprCons payload, got {}",
            payload
        ));
    };
    let op_node = he_atom_to_pattern_node(&op_type)?;
    let ret_node = he_atom_to_pattern_node(&ret_type)?;
    // Bind opType first, then retType on the resulting env
    let envs = he_bind_relation_result(env, &args[3], op_node)?;
    let mut results = Vec::new();
    for e in &envs {
        results.extend(he_bind_relation_result(e, &args[4], ret_node.clone())?);
    }
    Ok(results)
}

/// needsTupleInterp(space, atom, ty): no applicable func type AND has non-func types.
#[cfg(feature = "mork-backend")]
fn he_eval_needs_tuple_interp(
    space: &Space,
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 3 {
        return Err(format!(
            "HE relation 'needsTupleInterp' expects 3 args, got {}",
            args.len()
        ));
    }
    let atom_node = he_expect_ground_arg("needsTupleInterp", 1, &args[1], env)?;
    let atom_val = he_pattern_node_to_atom(&atom_node)?;
    let Some(non_func_ty) = has_non_func_types(space, &atom_val) else {
        return Ok(Vec::new());
    };
    // Guard: no applicable func type exists for this non-func type
    if find_applicable_func_type(space, &atom_val, &non_func_ty).is_some() {
        return Ok(Vec::new());
    }
    Ok(vec![env.clone()])
}

/// noTypeAtAll(space, atom): expression head has no explicit type annotation.
#[cfg(feature = "mork-backend")]
fn he_eval_no_type_at_all(
    space: &Space,
    args: &[PatternNode],
    env: &TemplateBindings,
) -> Result<Vec<TemplateBindings>, String> {
    if args.len() != 2 {
        return Err(format!(
            "HE relation 'noTypeAtAll' expects 2 args, got {}",
            args.len()
        ));
    }
    let atom_node = he_expect_ground_arg("noTypeAtAll", 1, &args[1], env)?;
    let atom_val = he_pattern_node_to_atom(&atom_node)?;
    let Atom::C_ExprCons(head, _) = atom_val else {
        return Ok(Vec::new());
    };
    if he_type_of(space, head.as_ref()).is_none() {
        Ok(vec![env.clone()])
    } else {
        Ok(Vec::new())
    }
}

fn he_atom_ctor(name: &str) -> PatternNode {
    PatternNode::Apply {
        ctor: name.to_string(),
        args: Vec::new(),
    }
}

#[cfg(feature = "mork-backend")]
fn he_pattern_is_empty(node: &PatternNode) -> bool {
    matches!(node, PatternNode::Apply { ctor, args } if ctor == "Empty" && args.is_empty())
}

#[cfg(feature = "mork-backend")]
fn he_pattern_is_error(node: &PatternNode) -> bool {
    matches!(node, PatternNode::Apply { ctor, .. } if ctor == "ErrorAtom")
}

#[cfg(feature = "mork-backend")]
fn he_pattern_meta_type(node: &PatternNode) -> Option<PatternNode> {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "SymAtom" && args.len() == 1 => {
            Some(he_atom_ctor("SymbolType"))
        },
        PatternNode::Apply { ctor, args } if ctor == "VarAtom" && args.len() == 1 => {
            Some(he_atom_ctor("VariableType"))
        },
        PatternNode::Apply { ctor, args } if ctor == "ExprCons" && args.len() == 2 => {
            Some(he_atom_ctor("ExpressionType"))
        },
        PatternNode::Apply { ctor, args } if ctor == "ExprNil" && args.is_empty() => {
            Some(he_atom_ctor("ExpressionType"))
        },
        PatternNode::Apply { ctor, args }
            if matches!(
                ctor.as_str(),
                "GInt"
                    | "GString"
                    | "GBool"
                    | "True"
                    | "False"
                    | "OpAdd"
                    | "OpSub"
                    | "OpMul"
                    | "OpDiv"
                    | "OpMod"
                    | "OpLt"
                    | "OpGt"
                    | "OpEq"
            ) && ((matches!(ctor.as_str(), "GInt" | "GString" | "GBool") && args.len() == 1)
                || (matches!(
                    ctor.as_str(),
                    "True" | "False" | "OpAdd" | "OpSub" | "OpMul" | "OpDiv" | "OpMod" | "OpLt" | "OpGt" | "OpEq"
                ) && args.is_empty())) =>
        {
            Some(he_atom_ctor("GroundedType"))
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn he_pattern_type_matches_meta_or_atom(atom: &PatternNode, ty: &PatternNode) -> bool {
    ty == &he_atom_ctor("AtomType")
        || he_pattern_meta_type(atom).as_ref() == Some(ty)
        || he_pattern_meta_type(atom).as_ref() == Some(&he_atom_ctor("VariableType"))
}

#[cfg(feature = "mork-backend")]
fn he_pattern_needs_type_cast(atom: &PatternNode, ty: &PatternNode) -> bool {
    matches!(
        he_pattern_meta_type(atom).as_ref(),
        Some(PatternNode::Apply { ctor, args })
            if ((ctor == "SymbolType" || ctor == "GroundedType" || ctor == "ExpressionType") && args.is_empty())
    ) && !he_pattern_type_matches_meta_or_atom(atom, ty)
        && matches!(atom, PatternNode::Apply { ctor, args } if (ctor == "ExprNil" && args.is_empty()) || ctor == "SymAtom" || ctor == "GInt" || ctor == "GString" || ctor == "GBool" || matches!(ctor.as_str(), "True" | "False" | "OpAdd" | "OpSub" | "OpMul" | "OpDiv" | "OpMod" | "OpLt" | "OpGt" | "OpEq"))
}

#[cfg(feature = "mork-backend")]
fn he_pattern_needs_interp_expr(atom: &PatternNode, ty: &PatternNode) -> bool {
    matches!(
        he_pattern_meta_type(atom),
        Some(PatternNode::Apply { ref ctor, ref args }) if ctor == "ExpressionType" && args.is_empty()
    ) && !he_pattern_type_matches_meta_or_atom(atom, ty)
}

#[cfg(feature = "mork-backend")]
fn he_pattern_changed_to_empty(orig: &PatternNode, new: &PatternNode) -> bool {
    he_pattern_is_empty(new) && orig != new
}

#[cfg(feature = "mork-backend")]
fn he_pattern_changed_to_error(orig: &PatternNode, new: &PatternNode) -> bool {
    he_pattern_is_error(new) && orig != new
}

#[cfg(feature = "mork-backend")]
fn he_pattern_func_arg_types(node: &PatternNode) -> Option<PatternNode> {
    // Unfold ArrowType(A, ArrowType(B, ...)) into ExprCons(A, ExprCons(B, ..., ExprNil)).
    // The last element of the arrow chain is the return type (dropped).
    match node {
        PatternNode::Apply { ctor, args } if ctor == "ArrowType" && args.len() == 2 => {
            let domain = &args[0];
            let codomain = &args[1];
            // If codomain is another ArrowType, collect remaining arg types
            match he_pattern_func_arg_types(codomain) {
                Some(rest_list) => Some(PatternNode::Apply {
                    ctor: "ExprCons".to_string(),
                    args: vec![domain.clone(), rest_list],
                }),
                None => {
                    // codomain is the return type; domain is the last arg type
                    Some(PatternNode::Apply {
                        ctor: "ExprCons".to_string(),
                        args: vec![
                            domain.clone(),
                            PatternNode::Apply {
                                ctor: "ExprNil".to_string(),
                                args: Vec::new(),
                            },
                        ],
                    })
                },
            }
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn parse_he_state_from_runtime_text(text: &str) -> Result<State, String> {
    let lang = MeTTaHELanguage;
    let parsed = lang.parse_term_for_env(text)?;
    let wrapped = parsed.as_any().downcast_ref::<MeTTaHETerm>().ok_or_else(|| {
        format!("HE generic rewrite executor expected MeTTaHETerm after parsing '{}'", text)
    })?;
    match &wrapped.0 {
        MeTTaHETermInner::State(state) => Ok(state.clone()),
        _ => Err(format!(
            "HE generic rewrite executor parsed non-State wrapper from '{}'",
            text
        )),
    }
}

#[cfg(feature = "mork-backend")]
fn he_try_execute_template_rule(
    rule_id: &str,
    logical_transition_id: &str,
    state: &State,
    contract: &HeRewriteContract,
    limits: MorkExecutionLimits,
) -> Result<Option<Vec<State>>, String> {
    if !he_template_rule_enabled(logical_transition_id) {
        return Ok(None);
    }
    let rule = contract.rewrite_ir.rule(rule_id).ok_or_else(|| {
        format!("HE rewrite contract missing structured rule '{}' for template execution", rule_id)
    })?;
    let space: &Space = match state {
        State::C_State(_, sp, _) => sp.as_ref(),
        _ => return Ok(None),
    };
    let evaluator = HeTemplatePremiseEvaluator { space, limits };
    let instantiated = execute_rule_to_patterns(
        &CPrefixConstructorCodec,
        &format!("{}", state),
        rule,
        &evaluator,
    )?;
    let next_states = instantiated
        .into_iter()
        .map(|node| render_he_runtime_term(&node))
        .map(|text| text.and_then(|text| parse_he_state_from_runtime_text(&text)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Some(next_states))
}

fn render_he_runtime_raw_payload(node: &PatternNode) -> Result<String, String> {
    match node {
        PatternNode::Apply { ctor, args } if args.is_empty() => Ok(ctor.clone()),
        _ => Err(format!(
            "HE template renderer expected raw payload leaf, got {:?}",
            node
        )),
    }
}

fn render_he_runtime_term(node: &PatternNode) -> Result<String, String> {
    match node {
        PatternNode::Apply { ctor, args } => {
            let rendered_ctor = CPrefixConstructorCodec.artifact_to_runtime_ctor(ctor);
            if args.is_empty() {
                return Ok(rendered_ctor);
            }
            let rendered_args = if matches!(ctor.as_str(), "SymAtom" | "GString")
                && args.len() == 1
            {
                vec![render_he_runtime_raw_payload(&args[0])?]
            } else {
                args.iter()
                    .map(render_he_runtime_term)
                    .collect::<Result<Vec<_>, _>>()?
            };
            Ok(format!("{rendered_ctor}({})", rendered_args.join(", ")))
        },
        PatternNode::Fvar { name } => Err(format!(
            "HE template renderer cannot render unresolved free variable '{}'",
            name
        )),
        PatternNode::Bvar { index } => Err(format!(
            "HE template renderer cannot render bound variable index {}",
            index
        )),
        PatternNode::Collection { .. } => {
            let text = crate::rewrite_template::render_runtime_term(&CPrefixConstructorCodec, node)?;
            let reparsed = parse_runtime_term(&CPrefixConstructorCodec, &text)?;
            crate::rewrite_template::render_runtime_term(&CPrefixConstructorCodec, &reparsed)
        },
        PatternNode::Lambda { .. }
        | PatternNode::MultiLambda { .. }
        | PatternNode::Subst { .. } => Err(format!(
            "HE template renderer does not yet support higher-order node {:?}",
            node
        )),
    }
}

#[cfg(feature = "mork-backend")]
fn he_rewrite_contract() -> Result<&'static HeRewriteContract, String> {
    static CONTRACT: OnceLock<Result<HeRewriteContract, String>> = OnceLock::new();
    cached_contract_result(&CONTRACT, load_he_rewrite_contract_from_artifacts)
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
    _mork_eval_ms: &mut f64,
) -> Result<Vec<(String, State)>, String> {
    let (instr, _space, _out) = match state {
        State::C_State(instr, space, out) => (instr.as_ref(), space.as_ref(), out.as_ref()),
        _ => {
            return Err(format!(
                "HE MORK native state machine expects C_State(...), got {}",
                state
            ));
        },
    };
    let contract = he_rewrite_contract()?;
    let source_tag = he_instr_transition_tag(instr);
    let active_source = if source_tag == "C_Done" {
        Ok(None)
    } else {
        Ok(Some(source_tag))
    };
    let mut results = dispatch_active_source_step("HE", &contract.transition, active_source, |rule, meta| {
        let rewrite_meta = contract.rewrite_ir.rule(rule).ok_or_else(|| {
            format!("HE rewrite-ir is missing rule '{}' required by transition spec", rule)
        })?;
        if rewrite_meta.source_instr != source_tag {
            return Err(format!(
                "HE rewrite-ir mismatch: rule '{}' maps to '{}' but active source is '{}'",
                rule, rewrite_meta.source_instr, source_tag
            ));
        }
        if let Some(states) =
            he_try_execute_template_rule(rule, &meta.logical_transition_id, state, contract, limits)?
        {
            return Ok(states);
        }
        // All rules are template-driven. Reaching here means a bug.
        Err(format!(
            "HE rule '{}' ({}) was not handled by template execution",
            rule, meta.logical_transition_id
        ))
    })?;

    // Catch-all: MettaCall(atom, AtomType) with no matching rules → Return(atom).
    // This matches the Ascent backend behavior; MettaCall with AtomType shouldn't normally
    // occur (M_TypeMatch handles it at the Metta level), but when it does, the atom is
    // returned unchanged.
    if results.is_empty() && source_tag == "C_MettaCall" {
        if let State::C_State(instr_box, space, out) = state {
            if let Instr::C_MettaCall(atom, ty) = instr_box.as_ref() {
                if **ty == Atom::C_AtomType {
                    let return_state = State::C_State(
                        Box::new(Instr::C_Return(atom.clone())),
                        space.clone(),
                        out.clone(),
                    );
                    results.push(("MC_AtomType_Passthrough".to_string(), return_state));
                }
            }
        }
    }

    Ok(results)
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

    let mut mork_eval_ms = 0.0f64;
    let mut results = run_native_term_graph_with_timing(term, start_state, limits, |state| {
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
    run_mettahe_native_state_graph(term, limits)
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
