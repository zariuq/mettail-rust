//! Shared MeTTa-family pattern matching and substitution helpers.
//!
//! Language backends provide a thin adapter trait implementation for their
//! concrete term type.

use std::collections::HashMap;
use std::hash::Hash;

use crate::{PatternIndexKey, QueryIndexKey};

/// Supported binary constructor kinds for generic traversal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MettaBinaryKind {
    ExprCons,
    EqAtom,
}

/// Supported grounded operator kinds for shared MeTTa-family evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MettaGroundedOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Gt,
    Eq,
}

/// Adapter trait for MeTTa-family pattern matching/substitution.
pub trait MettaFamilyPattern: Clone + PartialEq {
    /// Pattern variable name, if this node is a pattern variable.
    fn pattern_var_name(&self) -> Option<String>;

    /// Decompose supported binary constructors.
    fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)>;

    /// Recompose a binary constructor.
    fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self;
}

/// Optional list-shape adapter for MeTTa-family expression lists.
///
/// This enables shared rule/query indexing helpers used by language backends.
pub trait MettaFamilyListForm: MettaFamilyPattern + Eq + Hash {
    /// Decompose one expression-list cons cell.
    fn expr_cons_parts(&self) -> Option<(&Self, &Self)>;

    /// True when this node is expression-list nil.
    fn is_expr_nil(&self) -> bool;
}

/// Adapter trait for shared grounded operation helpers.
pub trait MettaFamilyGrounded: MettaFamilyPattern {
    /// Extract a token-like name from this atom when it represents a surface token.
    fn token_name(&self) -> Option<String>;

    /// Build a token atom from its canonical name.
    fn make_token_atom(token: String) -> Self;

    /// Wrap a token atom as an integer grounded atom.
    fn make_grounded_int(token: Self) -> Self;

    /// Wrap a token atom as a boolean grounded atom.
    fn make_grounded_bool(token: Self) -> Self;

    /// Return the inner token atom when this is an integer grounded atom.
    fn grounded_int_token(&self) -> Option<&Self>;

    /// Return the executable grounded operator kind, if any.
    fn executable_grounded_kind(&self) -> Option<MettaGroundedOpKind>;
}

/// Adapter trait for shared MeTTa-family type/meta-type helpers.
pub trait MettaFamilyTyping: Clone + PartialEq {
    /// Return the meta type of a runtime atom, if it has one.
    fn meta_type(&self) -> Option<Self>;

    /// Distinguished MeTTa-family type constructors.
    fn atom_type() -> Self;
    fn variable_type() -> Self;
    fn expression_type() -> Self;
    fn symbol_type() -> Self;
    fn grounded_type() -> Self;

    /// Extract the argument-type list from an arrow type.
    fn arrow_arg_types(&self) -> Option<Self>;
}

/// Adapter trait for shared MeTTa-family control/error atoms.
pub trait MettaFamilyControl: Clone + PartialEq {
    /// True iff this atom is the distinguished empty value.
    fn is_empty_atom(&self) -> bool;

    /// True iff this atom is a runtime error atom.
    fn is_error_atom(&self) -> bool;

    /// Build the canonical bad-type error for this dialect.
    fn make_bad_type_error(atom: Self, expected: Self, actual: Self) -> Self;
}

/// Recursive match with binding accumulation.
pub fn metta_match_rec<T>(pattern: &T, concrete: &T, bindings: &mut HashMap<String, T>) -> bool
where
    T: MettaFamilyPattern,
{
    if let Some(var_name) = pattern.pattern_var_name() {
        if let Some(bound) = bindings.get(&var_name) {
            return bound == concrete;
        }
        bindings.insert(var_name, concrete.clone());
        return true;
    }

    match (pattern.decompose_binary(), concrete.decompose_binary()) {
        (Some((pk, pl, pr)), Some((ck, cl, cr))) if pk == ck => {
            metta_match_rec(pl, cl, bindings) && metta_match_rec(pr, cr, bindings)
        },
        _ => pattern == concrete,
    }
}

/// Pattern match wrapper returning bindings on success.
pub fn metta_match<T>(pattern: &T, concrete: &T) -> Option<HashMap<String, T>>
where
    T: MettaFamilyPattern,
{
    let mut bindings = HashMap::new();
    if metta_match_rec(pattern, concrete, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

/// Apply bindings to an atom/tree.
pub fn metta_subst<T>(atom: &T, bindings: &HashMap<String, T>) -> T
where
    T: MettaFamilyPattern,
{
    if let Some(var_name) = atom.pattern_var_name() {
        if let Some(v) = bindings.get(&var_name) {
            return v.clone();
        }
        return atom.clone();
    }

    if let Some((kind, l, r)) = atom.decompose_binary() {
        return T::recompose_binary(kind, metta_subst(l, bindings), metta_subst(r, bindings));
    }

    atom.clone()
}

/// Decode an ExprCons/ExprNil list into a `Vec`.
pub fn metta_decode_expr_list<T>(atom: &T) -> Option<Vec<T>>
where
    T: MettaFamilyListForm,
{
    let mut items = Vec::new();
    let mut cur = atom;
    loop {
        if cur.is_expr_nil() {
            return Some(items);
        }
        let (head, tail) = cur.expr_cons_parts()?;
        items.push(head.clone());
        cur = tail;
    }
}

/// Parse the canonical integer token format used by MeTTa-family grounded ints.
pub fn metta_parse_int_token<T>(token_atom: &T) -> Option<i64>
where
    T: MettaFamilyGrounded,
{
    let tok = token_atom.token_name()?;
    if let Some(rest) = tok.strip_prefix("C_neg_") {
        rest.parse::<i64>().ok().map(|n| -n)
    } else if let Some(rest) = tok.strip_prefix("C_") {
        rest.parse::<i64>().ok()
    } else {
        tok.parse::<i64>().ok()
    }
}

/// Build a canonical grounded integer atom.
pub fn metta_make_int_atom<T>(n: i64) -> T
where
    T: MettaFamilyGrounded,
{
    let token = if n < 0 {
        format!("C_neg_{}", n.unsigned_abs())
    } else {
        format!("C_{n}")
    };
    T::make_grounded_int(T::make_token_atom(token))
}

/// Build a canonical grounded boolean atom.
pub fn metta_make_bool_atom<T>(b: bool) -> T
where
    T: MettaFamilyGrounded,
{
    T::make_grounded_bool(T::make_token_atom(if b { "True" } else { "False" }.to_string()))
}

/// Extract the integer payload of a grounded integer atom.
pub fn metta_extract_gint<T>(atom: &T) -> Option<i64>
where
    T: MettaFamilyGrounded,
{
    metta_parse_int_token(atom.grounded_int_token()?)
}

/// True iff the atom names an executable grounded operator.
pub fn metta_is_executable_grounded<T>(op: &T) -> bool
where
    T: MettaFamilyGrounded,
{
    op.executable_grounded_kind().is_some()
}

/// Evaluate one grounded operation on already-decoded arguments.
pub fn metta_eval_grounded_op<T>(op: &T, args: &[T]) -> Option<T>
where
    T: MettaFamilyGrounded,
{
    match (op.executable_grounded_kind()?, args) {
        (
            MettaGroundedOpKind::Add
            | MettaGroundedOpKind::Sub
            | MettaGroundedOpKind::Mul
            | MettaGroundedOpKind::Div
            | MettaGroundedOpKind::Mod,
            [lhs, rhs],
        ) => {
            let ln = metta_extract_gint(lhs)?;
            let rn = metta_extract_gint(rhs)?;
            let result = match op.executable_grounded_kind()? {
                MettaGroundedOpKind::Add => ln.checked_add(rn)?,
                MettaGroundedOpKind::Sub => ln.checked_sub(rn)?,
                MettaGroundedOpKind::Mul => ln.checked_mul(rn)?,
                MettaGroundedOpKind::Div => {
                    if rn == 0 {
                        return None;
                    }
                    ln.checked_div(rn)?
                },
                MettaGroundedOpKind::Mod => {
                    if rn == 0 {
                        return None;
                    }
                    ln.checked_rem(rn)?
                },
                _ => unreachable!(),
            };
            Some(metta_make_int_atom(result))
        },
        (
            MettaGroundedOpKind::Lt | MettaGroundedOpKind::Gt | MettaGroundedOpKind::Eq,
            [lhs, rhs],
        ) => {
            let ln = metta_extract_gint(lhs)?;
            let rn = metta_extract_gint(rhs)?;
            let result = match op.executable_grounded_kind()? {
                MettaGroundedOpKind::Lt => ln < rn,
                MettaGroundedOpKind::Gt => ln > rn,
                MettaGroundedOpKind::Eq => ln == rn,
                _ => unreachable!(),
            };
            Some(metta_make_bool_atom(result))
        },
        _ => None,
    }
}

/// Decode an expression-list tail and evaluate a grounded operator over it.
pub fn metta_eval_grounded_dispatch<T>(op: T, args_tail: T) -> Option<T>
where
    T: MettaFamilyGrounded + MettaFamilyListForm,
{
    let args = metta_decode_expr_list(&args_tail)?;
    metta_eval_grounded_op(&op, &args)
}

/// True iff the atom has a recognized meta type.
pub fn metta_has_meta_type<T>(atom: &T) -> bool
where
    T: MettaFamilyTyping,
{
    atom.meta_type().is_some()
}

/// True iff the requested type is `AtomType` or matches the atom's meta type.
pub fn metta_type_matches_meta_or_atom<T>(atom: &T, ty: &T) -> bool
where
    T: MettaFamilyTyping,
{
    if *ty == T::atom_type() {
        return true;
    }
    match atom.meta_type() {
        Some(mt) => mt == *ty || mt == T::variable_type(),
        None => false,
    }
}

/// True iff the requested type is incompatible with the atom's meta type.
pub fn metta_type_not_matches_meta_or_atom<T>(atom: &T, ty: &T) -> bool
where
    T: MettaFamilyTyping,
{
    match atom.meta_type() {
        Some(mt) => *ty != T::atom_type() && mt != T::variable_type() && mt != *ty,
        None => false,
    }
}

/// True iff evaluation should move from `Metta` to `TypeCast`.
pub fn metta_needs_type_cast<T>(atom: &T, ty: &T) -> bool
where
    T: MettaFamilyTyping + MettaFamilyListForm,
{
    ((matches!(atom.meta_type(), Some(mt) if mt == T::symbol_type() || mt == T::grounded_type()))
        && metta_type_not_matches_meta_or_atom(atom, ty))
        || (atom.is_expr_nil() && metta_type_not_matches_meta_or_atom(atom, ty))
}

/// True iff evaluation should move from `Metta` to `InterpExpr`.
pub fn metta_needs_interp_expr<T>(atom: &T, ty: &T) -> bool
where
    T: MettaFamilyTyping,
{
    matches!(atom.meta_type(), Some(mt) if mt == T::expression_type())
        && metta_type_not_matches_meta_or_atom(atom, ty)
}

/// True iff the atom is recognized but not an expression.
pub fn metta_not_expression<T>(atom: &T) -> bool
where
    T: MettaFamilyTyping,
{
    matches!(atom.meta_type(), Some(mt) if mt != T::expression_type())
}

/// Extract the argument-type payload from a function type.
pub fn metta_func_arg_types<T>(op_type: &T) -> Option<T>
where
    T: MettaFamilyTyping,
{
    op_type.arrow_arg_types()
}

/// True iff this atom is the MeTTa-family distinguished empty value.
pub fn metta_is_empty<T>(atom: &T) -> bool
where
    T: MettaFamilyControl,
{
    atom.is_empty_atom()
}

/// True iff this atom is a MeTTa-family runtime error value.
pub fn metta_is_error<T>(atom: &T) -> bool
where
    T: MettaFamilyControl,
{
    atom.is_error_atom()
}

/// True iff `new` changed from `orig` to the distinguished empty value.
pub fn metta_changed_to_empty<T>(orig: &T, new: &T) -> bool
where
    T: MettaFamilyControl,
{
    metta_is_empty(new) && new != orig
}

/// True iff `new` changed from `orig` to a runtime error value.
pub fn metta_changed_to_error<T>(orig: &T, new: &T) -> bool
where
    T: MettaFamilyControl,
{
    metta_is_error(new) && new != orig
}

/// Build the dialect-specific bad-type error atom.
pub fn metta_make_bad_type_error<T>(atom: &T, expected: &T, actual: &T) -> T
where
    T: MettaFamilyControl,
{
    T::make_bad_type_error(atom.clone(), expected.clone(), actual.clone())
}

/// True when a pattern subtree contains at least one pattern variable.
pub fn metta_pattern_contains_var<T>(atom: &T) -> bool
where
    T: MettaFamilyPattern,
{
    if atom.pattern_var_name().is_some() {
        return true;
    }
    if let Some((_, left, right)) = atom.decompose_binary() {
        return metta_pattern_contains_var(left) || metta_pattern_contains_var(right);
    }
    false
}

/// Build a continuation-return state from one result and one continuation.
pub fn metta_return_to_continuation<T, S>(result: &T, k: &T, mk_state: impl FnOnce(T, T) -> S) -> S
where
    T: Clone,
{
    mk_state(result.clone(), k.clone())
}

/// Build a next state from an already-separated head/rest pair.
pub fn metta_step_head_rest_to_state<T, I, S>(
    head: &T,
    rest: &T,
    build_instr: impl FnOnce(&T, &T) -> I,
    build_out: impl FnOnce(&T, &T) -> T,
    mk_state: impl FnOnce(I, T) -> S,
) -> S
where
    T: Clone,
{
    mk_state(build_instr(head, rest), build_out(head, rest))
}

/// Build a next state when an expression list is a cons cell.
pub fn metta_step_expr_cons_head_rest_to_state<T, I, S>(
    expr: &T,
    build_instr: impl FnOnce(&T, &T) -> I,
    build_out: impl FnOnce(&T, &T) -> T,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: MettaFamilyListForm,
{
    let (head, rest) = expr.expr_cons_parts()?;
    Some(metta_step_head_rest_to_state(
        head,
        rest,
        build_instr,
        build_out,
        mk_state,
    ))
}

/// Build a next state when an expression list is nil.
pub fn metta_step_expr_nil_to_state<T, I, S>(
    expr: &T,
    build_instr: impl FnOnce() -> I,
    out: &T,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: MettaFamilyListForm + Clone,
{
    expr.is_expr_nil().then(|| mk_state(build_instr(), out.clone()))
}

/// Build a next state while preserving the current output/continuation payload.
pub fn metta_step_to_same_out_state<T, I, S>(
    out: &T,
    build_instr: impl FnOnce() -> I,
    mk_state: impl FnOnce(I, T) -> S,
) -> S
where
    T: Clone,
{
    mk_state(build_instr(), out.clone())
}

/// Conditionally build a next state while preserving the current
/// output/continuation payload.
pub fn metta_step_to_same_out_state_if<T, I, S>(
    out: &T,
    pred: bool,
    build_instr: impl FnOnce() -> I,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    pred.then(|| metta_step_to_same_out_state(out, build_instr, mk_state))
}

/// Conditionally build a next state from one optional payload while preserving
/// the current output/continuation payload.
pub fn metta_step_to_same_out_state_if_some<T, U, I, S>(
    out: &T,
    value: Option<U>,
    build_instr: impl FnOnce(U) -> I,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    value.map(|value| metta_step_to_same_out_state(out, || build_instr(value), mk_state))
}

/// Build a state that returns a result to the current output value.
pub fn metta_return_to_out<T, S>(result: &T, out: &T, mk_state: impl FnOnce(T, T) -> S) -> S
where
    T: Clone,
{
    mk_state(result.clone(), out.clone())
}

/// Conditionally build a state that returns a result to the current output value.
pub fn metta_return_to_out_if<T, S>(
    result: &T,
    out: &T,
    pred: impl FnOnce(&T) -> bool,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    pred(result).then(|| metta_return_to_out(result, out, mk_state))
}

/// Build a continuation-return state whose result is a singleton expression list.
pub fn metta_return_singleton_expr_to_continuation<T, S>(
    result: &T,
    k: &T,
    mk_expr_cons: impl Fn(T, T) -> T,
    mk_expr_nil: impl FnOnce() -> T,
    mk_state: impl FnOnce(T, T) -> S,
) -> S
where
    T: Clone,
{
    mk_state(mk_expr_cons(result.clone(), mk_expr_nil()), k.clone())
}

/// Build a continuation-return state whose result is one cons-cell extending an existing head.
pub fn metta_return_cons_expr_to_continuation<T, S>(
    head: &T,
    result: &T,
    k: &T,
    mk_expr_cons: impl Fn(T, T) -> T,
    mk_state: impl FnOnce(T, T) -> S,
) -> S
where
    T: Clone,
{
    mk_state(mk_expr_cons(head.clone(), result.clone()), k.clone())
}

/// Continue with a new state only when `result` is a meta-level value.
pub fn metta_continue_state_if_meta_result<T, S>(
    result: &T,
    is_meta: impl Fn(&T) -> bool,
    build_state: impl FnOnce(&T) -> S,
) -> Option<S>
where
    T: Clone,
{
    is_meta(result).then(|| build_state(result))
}

/// Conditionally build a next state from a meta-level result by separately
/// constructing the next instruction and next output/continuation payload.
pub fn metta_continue_to_state_if_meta_result<T, I, S>(
    result: &T,
    is_meta: impl Fn(&T) -> bool,
    build_instr: impl FnOnce(&T) -> I,
    build_out: impl FnOnce(&T) -> T,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    is_meta(result).then(|| mk_state(build_instr(result), build_out(result)))
}

/// Conditionally continue to a next state when a MeTTa-family expression-list
/// tail is a cons cell and the current result is meta-level.
pub fn metta_continue_with_expr_tail_if_meta_result<T, I, S>(
    result: &T,
    tail: &T,
    is_meta: impl Fn(&T) -> bool,
    build_instr_from_tail: impl FnOnce(&T, &T) -> I,
    build_out_from_result: impl FnOnce(&T) -> T,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: MettaFamilyListForm + Clone,
{
    if !is_meta(result) {
        return None;
    }
    let (head, rest) = tail.expr_cons_parts()?;
    Some(mk_state(
        build_instr_from_tail(head, rest),
        build_out_from_result(result),
    ))
}

/// Conditionally continue to a next state when a MeTTa-family expression-list
/// tail is nil and the current result is meta-level.
pub fn metta_continue_with_expr_nil_tail_if_meta_result<T, I, S>(
    result: &T,
    tail: &T,
    is_meta: impl Fn(&T) -> bool,
    build_instr: impl FnOnce() -> I,
    build_out_from_result: impl FnOnce(&T) -> T,
    mk_state: impl FnOnce(I, T) -> S,
) -> Option<S>
where
    T: MettaFamilyListForm + Clone,
{
    if !is_meta(result) || !tail.is_expr_nil() {
        return None;
    }
    Some(mk_state(build_instr(), build_out_from_result(result)))
}

/// Conditionally return a singleton expression list through a continuation
/// when `result` is a meta-level value.
pub fn metta_return_singleton_expr_to_continuation_if_meta_result<T, S>(
    result: &T,
    k: &T,
    is_meta: impl Fn(&T) -> bool,
    mk_expr_cons: impl Fn(T, T) -> T,
    mk_expr_nil: impl FnOnce() -> T,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    is_meta(result).then(|| {
        metta_return_singleton_expr_to_continuation(result, k, mk_expr_cons, mk_expr_nil, mk_state)
    })
}

/// Conditionally return a singleton expression list through a continuation
/// when `tail` is expression-list nil and `result` is a meta-level value.
pub fn metta_return_singleton_expr_to_continuation_if_meta_result_and_nil_tail<T, S>(
    result: &T,
    tail: &T,
    k: &T,
    is_meta: impl Fn(&T) -> bool,
    mk_expr_cons: impl Fn(T, T) -> T,
    mk_expr_nil: impl FnOnce() -> T,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: MettaFamilyListForm + Clone,
{
    if !tail.is_expr_nil() {
        return None;
    }
    metta_return_singleton_expr_to_continuation_if_meta_result(
        result,
        k,
        is_meta,
        mk_expr_cons,
        mk_expr_nil,
        mk_state,
    )
}

/// Conditionally extend an expression list through a continuation when
/// `result` is a meta-level value.
pub fn metta_return_cons_expr_to_continuation_if_meta_result<T, S>(
    head: &T,
    result: &T,
    k: &T,
    is_meta: impl Fn(&T) -> bool,
    mk_expr_cons: impl Fn(T, T) -> T,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    is_meta(result).then(|| {
        metta_return_cons_expr_to_continuation(head, result, k, mk_expr_cons, mk_state)
    })
}

/// Conditionally bubble a return result through a continuation.
pub fn metta_bubble_return_to_continuation_if<T, S>(
    out: &T,
    result: &T,
    extract_k: impl Fn(&T) -> Option<&T>,
    pred: impl Fn(&T, &T) -> bool,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: Clone,
{
    let k = extract_k(out)?;
    pred(out, result).then(|| metta_return_to_continuation(result, k, mk_state))
}

/// Conditionally bubble a return result through a continuation when the result
/// is the distinguished empty value.
pub fn metta_bubble_empty_to_continuation_if<T, S>(
    out: &T,
    result: &T,
    extract_k: impl Fn(&T) -> Option<&T>,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: MettaFamilyControl + Clone,
{
    metta_bubble_return_to_continuation_if(out, result, extract_k, |_, result| {
        metta_is_empty(result)
    }, mk_state)
}

/// Conditionally bubble a return result through a continuation when the result
/// is a runtime error value.
pub fn metta_bubble_error_to_continuation_if<T, S>(
    out: &T,
    result: &T,
    extract_k: impl Fn(&T) -> Option<&T>,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: MettaFamilyControl + Clone,
{
    metta_bubble_return_to_continuation_if(out, result, extract_k, |_, result| {
        metta_is_error(result)
    }, mk_state)
}

/// Conditionally bubble a return result through a continuation when the result
/// changed from the original payload to the distinguished empty value.
pub fn metta_bubble_changed_to_empty_if<T, S>(
    out: &T,
    result: &T,
    extract_k: impl Fn(&T) -> Option<&T>,
    extract_orig: impl Fn(&T) -> Option<&T>,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: MettaFamilyControl + Clone,
{
    metta_bubble_return_to_continuation_if(out, result, extract_k, |out, result| {
        extract_orig(out)
            .map(|orig| metta_changed_to_empty(orig, result))
            .unwrap_or(false)
    }, mk_state)
}

/// Conditionally bubble a return result through a continuation when the result
/// changed from the original payload to a runtime error value.
pub fn metta_bubble_changed_to_error_if<T, S>(
    out: &T,
    result: &T,
    extract_k: impl Fn(&T) -> Option<&T>,
    extract_orig: impl Fn(&T) -> Option<&T>,
    mk_state: impl FnOnce(T, T) -> S,
) -> Option<S>
where
    T: MettaFamilyControl + Clone,
{
    metta_bubble_return_to_continuation_if(out, result, extract_k, |out, result| {
        extract_orig(out)
            .map(|orig| metta_changed_to_error(orig, result))
            .unwrap_or(false)
    }, mk_state)
}

fn expr_head_and_arity<T>(atom: &T) -> Option<(&T, usize)>
where
    T: MettaFamilyListForm,
{
    let mut cur = atom;
    let mut head: Option<&T> = None;
    let mut arity = 0usize;
    loop {
        if cur.is_expr_nil() {
            return head.map(|h| (h, arity));
        }
        if let Some((h, t)) = cur.expr_cons_parts() {
            if head.is_none() {
                head = Some(h);
            }
            arity = arity.saturating_add(1);
            cur = t;
            continue;
        }
        return None;
    }
}

/// Return the head/operator of an expression list, if present.
pub fn metta_expr_head<T>(atom: &T) -> Option<&T>
where
    T: MettaFamilyListForm,
{
    expr_head_and_arity(atom).map(|(head, _)| head)
}

/// Shared index keying for rule-pattern LHS classification.
pub fn metta_pattern_index_key<T>(lhs: &T) -> PatternIndexKey<T>
where
    T: MettaFamilyListForm,
{
    if let Some((head, arity)) = expr_head_and_arity(lhs) {
        if head.pattern_var_name().is_some() {
            return PatternIndexKey::ListArityAny { arity };
        }
        return PatternIndexKey::ListHeadConst { arity, head: head.clone() };
    }

    if lhs.pattern_var_name().is_some() {
        PatternIndexKey::AtomAny
    } else {
        PatternIndexKey::AtomConst(lhs.clone())
    }
}

/// Shared index keying for query expression classification.
pub fn metta_query_index_key<T>(atom: &T) -> QueryIndexKey<T>
where
    T: MettaFamilyListForm,
{
    if let Some((head, arity)) = expr_head_and_arity(atom) {
        return QueryIndexKey::List {
            arity,
            head: if head.pattern_var_name().is_some() {
                None
            } else {
                Some(head.clone())
            },
        };
    }

    if atom.pattern_var_name().is_some() {
        QueryIndexKey::AtomOther
    } else {
        QueryIndexKey::AtomConst(atom.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        metta_bubble_changed_to_empty_if, metta_bubble_changed_to_error_if,
        metta_bubble_empty_to_continuation_if, metta_bubble_error_to_continuation_if,
        metta_continue_state_if_meta_result, metta_continue_to_state_if_meta_result,
        metta_continue_with_expr_nil_tail_if_meta_result,
        metta_continue_with_expr_tail_if_meta_result,
        metta_changed_to_empty, metta_changed_to_error,
        metta_decode_expr_list, metta_eval_grounded_dispatch, metta_is_executable_grounded,
        metta_is_empty, metta_is_error, metta_make_bad_type_error,
        metta_func_arg_types, metta_has_meta_type, metta_needs_interp_expr,
        metta_needs_type_cast, metta_not_expression,
        metta_match, metta_pattern_contains_var, metta_pattern_index_key, metta_query_index_key,
        metta_parse_int_token,
        metta_return_cons_expr_to_continuation_if_meta_result,
        metta_return_singleton_expr_to_continuation_if_meta_result_and_nil_tail,
        metta_return_singleton_expr_to_continuation_if_meta_result, metta_return_to_out,
        metta_return_to_out_if, metta_step_expr_cons_head_rest_to_state,
        metta_step_expr_nil_to_state, metta_step_head_rest_to_state,
        metta_step_to_same_out_state, metta_step_to_same_out_state_if,
        metta_step_to_same_out_state_if_some, metta_subst,
        metta_type_matches_meta_or_atom, metta_type_not_matches_meta_or_atom, MettaBinaryKind,
        MettaFamilyControl, MettaFamilyGrounded, MettaFamilyListForm, MettaFamilyPattern,
        MettaFamilyTyping,
        MettaGroundedOpKind,
    };
    use crate::{PatternIndexKey, QueryIndexKey};
    use std::collections::HashMap;

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum T {
        Var(&'static str),
        Sym(&'static str),
        Cons(Box<T>, Box<T>),
        Eq(Box<T>, Box<T>),
        Nil,
    }

    impl MettaFamilyPattern for T {
        fn pattern_var_name(&self) -> Option<String> {
            match self {
                T::Var(v) => Some((*v).to_string()),
                _ => None,
            }
        }

        fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)> {
            match self {
                T::Cons(h, t) => Some((MettaBinaryKind::ExprCons, h, t)),
                T::Eq(l, r) => Some((MettaBinaryKind::EqAtom, l, r)),
                _ => None,
            }
        }

        fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self {
            match kind {
                MettaBinaryKind::ExprCons => T::Cons(Box::new(left), Box::new(right)),
                MettaBinaryKind::EqAtom => T::Eq(Box::new(left), Box::new(right)),
            }
        }
    }

    impl MettaFamilyListForm for T {
        fn expr_cons_parts(&self) -> Option<(&Self, &Self)> {
            match self {
                T::Cons(h, t) => Some((h, t)),
                _ => None,
            }
        }

        fn is_expr_nil(&self) -> bool {
            matches!(self, T::Nil)
        }
    }

    #[test]
    fn match_variable_consistency() {
        let pat = T::Cons(Box::new(T::Var("x")), Box::new(T::Var("x")));
        let ok = T::Cons(Box::new(T::Sym("a")), Box::new(T::Sym("a")));
        let bad = T::Cons(Box::new(T::Sym("a")), Box::new(T::Sym("b")));
        assert!(metta_match(&pat, &ok).is_some());
        assert!(metta_match(&pat, &bad).is_none());
    }

    #[test]
    fn subst_replaces_vars() {
        let atom = T::Eq(
            Box::new(T::Var("x")),
            Box::new(T::Cons(Box::new(T::Var("y")), Box::new(T::Sym("z")))),
        );
        let mut b = HashMap::new();
        b.insert("x".to_string(), T::Sym("left"));
        b.insert("y".to_string(), T::Sym("head"));
        let out = metta_subst(&atom, &b);
        let expected = T::Eq(
            Box::new(T::Sym("left")),
            Box::new(T::Cons(Box::new(T::Sym("head")), Box::new(T::Sym("z")))),
        );
        assert_eq!(out, expected);
    }

    #[test]
    fn pattern_key_helpers_work() {
        let pat_list = T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil));
        let pat_var_head = T::Cons(Box::new(T::Var("x")), Box::new(T::Nil));
        let pat_atom_var = T::Var("y");
        let query_list = T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil));

        assert!(!metta_pattern_contains_var(&pat_list));
        assert!(metta_pattern_contains_var(&pat_var_head));
        assert!(metta_pattern_contains_var(&pat_atom_var));

        assert_eq!(
            metta_pattern_index_key(&pat_list),
            PatternIndexKey::ListHeadConst { arity: 1, head: T::Sym("h") }
        );
        assert_eq!(
            metta_pattern_index_key(&pat_var_head),
            PatternIndexKey::ListArityAny { arity: 1 }
        );
        assert_eq!(metta_pattern_index_key(&pat_atom_var), PatternIndexKey::AtomAny);
        assert_eq!(
            metta_query_index_key(&query_list),
            QueryIndexKey::List { arity: 1, head: Some(T::Sym("h")) }
        );
    }

    #[test]
    fn meta_result_helpers_only_fire_when_predicate_holds() {
        let state = metta_continue_state_if_meta_result(&T::Sym("ok"), |_| true, |r| {
            T::Cons(Box::new(r.clone()), Box::new(T::Nil))
        });
        assert_eq!(state, Some(T::Cons(Box::new(T::Sym("ok")), Box::new(T::Nil))));

        let singleton = metta_return_singleton_expr_to_continuation_if_meta_result(
            &T::Sym("x"),
            &T::Sym("k"),
            |_| true,
            |h, t| T::Cons(Box::new(h), Box::new(t)),
            || T::Nil,
            |result, k| T::Eq(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            singleton,
            Some(T::Eq(
                Box::new(T::Cons(Box::new(T::Sym("x")), Box::new(T::Nil))),
                Box::new(T::Sym("k"))
            ))
        );

        let cons = metta_return_cons_expr_to_continuation_if_meta_result(
            &T::Sym("h"),
            &T::Sym("t"),
            &T::Sym("k"),
            |_| true,
            |h, t| T::Cons(Box::new(h), Box::new(t)),
            |result, k| T::Eq(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            cons,
            Some(T::Eq(
                Box::new(T::Cons(Box::new(T::Sym("h")), Box::new(T::Sym("t")))),
                Box::new(T::Sym("k"))
            ))
        );

        let none = metta_return_singleton_expr_to_continuation_if_meta_result(
            &T::Sym("x"),
            &T::Sym("k"),
            |_| false,
            |h, t| T::Cons(Box::new(h), Box::new(t)),
            || T::Nil,
            |result, k| T::Eq(Box::new(result), Box::new(k)),
        );
        assert_eq!(none, None);

        let next = metta_continue_to_state_if_meta_result(
            &T::Sym("head"),
            |_| true,
            |r| T::Cons(Box::new(r.clone()), Box::new(T::Sym("instr"))),
            |r| T::Cons(Box::new(r.clone()), Box::new(T::Sym("out"))),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(
            next,
            Some(T::Eq(
                Box::new(T::Cons(
                    Box::new(T::Sym("head")),
                    Box::new(T::Sym("instr"))
                )),
                Box::new(T::Cons(
                    Box::new(T::Sym("head")),
                    Box::new(T::Sym("out"))
                ))
            ))
        );

        let from_tail = metta_continue_with_expr_tail_if_meta_result(
            &T::Sym("head"),
            &T::Cons(Box::new(T::Sym("next")), Box::new(T::Nil)),
            |_| true,
            |head, rest| T::Cons(Box::new(head.clone()), Box::new(rest.clone())),
            |r| T::Cons(Box::new(r.clone()), Box::new(T::Sym("k"))),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(
            from_tail,
            Some(T::Eq(
                Box::new(T::Cons(Box::new(T::Sym("next")), Box::new(T::Nil))),
                Box::new(T::Cons(Box::new(T::Sym("head")), Box::new(T::Sym("k"))))
            ))
        );

        let from_nil_tail = metta_continue_with_expr_nil_tail_if_meta_result(
            &T::Sym("head"),
            &T::Nil,
            |_| true,
            || T::Sym("instr"),
            |r| T::Cons(Box::new(r.clone()), Box::new(T::Sym("k"))),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(
            from_nil_tail,
            Some(T::Eq(
                Box::new(T::Sym("instr")),
                Box::new(T::Cons(Box::new(T::Sym("head")), Box::new(T::Sym("k"))))
            ))
        );

        let singleton_from_nil_tail =
            metta_return_singleton_expr_to_continuation_if_meta_result_and_nil_tail(
                &T::Sym("x"),
                &T::Nil,
                &T::Sym("k"),
                |_| true,
                |h, t| T::Cons(Box::new(h), Box::new(t)),
                || T::Nil,
                |result, k| T::Eq(Box::new(result), Box::new(k)),
            );
        assert_eq!(
            singleton_from_nil_tail,
            Some(T::Eq(
                Box::new(T::Cons(Box::new(T::Sym("x")), Box::new(T::Nil))),
                Box::new(T::Sym("k"))
            ))
        );
    }

    #[test]
    fn return_to_out_helpers_clone_result_and_guard_predicate() {
        let direct = metta_return_to_out(&T::Sym("ok"), &T::Nil, |result, out| {
            T::Eq(Box::new(result), Box::new(out))
        });
        assert_eq!(direct, T::Eq(Box::new(T::Sym("ok")), Box::new(T::Nil)));

        let some = metta_return_to_out_if(&T::Sym("ok"), &T::Nil, |_| true, |result, out| {
            T::Eq(Box::new(result), Box::new(out))
        });
        assert_eq!(
            some,
            Some(T::Eq(Box::new(T::Sym("ok")), Box::new(T::Nil)))
        );

        let none = metta_return_to_out_if(&T::Nil, &T::Sym("out"), |_| false, |result, out| {
            T::Eq(Box::new(result), Box::new(out))
        });
        assert_eq!(none, None);
    }

    #[test]
    fn bubble_helpers_cover_empty_error_and_changed_transitions() {
        let empty = metta_bubble_empty_to_continuation_if(
            &TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::OtherType)),
            &TypedT::Empty,
            |out| match out {
                TypedT::Expr(_, k) => Some(k.as_ref()),
                _ => None,
            },
            |result, k| TypedT::Expr(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            empty,
            Some(TypedT::Expr(
                Box::new(TypedT::Empty),
                Box::new(TypedT::OtherType)
            ))
        );

        let error = metta_bubble_error_to_continuation_if(
            &TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::OtherType)),
            &TypedT::Error,
            |out| match out {
                TypedT::Expr(_, k) => Some(k.as_ref()),
                _ => None,
            },
            |result, k| TypedT::Expr(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            error,
            Some(TypedT::Expr(
                Box::new(TypedT::Error),
                Box::new(TypedT::OtherType)
            ))
        );

        let changed_empty = metta_bubble_changed_to_empty_if(
            &TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::OtherType)),
            &TypedT::Empty,
            |out| match out {
                TypedT::Expr(_, k) => Some(k.as_ref()),
                _ => None,
            },
            |out| match out {
                TypedT::Expr(orig, _) => Some(orig.as_ref()),
                _ => None,
            },
            |result, k| TypedT::Expr(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            changed_empty,
            Some(TypedT::Expr(
                Box::new(TypedT::Empty),
                Box::new(TypedT::OtherType)
            ))
        );

        let changed_error = metta_bubble_changed_to_error_if(
            &TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::OtherType)),
            &TypedT::Error,
            |out| match out {
                TypedT::Expr(_, k) => Some(k.as_ref()),
                _ => None,
            },
            |out| match out {
                TypedT::Expr(orig, _) => Some(orig.as_ref()),
                _ => None,
            },
            |result, k| TypedT::Expr(Box::new(result), Box::new(k)),
        );
        assert_eq!(
            changed_error,
            Some(TypedT::Expr(
                Box::new(TypedT::Error),
                Box::new(TypedT::OtherType)
            ))
        );
    }

    #[test]
    fn same_out_state_helpers_preserve_output_payload() {
        let direct = metta_step_to_same_out_state(&T::Sym("out"), || T::Sym("instr"), |instr, out| {
            T::Eq(Box::new(instr), Box::new(out))
        });
        assert_eq!(direct, T::Eq(Box::new(T::Sym("instr")), Box::new(T::Sym("out"))));

        let some = metta_step_to_same_out_state_if(
            &T::Sym("k"),
            true,
            || T::Sym("step"),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(some, Some(T::Eq(Box::new(T::Sym("step")), Box::new(T::Sym("k")))));

        let none = metta_step_to_same_out_state_if(
            &T::Sym("k"),
            false,
            || T::Sym("step"),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(none, None);

        let some_from_option =
            metta_step_to_same_out_state_if_some(&T::Sym("k"), Some(T::Sym("step")), |instr| instr, |instr, out| {
                T::Eq(Box::new(instr), Box::new(out))
            });
        assert_eq!(
            some_from_option,
            Some(T::Eq(Box::new(T::Sym("step")), Box::new(T::Sym("k"))))
        );

        let none_from_option = metta_step_to_same_out_state_if_some(
            &T::Sym("k"),
            Option::<T>::None,
            |instr| instr,
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(none_from_option, None);
    }

    #[test]
    fn expr_head_rest_state_helpers_follow_list_shape() {
        let direct = metta_step_head_rest_to_state(
            &T::Sym("h"),
            &T::Nil,
            |head, _rest| head.clone(),
            |head, rest| T::Cons(Box::new(head.clone()), Box::new(rest.clone())),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(
            direct,
            T::Eq(
                Box::new(T::Sym("h")),
                Box::new(T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil)))
            )
        );

        let expr = T::Cons(Box::new(T::Sym("h")), Box::new(T::Nil));
        let from_cons = metta_step_expr_cons_head_rest_to_state(
            &expr,
            |head, _rest| head.clone(),
            |head, rest| T::Cons(Box::new(head.clone()), Box::new(rest.clone())),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(from_cons, Some(direct.clone()));

        let from_nil = metta_step_expr_nil_to_state(
            &T::Nil,
            || T::Sym("instr"),
            &T::Sym("out"),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(
            from_nil,
            Some(T::Eq(Box::new(T::Sym("instr")), Box::new(T::Sym("out"))))
        );

        let none = metta_step_expr_cons_head_rest_to_state(
            &T::Sym("atom"),
            |head, _rest| head.clone(),
            |head, rest| T::Cons(Box::new(head.clone()), Box::new(rest.clone())),
            |instr, out| T::Eq(Box::new(instr), Box::new(out)),
        );
        assert_eq!(none, None);
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum GroundedT {
        Tok(String),
        GInt(Box<GroundedT>),
        GBool(Box<GroundedT>),
        Op(MettaGroundedOpKind),
        Cons(Box<GroundedT>, Box<GroundedT>),
        Nil,
    }

    impl MettaFamilyPattern for GroundedT {
        fn pattern_var_name(&self) -> Option<String> {
            None
        }

        fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)> {
            match self {
                GroundedT::Cons(head, tail) => Some((MettaBinaryKind::ExprCons, head, tail)),
                _ => None,
            }
        }

        fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self {
            match kind {
                MettaBinaryKind::ExprCons => GroundedT::Cons(Box::new(left), Box::new(right)),
                MettaBinaryKind::EqAtom => GroundedT::Cons(Box::new(left), Box::new(right)),
            }
        }
    }

    impl MettaFamilyListForm for GroundedT {
        fn expr_cons_parts(&self) -> Option<(&Self, &Self)> {
            match self {
                GroundedT::Cons(head, tail) => Some((head, tail)),
                _ => None,
            }
        }

        fn is_expr_nil(&self) -> bool {
            matches!(self, GroundedT::Nil)
        }
    }

    impl MettaFamilyGrounded for GroundedT {
        fn token_name(&self) -> Option<String> {
            match self {
                GroundedT::Tok(tok) => Some(tok.clone()),
                _ => None,
            }
        }

        fn make_token_atom(token: String) -> Self {
            GroundedT::Tok(token)
        }

        fn make_grounded_int(token: Self) -> Self {
            GroundedT::GInt(Box::new(token))
        }

        fn make_grounded_bool(token: Self) -> Self {
            GroundedT::GBool(Box::new(token))
        }

        fn grounded_int_token(&self) -> Option<&Self> {
            match self {
                GroundedT::GInt(tok) => Some(tok.as_ref()),
                _ => None,
            }
        }

        fn executable_grounded_kind(&self) -> Option<MettaGroundedOpKind> {
            match self {
                GroundedT::Op(kind) => Some(*kind),
                _ => None,
            }
        }
    }

    #[test]
    fn grounded_eval_helpers_cover_ints_bools_and_list_decode() {
        let args = GroundedT::Cons(
            Box::new(GroundedT::GInt(Box::new(GroundedT::Tok("C_2".to_string())))),
            Box::new(GroundedT::Cons(
                Box::new(GroundedT::GInt(Box::new(GroundedT::Tok("C_3".to_string())))),
                Box::new(GroundedT::Nil),
            )),
        );

        assert_eq!(
            metta_decode_expr_list(&args),
            Some(vec![
                GroundedT::GInt(Box::new(GroundedT::Tok("C_2".to_string()))),
                GroundedT::GInt(Box::new(GroundedT::Tok("C_3".to_string())))
            ])
        );
        assert!(metta_is_executable_grounded(&GroundedT::Op(MettaGroundedOpKind::Add)));
        assert_eq!(
            metta_eval_grounded_dispatch(GroundedT::Op(MettaGroundedOpKind::Add), args.clone()),
            Some(GroundedT::GInt(Box::new(GroundedT::Tok("C_5".to_string()))))
        );
        assert_eq!(
            metta_eval_grounded_dispatch(GroundedT::Op(MettaGroundedOpKind::Lt), args),
            Some(GroundedT::GBool(Box::new(GroundedT::Tok("True".to_string()))))
        );
        assert_eq!(
            metta_parse_int_token(&GroundedT::Tok("C_neg_7".to_string())),
            Some(-7)
        );
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum TypedT {
        Sym,
        Expr(Box<TypedT>, Box<TypedT>),
        Nil,
        Empty,
        Error,
        AtomType,
        VariableType,
        ExpressionType,
        SymbolType,
        GroundedType,
        ArrowType(Box<TypedT>, Box<TypedT>),
        BadType(Box<TypedT>, Box<TypedT>),
        OtherType,
    }

    impl MettaFamilyTyping for TypedT {
        fn meta_type(&self) -> Option<Self> {
            match self {
                TypedT::Sym => Some(TypedT::SymbolType),
                TypedT::Expr(_, _) | TypedT::Nil => Some(TypedT::ExpressionType),
                _ => None,
            }
        }

        fn atom_type() -> Self {
            TypedT::AtomType
        }

        fn variable_type() -> Self {
            TypedT::VariableType
        }

        fn expression_type() -> Self {
            TypedT::ExpressionType
        }

        fn symbol_type() -> Self {
            TypedT::SymbolType
        }

        fn grounded_type() -> Self {
            TypedT::GroundedType
        }

        fn arrow_arg_types(&self) -> Option<Self> {
            match self {
                TypedT::ArrowType(args, _) => Some((**args).clone()),
                _ => None,
            }
        }
    }

    impl MettaFamilyPattern for TypedT {
        fn pattern_var_name(&self) -> Option<String> {
            None
        }

        fn decompose_binary(&self) -> Option<(MettaBinaryKind, &Self, &Self)> {
            match self {
                TypedT::Expr(head, tail) => Some((MettaBinaryKind::ExprCons, head, tail)),
                _ => None,
            }
        }

        fn recompose_binary(kind: MettaBinaryKind, left: Self, right: Self) -> Self {
            match kind {
                MettaBinaryKind::ExprCons => TypedT::Expr(Box::new(left), Box::new(right)),
                MettaBinaryKind::EqAtom => TypedT::Expr(Box::new(left), Box::new(right)),
            }
        }
    }

    impl MettaFamilyListForm for TypedT {
        fn expr_cons_parts(&self) -> Option<(&Self, &Self)> {
            match self {
                TypedT::Expr(head, tail) => Some((head, tail)),
                _ => None,
            }
        }

        fn is_expr_nil(&self) -> bool {
            matches!(self, TypedT::Nil)
        }
    }

    impl MettaFamilyControl for TypedT {
        fn is_empty_atom(&self) -> bool {
            matches!(self, TypedT::Empty)
        }

        fn is_error_atom(&self) -> bool {
            matches!(self, TypedT::Error | TypedT::BadType(_, _))
        }

        fn make_bad_type_error(atom: Self, expected: Self, actual: Self) -> Self {
            TypedT::Expr(
                Box::new(atom),
                Box::new(TypedT::BadType(Box::new(expected), Box::new(actual))),
            )
        }
    }

    #[test]
    fn typing_helpers_cover_meta_match_cast_interp_and_arrow() {
        assert!(metta_has_meta_type(&TypedT::Sym));
        assert!(metta_type_matches_meta_or_atom(&TypedT::Sym, &TypedT::AtomType));
        assert!(metta_type_matches_meta_or_atom(
            &TypedT::Sym,
            &TypedT::SymbolType
        ));
        assert!(metta_type_not_matches_meta_or_atom(
            &TypedT::Sym,
            &TypedT::OtherType
        ));
        assert!(metta_needs_type_cast(&TypedT::Sym, &TypedT::OtherType));
        assert!(metta_needs_interp_expr(
            &TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::Nil)),
            &TypedT::OtherType
        ));
        assert!(metta_not_expression(&TypedT::Sym));
        assert_eq!(
            metta_func_arg_types(&TypedT::ArrowType(
                Box::new(TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::Nil))),
                Box::new(TypedT::OtherType),
            )),
            Some(TypedT::Expr(Box::new(TypedT::Sym), Box::new(TypedT::Nil)))
        );
    }

    #[test]
    fn control_helpers_cover_empty_error_and_bad_type() {
        assert!(metta_is_empty(&TypedT::Empty));
        assert!(metta_is_error(&TypedT::Error));
        assert!(metta_changed_to_empty(&TypedT::Sym, &TypedT::Empty));
        assert!(metta_changed_to_error(&TypedT::Sym, &TypedT::Error));
        assert_eq!(
            metta_make_bad_type_error(&TypedT::Sym, &TypedT::AtomType, &TypedT::OtherType),
            TypedT::Expr(
                Box::new(TypedT::Sym),
                Box::new(TypedT::BadType(
                    Box::new(TypedT::AtomType),
                    Box::new(TypedT::OtherType)
                ))
            )
        );
    }
}
