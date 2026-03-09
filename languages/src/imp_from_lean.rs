#![allow(
    non_local_definitions,
    non_camel_case_types,
    non_snake_case,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
use mettail_runtime::{Language, Term};

include!("generated/imp_language_working.rs");

use crate::imp_surface::{parse_imp_term, parse_imp_term_for_env};

#[cfg(feature = "mork-backend")]
use crate::artifact_contract::{PatternNode, RewriteIRRule};
#[cfg(feature = "mork-backend")]
use crate::imp_artifacts::{
    imp_artifact_dir, load_imp_lookup_artifact, load_imp_rewrite_ir_artifact,
    load_imp_transition_artifact,
};
#[cfg(feature = "mork-backend")]
use crate::native_transition_contract::{
    build_native_transition_contract, cached_contract_result, dispatch_active_source_step,
    NativeTransitionContract,
};
#[cfg(feature = "mork-backend")]
use crate::rewrite_template::{
    bind_var, execute_rule_to_runtime_strings, resolve_query_arg, CPrefixConstructorCodec,
    ResolvedQueryArg, RewritePremiseEvaluator, TemplateBindings,
};
#[cfg(feature = "mork-backend")]
use mettail_runtime::{run_native_term_graph_with_timing, AscentResults, MorkExecutionLimits};
#[cfg(feature = "mork-backend")]
use std::collections::HashMap;
#[cfg(feature = "mork-backend")]
use std::sync::OnceLock;

impl IMPLanguage {
    pub fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> {
        parse_imp_term(input)
    }

    pub fn parse_term_for_env(&self, input: &str) -> Result<Box<dyn Term>, String> {
        parse_imp_term_for_env(input)
    }
}

#[cfg(feature = "mork-backend")]
#[derive(Debug)]
struct ImpRewriteContract {
    transition: NativeTransitionContract,
    rules_by_id: HashMap<String, RewriteIRRule>,
}

#[cfg(feature = "mork-backend")]
fn imp_rewrite_contract() -> Result<&'static ImpRewriteContract, String> {
    static CONTRACT: OnceLock<Result<ImpRewriteContract, String>> = OnceLock::new();
    cached_contract_result(&CONTRACT, || {
        let dir = imp_artifact_dir();
        let transition = load_imp_transition_artifact(&dir)?;
        let lookup = load_imp_lookup_artifact(&dir)?;
        let rewrite_ir = load_imp_rewrite_ir_artifact(&dir)?;
        let transition = build_native_transition_contract(
            "IMP",
            transition,
            lookup,
            rewrite_ir.clone(),
            |lookup| {
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
                    return Err(
                        "IMP storeGet family must be exact and no-false-negatives".to_string()
                    );
                }
                Ok(())
            },
        )?;
        let mut rules_by_id = HashMap::new();
        for rule in rewrite_ir.rules {
            if rule.lhs.is_none() || rule.rhs.is_none() {
                return Err(format!(
                    "IMP rewrite_ir v2 requires structured lhs/rhs for rule '{}'",
                    rule.rule_id
                ));
            }
            if rules_by_id.insert(rule.rule_id.clone(), rule).is_some() {
                return Err("IMP rewrite_ir contains duplicate rule ids".to_string());
            }
        }
        Ok(ImpRewriteContract { transition, rules_by_id })
    })
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
        (Store::C_Store(_, y, z), ImpVar::C_VarX) => {
            Some(Box::new(Store::C_Store(Box::new(value.clone()), y.clone(), z.clone())))
        },
        (Store::C_Store(x, _, z), ImpVar::C_VarY) => {
            Some(Box::new(Store::C_Store(x.clone(), Box::new(value.clone()), z.clone())))
        },
        (Store::C_Store(x, y, _), ImpVar::C_VarZ) => {
            Some(Box::new(Store::C_Store(x.clone(), y.clone(), Box::new(value.clone()))))
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn apply_ctor(ctor: &str, args: Vec<PatternNode>) -> PatternNode {
    PatternNode::Apply { ctor: ctor.to_string(), args }
}

#[cfg(feature = "mork-backend")]
fn nat_to_node(n: &Nat) -> PatternNode {
    match n {
        Nat::C_Zero => apply_ctor("Zero", vec![]),
        Nat::C_Succ(prev) => apply_ctor("Succ", vec![nat_to_node(prev.as_ref())]),
        _ => unreachable!("generated IMP Nat only exposes Zero/Succ"),
    }
}

#[cfg(feature = "mork-backend")]
fn nat_from_node(node: &PatternNode) -> Option<Box<Nat>> {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "Zero" && args.is_empty() => {
            Some(Box::new(Nat::C_Zero))
        },
        PatternNode::Apply { ctor, args } if ctor == "Succ" && args.len() == 1 => {
            nat_from_node(&args[0]).map(|prev| Box::new(Nat::C_Succ(prev)))
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn bool_to_node(b: &Bool) -> PatternNode {
    match b {
        Bool::C_BoolTrue => apply_ctor("BoolTrue", vec![]),
        Bool::C_BoolFalse => apply_ctor("BoolFalse", vec![]),
        _ => unreachable!("generated IMP Bool only exposes BoolTrue/BoolFalse"),
    }
}

#[cfg(feature = "mork-backend")]
fn imp_var_from_node(node: &PatternNode) -> Option<Box<ImpVar>> {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "VarX" && args.is_empty() => {
            Some(Box::new(ImpVar::C_VarX))
        },
        PatternNode::Apply { ctor, args } if ctor == "VarY" && args.is_empty() => {
            Some(Box::new(ImpVar::C_VarY))
        },
        PatternNode::Apply { ctor, args } if ctor == "VarZ" && args.is_empty() => {
            Some(Box::new(ImpVar::C_VarZ))
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn store_to_node(store: &Store) -> PatternNode {
    match store {
        Store::C_Store(x, y, z) => apply_ctor(
            "Store",
            vec![nat_to_node(x.as_ref()), nat_to_node(y.as_ref()), nat_to_node(z.as_ref())],
        ),
        _ => unreachable!("generated IMP Store only exposes Store"),
    }
}

#[cfg(feature = "mork-backend")]
fn store_from_node(node: &PatternNode) -> Option<Box<Store>> {
    match node {
        PatternNode::Apply { ctor, args } if ctor == "Store" && args.len() == 3 => {
            Some(Box::new(Store::C_Store(
                nat_from_node(&args[0])?,
                nat_from_node(&args[1])?,
                nat_from_node(&args[2])?,
            )))
        },
        _ => None,
    }
}

#[cfg(feature = "mork-backend")]
fn bind_relation_result(
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
fn expect_ground_arg(
    relation: &str,
    idx: usize,
    arg: &PatternNode,
    env: &TemplateBindings,
) -> Result<PatternNode, String> {
    match resolve_query_arg(arg, env)? {
        ResolvedQueryArg::Ground(value) => Ok(value),
        ResolvedQueryArg::UnboundVar(name) => Err(format!(
            "IMP relation '{}' requires argument {} to be ground, got unbound variable '{}'",
            relation, idx, name
        )),
    }
}

#[cfg(feature = "mork-backend")]
struct ImpPremiseEvaluator;

#[cfg(feature = "mork-backend")]
impl RewritePremiseEvaluator for ImpPremiseEvaluator {
    fn eval_relation_query(
        &self,
        relation: &str,
        args: &[PatternNode],
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        match relation {
            "storeGet" => {
                if args.len() != 3 {
                    return Err(format!(
                        "IMP relation '{}' expects 3 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let store = store_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "storeGet arg 0 must be a Store term".to_string())?;
                let var = imp_var_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "storeGet arg 1 must be a Var term".to_string())?;
                let Some(value) = store_get(store.as_ref(), var.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[2], nat_to_node(value.as_ref()))
            },
            "storeSet" => {
                if args.len() != 4 {
                    return Err(format!(
                        "IMP relation '{}' expects 4 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let store = store_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "storeSet arg 0 must be a Store term".to_string())?;
                let var = imp_var_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "storeSet arg 1 must be a Var term".to_string())?;
                let value = nat_from_node(&expect_ground_arg(relation, 2, &args[2], env)?)
                    .ok_or_else(|| "storeSet arg 2 must be a Nat term".to_string())?;
                let Some(updated) = store_set(store.as_ref(), var.as_ref(), value.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[3], store_to_node(updated.as_ref()))
            },
            "natAdd" => {
                if args.len() != 3 {
                    return Err(format!(
                        "IMP relation '{}' expects 3 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let lhs = nat_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "natAdd arg 0 must be Nat".to_string())?;
                let rhs = nat_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "natAdd arg 1 must be Nat".to_string())?;
                let Some(sum) = nat_add(lhs.as_ref(), rhs.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[2], nat_to_node(sum.as_ref()))
            },
            "natMul" => {
                if args.len() != 3 {
                    return Err(format!(
                        "IMP relation '{}' expects 3 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let lhs = nat_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "natMul arg 0 must be Nat".to_string())?;
                let rhs = nat_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "natMul arg 1 must be Nat".to_string())?;
                let Some(prod) = nat_mul(lhs.as_ref(), rhs.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[2], nat_to_node(prod.as_ref()))
            },
            "natLe" => {
                if args.len() != 3 {
                    return Err(format!(
                        "IMP relation '{}' expects 3 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let lhs = nat_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "natLe arg 0 must be Nat".to_string())?;
                let rhs = nat_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "natLe arg 1 must be Nat".to_string())?;
                let Some(out) = nat_le(lhs.as_ref(), rhs.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[2], bool_to_node(out.as_ref()))
            },
            "natEq" => {
                if args.len() != 3 {
                    return Err(format!(
                        "IMP relation '{}' expects 3 args, got {}",
                        relation,
                        args.len()
                    ));
                }
                let lhs = nat_from_node(&expect_ground_arg(relation, 0, &args[0], env)?)
                    .ok_or_else(|| "natEq arg 0 must be Nat".to_string())?;
                let rhs = nat_from_node(&expect_ground_arg(relation, 1, &args[1], env)?)
                    .ok_or_else(|| "natEq arg 1 must be Nat".to_string())?;
                let Some(out) = nat_eq(lhs.as_ref(), rhs.as_ref()) else {
                    return Ok(Vec::new());
                };
                bind_relation_result(env, &args[2], bool_to_node(out.as_ref()))
            },
            _ => Err(format!(
                "IMP generic rewrite executor does not yet support relation '{}'",
                relation
            )),
        }
    }
}

#[cfg(feature = "mork-backend")]
fn parse_imp_state_from_runtime_text(text: &str) -> Result<State, String> {
    let lang = IMPLanguage;
    let term = lang.parse_term(text)?;
    let wrapped = term.as_any().downcast_ref::<IMPTerm>().ok_or_else(|| {
        format!("IMP generic rewrite executor expected IMPTerm wrapper after parsing '{}'", text)
    })?;
    match &wrapped.0 {
        IMPTermInner::State(state) => Ok(state.clone()),
        _ => Err(format!("IMP generic rewrite executor parsed non-State term from '{}'", text)),
    }
}

#[cfg(feature = "mork-backend")]
fn imp_apply_rule(
    rule_id: &str,
    state: &State,
    contract: &ImpRewriteContract,
) -> Result<Vec<State>, String> {
    let rule = contract
        .rules_by_id
        .get(rule_id)
        .ok_or_else(|| format!("IMP rewrite contract missing structured rule '{}'", rule_id))?;
    let rendered = execute_rule_to_runtime_strings(
        &CPrefixConstructorCodec,
        &format!("{}", state),
        rule,
        &ImpPremiseEvaluator,
    )?;
    rendered
        .into_iter()
        .map(|text| parse_imp_state_from_runtime_text(&text))
        .collect()
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
    let contract = imp_rewrite_contract()?;
    dispatch_active_source_step(
        "IMP",
        &contract.transition,
        Ok(imp_source_instr(state)),
        |rule, _meta| imp_apply_rule(rule, state, contract),
    )
}

#[cfg(feature = "mork-backend")]
fn run_imp_native_state_graph(
    term: &dyn Term,
    limits: MorkExecutionLimits,
) -> Result<AscentResults, String> {
    let wrapped = term.as_any().downcast_ref::<IMPTerm>().ok_or_else(|| {
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

    run_native_term_graph_with_timing(term, start_state, limits, |state| {
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
    run_imp_native_state_graph(term, limits)
}
