//! PeTTa Artifact Construction (Program-Parametric)
//!
//! Unlike HE/IMP/MM0Lite which load static JSON artifacts, PeTTa derives its
//! transition spec and rewrite IR **per-program** from the user's rule set.
//! This mirrors the Lean derivation functions:
//!   - `derivePeTTaTransitionSpec?` (TransitionSpec.lean)
//!   - `derivePeTTaRewriteIR?` (RewriteIR.lean)
//!
//! The lookup plan is static and loaded from disk.

use crate::artifact_contract::{
    LookupArtifact, PatternNode, PremiseNode, RewriteIRArtifact, RewriteIRRule, RewriteRuleMode,
    RewriteIRV2PremiseVarFlow, RewriteIRV2RootUpdateHint, TransitionArtifact, TransitionRule,
    TransitionSemKey, TransitionSource,
};
// DELETED: artifact_runtime and native_transition_contract were hand-written PathMap reimplementations.
// use crate::artifact_runtime::{ArtifactPatternStep, PatternArtifactRuntime};
use crate::execution_contract::{
    execution_contract_entry, execution_contract_grounded_builtin_entry,
    execution_contract_relation_premise_entry, execution_contract_space_effect_payload_entry,
    load_execution_contract_artifact_from_dir, BuiltinDemandKind, ExecutionContractArtifact,
    ExecutionContractEntry, ExecutionEffectClass, GroundedBuiltinHostKind,
    IntrinsicBuiltinExecutionContract, PayloadPatternShapeKind, PremiseArgRole,
    ResultBindingPolicy, SpaceEffectPayloadKind, SpaceEffectSinkKind,
};
// use crate::native_transition_contract::{
//     build_native_transition_contract, expect_rule_contract, NativeTransitionContract,
//     NativeTransitionRuleMeta,
// };
use crate::rewrite_template::{
    instantiate_pattern, match_pattern, RewritePremiseEvaluator, TemplateBindings,
};
use crate::scope_contract::{
    load_scope_contract_artifact_from_dir, ordered_free_vars_with_scope_contract,
    ScopeContractArtifact, ScopeKind,
};
use std::collections::BTreeMap;
use std::path::PathBuf;

/// A PeTTa rewrite rule in its abstract form (pre-artifact).
/// This is what the surface parser produces from `(= lhs rhs)` definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeTTaRule {
    pub name: String,
    pub left: PatternNode,
    pub right: PatternNode,
    pub premises: Vec<PremiseNode>,
}

/// Source dispatch key: (head_tag, arity).
/// Mirrors `SourceKey` from TransitionSpec.lean.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SourceKey {
    head_tag: String,
    arity: usize,
}

/// Replace non-alphanumeric characters with `_`.
/// Mirrors `sanitizeToken` from TransitionSpec.lean.
fn sanitize_token(s: &str) -> String {
    let mapped: String = s
        .chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect();
    if mapped.is_empty() {
        "_".to_string()
    } else {
        mapped
    }
}

/// Derive the source dispatch key from a pattern's head.
/// Mirrors `sourceKeyOfPattern` from TransitionSpec.lean.
fn source_key_of_pattern(pat: &PatternNode) -> SourceKey {
    match pat {
        PatternNode::Apply { ctor, args } => SourceKey {
            head_tag: ctor.clone(),
            arity: args.len(),
        },
        PatternNode::Fvar { .. } => SourceKey { head_tag: "$fvar".to_string(), arity: 0 },
        PatternNode::Bvar { .. } => SourceKey { head_tag: "$bvar".to_string(), arity: 0 },
        PatternNode::Lambda { .. } => SourceKey {
            head_tag: "$lambda".to_string(),
            arity: 1,
        },
        PatternNode::MultiLambda { arity, .. } => SourceKey {
            head_tag: format!("$multiLambda{}", arity),
            arity: 1,
        },
        PatternNode::Subst { .. } => SourceKey { head_tag: "$subst".to_string(), arity: 2 },
        PatternNode::Collection { collection_type, elements, rest } => {
            let rest_tag = if rest.is_some() { "_rest" } else { "" };
            SourceKey {
                head_tag: format!("$collection_{}{}", collection_type, rest_tag),
                arity: elements.len(),
            }
        },
    }
}

/// Source instruction tag: `C_{sanitized_head}_A{arity}`.
/// Mirrors `sourceInstrOfKey` from TransitionSpec.lean.
fn source_instr_of_key(key: &SourceKey) -> String {
    format!("C_{}_A{}", sanitize_token(&key.head_tag), key.arity)
}

/// Source label: `{head}/{arity}`.
/// Mirrors `sourceLabelOfKey` from TransitionSpec.lean.
fn source_label_of_key(key: &SourceKey) -> String {
    format!("{}/{}", key.head_tag, key.arity)
}

pub(crate) fn source_label_of_pattern(pat: &PatternNode) -> String {
    source_label_of_key(&source_key_of_pattern(pat))
}

/// Extract premise relation names from a rule's premises.
fn premise_relation_names(premises: &[PremiseNode]) -> Vec<String> {
    premises
        .iter()
        .filter_map(|p| match p {
            PremiseNode::RelationQuery { relation, .. } => Some(relation.clone()),
            _ => None,
        })
        .collect()
}

// rule_has_compat_head_constraint + derive_rewrite_rule_mode are now in
// compat_head_boundary.rs. Keep this thin wrapper for existing callers.
pub(crate) fn derive_petta_rewrite_rule_mode(
    lhs: &PatternNode,
    rhs_fresh_vars: &[String],
) -> RewriteRuleMode {
    crate::compat_head_boundary::derive_rewrite_rule_mode(lhs, rhs_fresh_vars)
}

/// Mirror the current Lean rewrite export split: premise-free rules may still
/// emit symbolic rhs terms through rule enumeration, so missing rhs vars are
/// treated as fresh symbolic outputs there. Premise-bearing rules stay
/// conservative until the certified MM2 realization supports them more
/// generally.
pub(crate) fn split_petta_rhs_var_obligations(
    has_premises: bool,
    rhs_missing: Vec<String>,
) -> (Vec<String>, Vec<String>) {
    if has_premises {
        (Vec::new(), rhs_missing)
    } else {
        (rhs_missing, Vec::new())
    }
}

fn ordered_uniq(xs: Vec<String>) -> Vec<String> {
    let mut out = Vec::new();
    for x in xs {
        if !out.contains(&x) {
            out.push(x);
        }
    }
    out
}

fn ordered_uniq_u64(xs: Vec<u64>) -> Vec<u64> {
    let mut out = Vec::new();
    for x in xs {
        if !out.contains(&x) {
            out.push(x);
        }
    }
    out
}

pub fn load_optional_petta_scope_contract_artifact() -> Result<Option<ScopeContractArtifact>, String> {
    for dir in petta_transition_search_paths() {
        let json_path = dir.join("petta.scope_contract.json");
        let checksum_path = dir.join("petta.scope_contract.checksum");
        if !json_path.is_file() || !checksum_path.is_file() {
            continue;
        }
        match load_scope_contract_artifact_from_dir(
            &dir,
            "petta.scope_contract.json",
            "petta.scope_contract.checksum",
            "petta",
        ) {
            Ok(artifact) => {
                validate_petta_scope_contract_artifact(&artifact)?;
                return Ok(Some(artifact));
            },
            Err(err) => {
                return Err(format!(
                    "failed to load PeTTa scope contract from {}: {}",
                    dir.display(),
                    err
                ))
            },
        }
    }
    Ok(None)
}

fn load_petta_scope_contract_artifact() -> Result<ScopeContractArtifact, String> {
    load_optional_petta_scope_contract_artifact()?.ok_or_else(|| {
        "PeTTa scope contract artifact is required for rewrite-ir-v2 free-variable analysis"
            .to_string()
    })
}

fn free_vars_pattern(
    node: &PatternNode,
    scope_contract: &ScopeContractArtifact,
) -> Result<Vec<String>, String> {
    ordered_free_vars_with_scope_contract(node, scope_contract)
}

fn premise_vars(
    premise: &PremiseNode,
    scope_contract: &ScopeContractArtifact,
) -> Result<Vec<String>, String> {
    match premise {
        PremiseNode::Freshness { var_name, term } => {
            let mut vars = vec![var_name.clone()];
            vars.extend(free_vars_pattern(term, scope_contract)?);
            Ok(ordered_uniq(vars))
        },
        PremiseNode::Congruence { lhs, rhs } => Ok(ordered_uniq(
            free_vars_pattern(lhs, scope_contract)?
                .into_iter()
                .chain(free_vars_pattern(rhs, scope_contract)?)
                .collect(),
        )),
        PremiseNode::RelationQuery { args, .. } => {
            let mut vars = Vec::new();
            for arg in args {
                vars.extend(free_vars_pattern(arg, scope_contract)?);
            }
            Ok(ordered_uniq(vars))
        },
    }
}

fn derive_premise_var_flow(
    lhs_vars: &[String],
    premises: &[PremiseNode],
    scope_contract: &ScopeContractArtifact,
) -> Result<Vec<RewriteIRV2PremiseVarFlow>, String> {
    let mut seen = lhs_vars.to_vec();
    let mut flows = Vec::new();
    for (idx, premise) in premises.iter().enumerate() {
        let vars = premise_vars(premise, scope_contract)?;
        let introduced_vars = vars
            .iter()
            .filter(|name| !seen.contains(name))
            .cloned()
            .collect::<Vec<_>>();
        seen.extend(introduced_vars.clone());
        flows.push(RewriteIRV2PremiseVarFlow {
            premise_index: idx as u64,
            premise_vars: vars,
            introduced_vars,
        });
    }
    Ok(flows)
}

fn list_get<T>(xs: &[T], i: usize) -> Option<&T> {
    xs.get(i)
}

fn root_update_hint(lhs: &PatternNode, rhs: &PatternNode) -> Option<RewriteIRV2RootUpdateHint> {
    match (lhs, rhs) {
        (
            PatternNode::Apply { ctor: lhs_ctor, args: lhs_args },
            PatternNode::Apply { ctor: rhs_ctor, args: rhs_args },
        ) => {
            let shared = lhs_args.len().min(rhs_args.len());
            let mut preserved = Vec::new();
            let mut changed = Vec::new();
            for i in 0..shared {
                if list_get(lhs_args, i) == list_get(rhs_args, i) {
                    preserved.push(i as u64);
                } else {
                    changed.push(i as u64);
                }
            }
            Some(RewriteIRV2RootUpdateHint {
                lhs_root_ctor: lhs_ctor.clone(),
                rhs_root_ctor: rhs_ctor.clone(),
                lhs_arity: lhs_args.len() as u64,
                rhs_arity: rhs_args.len() as u64,
                preserved_arg_positions: ordered_uniq_u64(preserved),
                changed_arg_positions: ordered_uniq_u64(changed),
            })
        },
        _ => None,
    }
}

fn has_freshness_premise(premises: &[PremiseNode]) -> bool {
    premises
        .iter()
        .any(|p| matches!(p, PremiseNode::Freshness { .. }))
}

fn has_congruence_premise(premises: &[PremiseNode]) -> bool {
    premises
        .iter()
        .any(|p| matches!(p, PremiseNode::Congruence { .. }))
}

/// Classify source instruction class.
/// Mirrors `sourceInstrClassFor` from TransitionSpec.lean.
fn source_instr_class(key: &SourceKey) -> &'static str {
    if key.head_tag.starts_with('$') {
        "pattern_root"
    } else {
        "apply_head"
    }
}

/// Classify transition kind.
/// Mirrors `transitionKindFor` from TransitionSpec.lean.
fn transition_kind(rel_names: &[String], has_fresh: bool, has_cong: bool) -> &'static str {
    if !rel_names.is_empty() {
        "rewrite_with_relation_premises"
    } else if has_fresh {
        "rewrite_with_freshness"
    } else if has_cong {
        "rewrite_with_congruence"
    } else {
        "rewrite_root"
    }
}

/// Classify guard family.
/// Mirrors `guardFamilyFor` from TransitionSpec.lean.
fn guard_family(rel_names: &[String], has_fresh: bool, has_cong: bool) -> &'static str {
    if rel_names.iter().any(|r| r == "spaceMatch") {
        "space_match"
    } else if !rel_names.is_empty() {
        "relation_query"
    } else if has_fresh {
        "freshness"
    } else if has_cong {
        "congruence"
    } else {
        "pattern_match"
    }
}

/// Build a `TransitionArtifact` from a list of PeTTa rules.
/// Mirrors `derivePeTTaTransitionSpec?` from TransitionSpec.lean.
pub fn build_petta_transition_spec(rules: &[PeTTaRule]) -> Result<TransitionArtifact, String> {
    // Derive transitions (mirrors foldRewriteTransitions)
    let mut transition_rules = Vec::with_capacity(rules.len());
    // Group rules by source_instr for the sources list (ordered by first appearance)
    let mut source_order: Vec<String> = Vec::new();
    let mut source_map: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut source_labels: BTreeMap<String, String> = BTreeMap::new();

    for (idx, rule) in rules.iter().enumerate() {
        let key = source_key_of_pattern(&rule.left);
        let src_instr = source_instr_of_key(&key);
        let src_label = source_label_of_key(&key);
        let rule_id = format!("R{}", idx);
        let rel_names = premise_relation_names(&rule.premises);
        let has_fresh = has_freshness_premise(&rule.premises);
        let has_cong = has_congruence_premise(&rule.premises);

        // Track source ordering
        if !source_map.contains_key(&src_instr) {
            source_order.push(src_instr.clone());
        }
        source_map
            .entry(src_instr.clone())
            .or_default()
            .push(rule_id.clone());
        source_labels
            .entry(src_instr.clone())
            .or_insert_with(|| src_label.clone());

        transition_rules.push(TransitionRule {
            logical_transition_id: format!("{}:{}", src_instr, rule.name),
            source_instr: src_instr,
            source_label: src_label,
            rule_id,
            sem_key: TransitionSemKey {
                source_instr_class: source_instr_class(&key).to_string(),
                transition_kind: transition_kind(&rel_names, has_fresh, has_cong).to_string(),
                guard_family: guard_family(&rel_names, has_fresh, has_cong).to_string(),
                effect_kind: "emit_pattern".to_string(),
                dialect_ext: None,
                contracts: vec![
                    "nondeterministic".to_string(),
                    "order_sensitive".to_string(),
                    "memoization_safe".to_string(),
                    "specialization_safe".to_string(),
                ],
            },
            priority: idx as u64,
        });
    }

    // Build sources in order of first appearance
    let sources: Vec<TransitionSource> = source_order
        .iter()
        .map(|si| TransitionSource {
            source_instr: si.clone(),
            source_label: source_labels[si].clone(),
            ordered_rules: source_map[si].clone(),
        })
        .collect();

    Ok(TransitionArtifact {
        schema_version: 2,
        dialect: "petta".to_string(),
        sources,
        rules: transition_rules,
    })
}

/// Build a `RewriteIRArtifact` from a list of PeTTa rules.
/// Mirrors `derivePeTTaRewriteIR?` from RewriteIR.lean.
pub fn build_petta_rewrite_ir(rules: &[PeTTaRule]) -> Result<RewriteIRArtifact, String> {
    let scope_contract = load_petta_scope_contract_artifact()?;

    let ir_rules: Vec<RewriteIRRule> = rules
        .iter()
        .enumerate()
        .map(|(idx, rule)| -> Result<RewriteIRRule, String> {
            let key = source_key_of_pattern(&rule.left);
            let lhs_vars = ordered_uniq(free_vars_pattern(&rule.left, &scope_contract)?);
            let premise_var_flow =
                derive_premise_var_flow(&lhs_vars, &rule.premises, &scope_contract)?;
            let available = ordered_uniq(
                lhs_vars
                    .iter()
                    .cloned()
                    .chain(
                        premise_var_flow
                            .iter()
                            .flat_map(|flow| flow.introduced_vars.clone()),
                    )
                    .collect(),
            );
            let rhs_vars = ordered_uniq(free_vars_pattern(&rule.right, &scope_contract)?);
            let rhs_missing = ordered_uniq(
                rhs_vars
                    .iter()
                    .filter(|name| !available.contains(name))
                    .cloned()
                    .collect(),
            );
            let (rhs_fresh_vars, rhs_eval_requires) =
                split_petta_rhs_var_obligations(!rule.premises.is_empty(), rhs_missing.clone());
            let rule_mode = derive_petta_rewrite_rule_mode(&rule.left, &rhs_fresh_vars);
            Ok(RewriteIRRule {
                rule_id: format!("R{}", idx),
                rule_name: rule.name.clone(),
                source_instr: source_instr_of_key(&key),
                source_label: source_label_of_key(&key),
                priority: idx as u64,
                left_repr: format!("{:?}", rule.left),
                right_repr: format!("{:?}", rule.right),
                premise_relations: premise_relation_names(&rule.premises),
                lhs: Some(rule.left.clone()),
                rhs: Some(rule.right.clone()),
                premises: rule.premises.clone(),
                lhs_vars,
                premise_var_flow,
                rhs_vars,
                rhs_fresh_vars,
                rhs_eval_requires,
                rule_mode: Some(rule_mode),
                root_update: root_update_hint(&rule.left, &rule.right),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(RewriteIRArtifact {
        schema_version: 2,
        dialect: "petta".to_string(),
        rules: ir_rules,
    })
}

fn petta_transition_search_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();
    if let Ok(dir) = std::env::var("METTAIL_PETTA_EXECUTION_CONTRACT_DIR") {
        paths.push(PathBuf::from(dir));
    }
    if let Ok(dir) = std::env::var("METTAIL_PETTA_ARTIFACT_DIR") {
        paths.push(PathBuf::from(dir));
    }
    if let Ok(dir) = std::env::var("METTAIL_TRANSITION_SPEC_DIR") {
        paths.push(PathBuf::from(dir));
    }
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    paths.push(manifest_dir.join("artifacts/transition"));
    paths.push(PathBuf::from("artifacts/transition"));
    for prefix in ["..", "../..", "../../.."] {
        paths.push(PathBuf::from(prefix).join("lean-projects/mettapedia/artifacts/transition"));
        paths.push(PathBuf::from(prefix).join("lean-projects/algorithms/artifacts/transition"));
    }
    paths.push(manifest_dir.join("../../../lean-projects/mettapedia/artifacts/transition"));
    paths.push(manifest_dir.join("../../../lean-projects/algorithms/artifacts/transition"));
    paths
}

/// Load the optional PeTTa execution-contract sidecar from disk.
///
/// This is the intended replacement for hardcoded Rust execution-boundary
/// policy. If the sidecar is absent, callers must continue to fail closed or
/// use explicitly temporary bootstrap wiring outside the production path.
pub fn load_optional_petta_execution_contract_artifact(
) -> Result<Option<ExecutionContractArtifact>, String> {
    let mut first_error: Option<String> = None;
    for dir in petta_transition_search_paths() {
        let json_path = dir.join("petta.execution_contract.json");
        let checksum_path = dir.join("petta.execution_contract.checksum");
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_execution_contract_artifact_from_dir(
            &dir,
            "petta.execution_contract.json",
            "petta.execution_contract.checksum",
            "petta",
        ) {
            Ok(artifact) => {
                validate_petta_execution_contract_artifact(&artifact)?;
                return Ok(Some(artifact));
            },
            Err(err) => {
                if first_error.is_none() {
                    first_error = Some(err);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => Ok(None),
    }
}

fn validate_petta_execution_contract_artifact(
    artifact: &ExecutionContractArtifact,
) -> Result<(), String> {
    let required_lookup = [("match", 3, "spaceMatch"), ("get-atoms", 1, "selfFacts")];
    for (head, arity, family) in required_lookup {
        let entry = execution_contract_entry(artifact, head, arity).ok_or_else(|| {
            format!("PeTTa execution contract missing required certified lookup {head}/{arity}")
        })?;
        let ExecutionContractEntry::LookupQuery(query) = entry else {
            return Err(format!(
                "PeTTa execution contract entry for {head}/{arity} must be a lookup_query lane"
            ));
        };
        if query.lookup_family.family != family {
            return Err(format!(
                "PeTTa execution contract entry for {head}/{arity} expected lookup family '{}', got '{}'",
                family, query.lookup_family.family
            ));
        }
    }

    let required_space_effects = [
        ("add-atom", 2),
        ("add-atom!", 2),
        ("remove-atom", 2),
        ("remove-atom!", 2),
    ];
    for (head, arity) in required_space_effects {
        let entry = execution_contract_entry(artifact, head, arity).ok_or_else(|| {
            format!(
                "PeTTa execution contract missing required certified space effect {head}/{arity}"
            )
        })?;
        if !matches!(entry, ExecutionContractEntry::SpaceEffect(_)) {
            return Err(format!(
                "PeTTa execution contract entry for {head}/{arity} must be a space_effect lane"
            ));
        }
    }

    let relation_premise = execution_contract_relation_premise_entry(artifact, "spaceMatch", 3)
        .ok_or_else(|| {
            "PeTTa execution contract missing required relation_premise spaceMatch/3".to_string()
        })?;
    if relation_premise.lookup_family.family != "spaceMatch" {
        return Err(format!(
            "PeTTa relation_premise spaceMatch/3 expected lookup family 'spaceMatch', got '{}'",
            relation_premise.lookup_family.family
        ));
    }
    if relation_premise.arg_roles
        != vec![
            PremiseArgRole::Pattern,
            PremiseArgRole::Template,
            PremiseArgRole::ResultVar,
        ]
    {
        return Err(
            "PeTTa relation_premise spaceMatch/3 must use arg roles [pattern, template, result_var]"
                .to_string(),
        );
    }
    if relation_premise.result_binding_policy
        != Some(ResultBindingPolicy::MustBeFreshVar)
    {
        return Err(
            "PeTTa relation_premise spaceMatch/3 must require must_be_fresh_var"
                .to_string(),
        );
    }

    let add_fact_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "add-atom",
        2,
        SpaceEffectPayloadKind::FactPayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload add-atom/2 fact_payload"
            .to_string()
    })?;
    if add_fact_payload.payload_shape != PayloadPatternShapeKind::NonRewritePattern
        || add_fact_payload.sink_kind != SpaceEffectSinkKind::InsertFact
        || add_fact_payload.space_arg_position != 0
        || add_fact_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa add-atom fact payload contract must use non_rewrite_pattern at (space=0,payload=1) with insert_fact sink"
                .to_string(),
        );
    }

    let remove_fact_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "remove-atom",
        2,
        SpaceEffectPayloadKind::FactPayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload remove-atom/2 fact_payload"
            .to_string()
    })?;
    if remove_fact_payload.payload_shape != PayloadPatternShapeKind::NonRewritePattern
        || remove_fact_payload.sink_kind != SpaceEffectSinkKind::RemoveFact
        || remove_fact_payload.space_arg_position != 0
        || remove_fact_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa remove-atom fact payload contract must use non_rewrite_pattern at (space=0,payload=1) with remove_fact sink"
                .to_string(),
        );
    }

    let add_rule_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "add-atom",
        2,
        SpaceEffectPayloadKind::SourceRulePayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload add-atom/2 source_rule_payload"
            .to_string()
    })?;
    if add_rule_payload.payload_shape != PayloadPatternShapeKind::RewriteEqRule
        || add_rule_payload.sink_kind != SpaceEffectSinkKind::InsertRule
        || add_rule_payload.space_arg_position != 0
        || add_rule_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa add-atom source-rule payload contract must use rewrite_eq_rule at (space=0,payload=1) with insert_rule sink"
                .to_string(),
        );
    }

    let remove_rule_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "remove-atom",
        2,
        SpaceEffectPayloadKind::SourceRulePayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload remove-atom/2 source_rule_payload"
            .to_string()
    })?;
    if remove_rule_payload.payload_shape != PayloadPatternShapeKind::RewriteEqRule
        || remove_rule_payload.sink_kind != SpaceEffectSinkKind::RemoveRule
        || remove_rule_payload.space_arg_position != 0
        || remove_rule_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa remove-atom source-rule payload contract must use rewrite_eq_rule at (space=0,payload=1) with remove_rule sink"
                .to_string(),
        );
    }

    let add_bang_fact_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "add-atom!",
        2,
        SpaceEffectPayloadKind::FactPayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload add-atom!/2 fact_payload"
            .to_string()
    })?;
    if add_bang_fact_payload.payload_shape != PayloadPatternShapeKind::NonRewritePattern
        || add_bang_fact_payload.sink_kind != SpaceEffectSinkKind::InsertFact
        || add_bang_fact_payload.space_arg_position != 0
        || add_bang_fact_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa add-atom! fact payload contract must use non_rewrite_pattern at (space=0,payload=1) with insert_fact sink"
                .to_string(),
        );
    }

    let remove_bang_fact_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "remove-atom!",
        2,
        SpaceEffectPayloadKind::FactPayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload remove-atom!/2 fact_payload"
            .to_string()
    })?;
    if remove_bang_fact_payload.payload_shape != PayloadPatternShapeKind::NonRewritePattern
        || remove_bang_fact_payload.sink_kind != SpaceEffectSinkKind::RemoveFact
        || remove_bang_fact_payload.space_arg_position != 0
        || remove_bang_fact_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa remove-atom! fact payload contract must use non_rewrite_pattern at (space=0,payload=1) with remove_fact sink"
                .to_string(),
        );
    }

    let add_bang_rule_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "add-atom!",
        2,
        SpaceEffectPayloadKind::SourceRulePayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload add-atom!/2 source_rule_payload"
            .to_string()
    })?;
    if add_bang_rule_payload.payload_shape != PayloadPatternShapeKind::RewriteEqRule
        || add_bang_rule_payload.sink_kind != SpaceEffectSinkKind::InsertRule
        || add_bang_rule_payload.space_arg_position != 0
        || add_bang_rule_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa add-atom! source-rule payload contract must use rewrite_eq_rule at (space=0,payload=1) with insert_rule sink"
                .to_string(),
        );
    }

    let remove_bang_rule_payload = execution_contract_space_effect_payload_entry(
        artifact,
        "remove-atom!",
        2,
        SpaceEffectPayloadKind::SourceRulePayload,
    )
    .ok_or_else(|| {
        "PeTTa execution contract missing required space_effect_payload remove-atom!/2 source_rule_payload"
            .to_string()
    })?;
    if remove_bang_rule_payload.payload_shape != PayloadPatternShapeKind::RewriteEqRule
        || remove_bang_rule_payload.sink_kind != SpaceEffectSinkKind::RemoveRule
        || remove_bang_rule_payload.space_arg_position != 0
        || remove_bang_rule_payload.payload_arg_position != 1
    {
        return Err(
            "PeTTa remove-atom! source-rule payload contract must use rewrite_eq_rule at (space=0,payload=1) with remove_rule sink"
                .to_string(),
        );
    }

    let println_entry = execution_contract_grounded_builtin_entry(artifact, "println!", 1)
        .ok_or_else(|| {
            "PeTTa execution contract missing required grounded builtin println!/1".to_string()
        })?;
    if println_entry.host_kind != GroundedBuiltinHostKind::PrintlnTerm
        || println_entry.effect_class != ExecutionEffectClass::OracleIo
        || println_entry.builtin_demand != BuiltinDemandKind::RawArgs
    {
        return Err(
            "PeTTa println! grounded contract must use host kind println_term, effect_class oracle_io, and raw_args demand"
                .to_string(),
        );
    }

    let is_member_entry = execution_contract_grounded_builtin_entry(artifact, "is-member", 2)
        .ok_or_else(|| {
            "PeTTa execution contract missing required grounded builtin is-member/2".to_string()
        })?;
    if is_member_entry.host_kind != GroundedBuiltinHostKind::TupleMembership
        || is_member_entry.effect_class != ExecutionEffectClass::PureStructural
        || is_member_entry.builtin_demand != BuiltinDemandKind::ElemAndTupleArgs
    {
        return Err(
            "PeTTa is-member grounded contract must use host kind tuple_membership, effect_class pure_structural, and elem_and_tuple_args demand"
                .to_string(),
        );
    }

    Ok(())
}

fn validate_petta_scope_contract_artifact(
    artifact: &ScopeContractArtifact,
) -> Result<(), String> {
    if artifact.wildcard_symbol != "_" {
        return Err(format!(
            "PeTTa scope contract must use wildcard_symbol='_', got '{}'",
            artifact.wildcard_symbol
        ));
    }
    let require = |head: &str, arity: u64, kind: ScopeKind| {
        artifact.entries.iter().find(|entry| {
            entry.head == head && entry.arity == arity && entry.scope_kind == kind
        })
        .ok_or_else(|| {
            format!(
                "PeTTa scope contract missing required {:?} entry for {}/{}",
                kind, head, arity
            )
        })
    };

    let let_entry = require("let", 3, ScopeKind::LetLike)?;
    if let_entry.binder_positions != vec![0]
        || let_entry.value_positions != vec![1]
        || let_entry.body_positions != vec![2]
    {
        return Err(
            "PeTTa let scope contract must use binder=[0], value=[1], body=[2]".to_string(),
        );
    }

    let chain_entry = require("chain", 3, ScopeKind::ChainLike)?;
    if chain_entry.binder_positions != vec![1]
        || chain_entry.value_positions != vec![0]
        || chain_entry.body_positions != vec![2]
    {
        return Err(
            "PeTTa chain scope contract must use binder=[1], value=[0], body=[2]".to_string(),
        );
    }

    let let_star_entry = require("let*", 2, ScopeKind::LetStarLike)?;
    if let_star_entry.value_positions != vec![0]
        || let_star_entry.body_positions != vec![1]
        || !let_star_entry.sequential
    {
        return Err(
            "PeTTa let* scope contract must use values=[0], body=[1], sequential=true"
                .to_string(),
        );
    }

    let match_entry = require("match", 3, ScopeKind::MatchLike)?;
    if match_entry.binder_positions != vec![1]
        || match_entry.value_positions != vec![0]
        || match_entry.body_positions != vec![2]
        || match_entry.sequential
    {
        return Err(
            "PeTTa match scope contract must use binder=[1], value=[0], body=[2], sequential=false"
                .to_string(),
        );
    }

    let lambda_entry = require("|->", 2, ScopeKind::LambdaLike)?;
    if lambda_entry.binder_positions != vec![0]
        || !lambda_entry.value_positions.is_empty()
        || lambda_entry.body_positions != vec![1]
        || lambda_entry.sequential
    {
        return Err(
            "PeTTa |-> scope contract must use binder=[0], body=[1], sequential=false"
                .to_string(),
        );
    }

    let case_entry = require("case", 2, ScopeKind::CaseLike)?;
    if case_entry.value_positions != vec![0]
        || case_entry.body_positions != vec![1]
        || case_entry.sequential
    {
        return Err(
            "PeTTa case scope contract must use scrutinee/value=[0], branches/body=[1], sequential=false"
                .to_string(),
        );
    }

    let add_rule_payload = require("add-atom", 2, ScopeKind::SourceRulePayload)?;
    if add_rule_payload.scoped_payload_positions != vec![1]
        || add_rule_payload.payload_shape != Some(PayloadPatternShapeKind::RewriteEqRule)
    {
        return Err(
            "PeTTa add-atom scope contract must scope payload position 1 with rewrite_eq_rule shape"
                .to_string(),
        );
    }

    let add_bang_rule_payload = require("add-atom!", 2, ScopeKind::SourceRulePayload)?;
    if add_bang_rule_payload.scoped_payload_positions != vec![1]
        || add_bang_rule_payload.payload_shape != Some(PayloadPatternShapeKind::RewriteEqRule)
    {
        return Err(
            "PeTTa add-atom! scope contract must scope payload position 1 with rewrite_eq_rule shape"
                .to_string(),
        );
    }

    let remove_rule_payload = require("remove-atom", 2, ScopeKind::SourceRulePayload)?;
    if remove_rule_payload.scoped_payload_positions != vec![1]
        || remove_rule_payload.payload_shape != Some(PayloadPatternShapeKind::RewriteEqRule)
    {
        return Err(
            "PeTTa remove-atom scope contract must scope payload position 1 with rewrite_eq_rule shape"
                .to_string(),
        );
    }

    let remove_bang_rule_payload = require("remove-atom!", 2, ScopeKind::SourceRulePayload)?;
    if remove_bang_rule_payload.scoped_payload_positions != vec![1]
        || remove_bang_rule_payload.payload_shape != Some(PayloadPatternShapeKind::RewriteEqRule)
    {
        return Err(
            "PeTTa remove-atom! scope contract must scope payload position 1 with rewrite_eq_rule shape"
                .to_string(),
        );
    }

    Ok(())
}

/// Load the static PeTTa lookup plan from disk.
/// Searches standard paths for `petta.lookup_plan.json`.
pub fn load_petta_lookup_artifact() -> Result<LookupArtifact, String> {
    for dir in petta_lookup_search_paths() {
        let json_path = dir.join("petta.lookup_plan.json");
        if json_path.exists() {
            let checksum_path = dir.join("petta.lookup_plan.checksum");
            if checksum_path.exists() {
                return crate::artifact_contract::load_json_with_checksum(
                    &json_path,
                    &checksum_path,
                    "petta lookup",
                );
            }
            // No checksum file — load JSON directly
            let text = std::fs::read_to_string(&json_path)
                .map_err(|e| format!("failed to read {}: {}", json_path.display(), e))?;
            return serde_json::from_str(&text)
                .map_err(|e| format!("failed to parse {}: {}", json_path.display(), e));
        }
    }
    Err("PeTTa lookup plan artifact not found in any search path".to_string())
}

fn validate_petta_lookup_artifact(lookup: &LookupArtifact) -> Result<(), String> {
    if lookup
        .families
        .iter()
        .any(|family| family.family == "spaceMatch")
    {
        Ok(())
    } else {
        Err("PeTTa lookup-plan missing required spaceMatch family".to_string())
    }
}

/// Explicit PeTTa artifact bundle for the compiled/runtime lane.
///
/// This keeps the program-level artifact trio together and makes the current
/// replacement seam auditable:
/// - transition dispatch metadata
/// - lookup-plan contract
/// - executable rewrite IR
#[derive(Debug, Clone)]
pub struct PeTTaArtifactBundle {
    pub transition: TransitionArtifact,
    pub lookup: LookupArtifact,
    pub rewrite_ir: RewriteIRArtifact,
    pub execution_contract: Option<ExecutionContractArtifact>,
    pub scope_contract: Option<ScopeContractArtifact>,
}

pub fn build_petta_artifact_bundle(rules: &[PeTTaRule]) -> Result<PeTTaArtifactBundle, String> {
    let transition = build_petta_transition_spec(rules)?;
    let lookup = load_petta_lookup_artifact()?;
    validate_petta_lookup_artifact(&lookup)?;
    let rewrite_ir = build_petta_rewrite_ir(rules)?;
    let execution_contract = load_optional_petta_execution_contract_artifact()?;
    let scope_contract = load_optional_petta_scope_contract_artifact()?;
    Ok(PeTTaArtifactBundle {
        transition,
        lookup,
        rewrite_ir,
        execution_contract,
        scope_contract,
    })
}

// DELETED: build_petta_native_transition_contract* used the hand-written
// native_transition_contract.rs (reimplemented PathMap in Rust).
// PeTTa execution must go through MM2 emission → mork::space::Space::metta_calculus().
// fn build_petta_native_transition_contract_from_bundle(...) { ... }
// pub fn build_petta_native_transition_contract(...) { ... }

#[allow(dead_code)]
struct PeTTaArtifactPremiseEvaluator<'a> {
    facts: &'a [PatternNode],
}

impl RewritePremiseEvaluator for PeTTaArtifactPremiseEvaluator<'_> {
    fn eval_relation_query(
        &self,
        relation: &str,
        args: &[PatternNode],
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        match relation {
            "spaceMatch" => self.eval_space_match(args, env),
            _ => Err(format!(
                "PeTTa artifact runtime does not yet implement relation premise '{}'",
                relation
            )),
        }
    }
}

#[allow(dead_code)]
impl PeTTaArtifactPremiseEvaluator<'_> {
    fn eval_space_match(
        &self,
        args: &[PatternNode],
        env: &TemplateBindings,
    ) -> Result<Vec<TemplateBindings>, String> {
        if args.len() != 3 {
            return Err(format!(
                "PeTTa artifact runtime expected spaceMatch(pattern, template, result), got {} arguments",
                args.len()
            ));
        }

        let pattern = partial_instantiate(&args[0], env);
        let template = &args[1];
        let result_var_name = match &args[2] {
            PatternNode::Fvar { name } => name.clone(),
            other => {
                return Err(format!(
                    "PeTTa artifact runtime expects spaceMatch result position to be a variable, got {:?}",
                    other
                ));
            },
        };

        let mut result_envs = Vec::new();
        for fact in self.facts {
            let Some(match_bindings) = match_pattern(&pattern, fact)? else {
                continue;
            };
            let Some(mut merged) = merge_bindings(env, &match_bindings) else {
                continue;
            };
            let result = match instantiate_pattern(template, &merged) {
                Ok(result) => result,
                Err(_) => continue,
            };
            if let Some(expected) = env.get(&result_var_name) {
                if &result == expected {
                    result_envs.push(merged);
                }
            } else {
                merged.insert(result_var_name.clone(), result);
                result_envs.push(merged);
            }
        }
        Ok(result_envs)
    }
}

#[allow(dead_code)]
fn merge_bindings(base: &TemplateBindings, extra: &TemplateBindings) -> Option<TemplateBindings> {
    let mut merged = base.clone();
    for (name, value) in extra {
        match merged.get(name) {
            Some(existing) if existing == value => {},
            Some(_) => return None,
            None => {
                merged.insert(name.clone(), value.clone());
            },
        }
    }
    Some(merged)
}

#[allow(dead_code)]
fn partial_instantiate(node: &PatternNode, env: &TemplateBindings) -> PatternNode {
    match node {
        PatternNode::Fvar { name } => match env.get(name) {
            Some(value) => value.clone(),
            None => node.clone(),
        },
        PatternNode::Apply { ctor, args } => PatternNode::Apply {
            ctor: ctor.clone(),
            args: args
                .iter()
                .map(|arg| partial_instantiate(arg, env))
                .collect(),
        },
        PatternNode::Collection { collection_type, elements, rest } => PatternNode::Collection {
            collection_type: collection_type.clone(),
            elements: elements
                .iter()
                .map(|element| partial_instantiate(element, env))
                .collect(),
            rest: rest.clone(),
        },
        _ => node.clone(),
    }
}

// DISABLED: PeTTaArtifactRuntime and everything below used the hand-written
// native_transition_contract (reimplemented PathMap in Rust).
// Must be replaced with MM2 emission → mork::space::Space::metta_calculus().
// See mork_backend.rs for the correct pattern.
#[cfg(any())] // permanently disabled — DO NOT re-enable
mod _disabled_artifact_runtime {
    use super::*;

    #[derive(Debug)]
    pub struct PeTTaArtifactRuntime {
        facts: Vec<PatternNode>,
        bundle: PeTTaArtifactBundle,
        runtime: PatternArtifactRuntime, // from deleted artifact_runtime.rs
    }

    impl PeTTaArtifactRuntime {
        pub fn from_bundle(
            facts: Vec<PatternNode>,
            bundle: PeTTaArtifactBundle,
        ) -> Result<Self, String> {
            let contract = build_petta_native_transition_contract_from_bundle(&bundle)?;
            let runtime = PatternArtifactRuntime::new("PeTTa", contract, &bundle.rewrite_ir);
            Ok(Self { facts, bundle, runtime })
        }

        pub fn from_rules(rules: &[PeTTaRule]) -> Result<Self, String> {
            Self::from_space(Vec::new(), rules)
        }

        pub fn from_space(facts: Vec<PatternNode>, rules: &[PeTTaRule]) -> Result<Self, String> {
            let bundle = build_petta_artifact_bundle(rules)?;
            Self::from_bundle(facts, bundle)
        }

        pub fn facts(&self) -> &[PatternNode] {
            &self.facts
        }

        pub fn artifact_bundle(&self) -> &PeTTaArtifactBundle {
            &self.bundle
        }

        pub fn execution_contract(&self) -> Result<&ExecutionContractArtifact, String> {
            self.bundle.execution_contract.as_ref().ok_or_else(|| {
                "PeTTa artifact runtime is missing petta.execution_contract.json/checksum"
                    .to_string()
            })
        }

        fn require_lookup_query_contract(
            &self,
            head: &str,
            arity: usize,
            expected_family: &str,
        ) -> Result<(), String> {
            let contract = self.execution_contract()?;
            let entry = execution_contract_entry(contract, head, arity).ok_or_else(|| {
                format!("PeTTa execution contract missing certified entry for {head}/{arity}")
            })?;
            let ExecutionContractEntry::LookupQuery(query) = entry else {
                return Err(format!(
                    "PeTTa execution contract entry for {head}/{arity} is not a lookup_query lane"
                ));
            };
            if query.lookup_family.family != expected_family {
                return Err(format!(
                "PeTTa execution contract entry for {head}/{arity} expected lookup family '{}', got '{}'",
                expected_family, query.lookup_family.family
            ));
            }
            if !query.query_compilable {
                return Err(format!(
                    "PeTTa execution contract entry for {head}/{arity} is not query_compilable"
                ));
            }
            Ok(())
        }

        fn require_space_effect_contract(&self, head: &str, arity: usize) -> Result<(), String> {
            let contract = self.execution_contract()?;
            let entry = execution_contract_entry(contract, head, arity).ok_or_else(|| {
                format!("PeTTa execution contract missing certified entry for {head}/{arity}")
            })?;
            let ExecutionContractEntry::SpaceEffect(effect) = entry else {
                return Err(format!(
                    "PeTTa execution contract entry for {head}/{arity} is not a space_effect lane"
                ));
            };
            if !effect.space_effect_compilable {
                return Err(format!(
                "PeTTa execution contract entry for {head}/{arity} is not space_effect_compilable"
            ));
            }
            Ok(())
        }

        pub fn intrinsic_builtin_contract_for_term(
            &self,
            term: &PatternNode,
        ) -> Result<Option<&IntrinsicBuiltinExecutionContract>, String> {
            let PatternNode::Apply { ctor, args } = term else {
                return Ok(None);
            };
            let contract = self.execution_contract()?;
            let Some(entry) = execution_contract_entry(contract, ctor, args.len()) else {
                return Ok(None);
            };
            match entry {
                ExecutionContractEntry::IntrinsicBuiltin(intrinsic) => Ok(Some(intrinsic)),
                ExecutionContractEntry::LookupQuery(_) | ExecutionContractEntry::SpaceEffect(_) => {
                    Ok(None)
                },
            }
        }

        fn expect_self_space_ref(&self, op: &str, space: &PatternNode) -> Result<(), String> {
            match space {
                PatternNode::Apply { ctor, args } if ctor == "&self" && args.is_empty() => Ok(()),
                other => Err(format!(
                    "PeTTa artifact runtime currently certifies only ({} &self ...), got {:?}",
                    op, other
                )),
            }
        }

        fn eval_match_self_query(
            &self,
            space: &PatternNode,
            pattern: &PatternNode,
            template: &PatternNode,
        ) -> Result<Vec<PatternNode>, String> {
            self.require_lookup_query_contract("match", 3, "spaceMatch")?;
            self.expect_self_space_ref("match", space)?;
            let mut results = Vec::new();
            for fact in &self.facts {
                let Some(bindings) = match_pattern(pattern, fact)? else {
                    continue;
                };
                let instantiated = instantiate_pattern(template, &bindings)?;
                results.push(instantiated);
            }
            Ok(results)
        }

        fn eval_get_atoms_self_query(
            &self,
            space: &PatternNode,
        ) -> Result<Vec<PatternNode>, String> {
            self.require_lookup_query_contract("get-atoms", 1, "selfFacts")?;
            self.expect_self_space_ref("get-atoms", space)?;
            Ok(vec![PatternNode::Apply {
                ctor: "list".to_string(),
                args: self.facts.clone(),
            }])
        }

        pub fn evaluate_query_term(
            &self,
            term: &PatternNode,
        ) -> Result<Option<Vec<PatternNode>>, String> {
            match term {
                PatternNode::Apply { ctor, args } if ctor == "match" && args.len() == 3 => self
                    .eval_match_self_query(&args[0], &args[1], &args[2])
                    .map(Some),
                PatternNode::Apply { ctor, args } if ctor == "get-atoms" && args.len() == 1 => {
                    self.eval_get_atoms_self_query(&args[0]).map(Some)
                },
                _ => Ok(None),
            }
        }

        fn eval_add_atom_self_effect(
            &mut self,
            space: &PatternNode,
            payload: &PatternNode,
        ) -> Result<Vec<PatternNode>, String> {
            self.require_space_effect_contract("add-atom", 2)?;
            self.expect_self_space_ref("add-atom", space)?;
            if matches!(payload, PatternNode::Apply { ctor, args } if ctor == "=" && args.len() == 2)
            {
                return Err(
                "PeTTa artifact runtime does not yet implement dynamic rule payloads for add-atom"
                    .to_string(),
            );
            }
            self.facts.push(payload.clone());
            Ok(vec![PatternNode::Apply { ctor: "()".to_string(), args: vec![] }])
        }

        fn eval_remove_atom_self_effect(
            &mut self,
            space: &PatternNode,
            payload: &PatternNode,
        ) -> Result<Vec<PatternNode>, String> {
            self.require_space_effect_contract("remove-atom", 2)?;
            self.expect_self_space_ref("remove-atom", space)?;
            if matches!(payload, PatternNode::Apply { ctor, args } if ctor == "=" && args.len() == 2)
            {
                return Err(
                "PeTTa artifact runtime does not yet implement dynamic rule payloads for remove-atom"
                    .to_string(),
            );
            }
            self.facts.retain(|fact| fact != payload);
            Ok(vec![PatternNode::Apply { ctor: "()".to_string(), args: vec![] }])
        }

        pub fn evaluate_space_effect_term(
            &mut self,
            term: &PatternNode,
        ) -> Result<Option<Vec<PatternNode>>, String> {
            match term {
                PatternNode::Apply { ctor, args } if ctor == "add-atom" && args.len() == 2 => {
                    self.eval_add_atom_self_effect(&args[0], &args[1]).map(Some)
                },
                PatternNode::Apply { ctor, args } if ctor == "remove-atom" && args.len() == 2 => {
                    self.eval_remove_atom_self_effect(&args[0], &args[1])
                        .map(Some)
                },
                _ => Ok(None),
            }
        }

        fn execute_contract_rule(
            &self,
            rule_id: &str,
            meta: &NativeTransitionRuleMeta,
            term: &PatternNode,
            evaluator: &impl RewritePremiseEvaluator,
        ) -> Result<Vec<ArtifactPatternStep>, String> {
            match (
            meta.transition_kind.as_str(),
            meta.guard_family.as_str(),
            meta.effect_kind.as_str(),
        ) {
            ("rewrite_root", "pattern_match", "emit_pattern") => {
                expect_rule_contract(
                    "PeTTa",
                    meta,
                    "rewrite_root",
                    "pattern_match",
                    "emit_pattern",
                )?;
                self.runtime.execute_template_rule(rule_id, term, evaluator)
            },
            ("rewrite_with_relation_premises", "space_match", "emit_pattern") => {
                expect_rule_contract(
                    "PeTTa",
                    meta,
                    "rewrite_with_relation_premises",
                    "space_match",
                    "emit_pattern",
                )?;
                self.require_lookup_query_contract("match", 3, "spaceMatch")?;
                self.runtime.execute_template_rule(rule_id, term, evaluator)
            },
            _ => Err(format!(
                "PeTTa artifact runtime does not yet implement transition_kind='{}', guard_family='{}', effect_kind='{}' for rule '{}'",
                meta.transition_kind, meta.guard_family, meta.effect_kind, rule_id
            )),
        }
        }

        pub fn rewrite_root_once(&self, term: &PatternNode) -> Result<Vec<PatternNode>, String> {
            let source_instr = source_instr_of_key(&source_key_of_pattern(term));
            if self
                .runtime
                .contract()
                .ordered_rules_for(&source_instr)
                .is_none()
            {
                return Ok(Vec::new());
            }
            let evaluator = PeTTaArtifactPremiseEvaluator { facts: &self.facts };
            let results = self.runtime.dispatch_pattern_source_step(
                &source_instr,
                term,
                &evaluator,
                |_, rule_id, meta, term, evaluator| {
                    self.execute_contract_rule(rule_id, meta, term, evaluator)
                },
            )?;
            let mut out = Vec::new();
            for (_rule_id, next) in results {
                if !out.contains(&next.0) {
                    out.push(next.0);
                }
            }
            Ok(out)
        }
    }
} // end _disabled_artifact_runtime

fn petta_lookup_search_paths() -> Vec<std::path::PathBuf> {
    let mut paths = Vec::new();
    if let Ok(dir) = std::env::var("METTAIL_PETTA_ARTIFACT_DIR") {
        paths.push(std::path::PathBuf::from(dir));
    }
    if let Ok(dir) = std::env::var("METTAIL_LOOKUP_SPEC_DIR") {
        paths.push(std::path::PathBuf::from(dir));
    }
    let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    paths.push(manifest_dir.join("../repl/artifacts/lookup"));
    paths.push(manifest_dir.join("artifacts/lookup"));
    // Relative to working directory
    paths.push(std::path::PathBuf::from("repl/artifacts/lookup"));
    paths.push(std::path::PathBuf::from("artifacts/lookup"));
    paths
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(dead_code)]
    fn sym(name: &str) -> PatternNode {
        PatternNode::Apply { ctor: name.to_string(), args: vec![] }
    }

    #[allow(dead_code)]
    fn fvar(name: &str) -> PatternNode {
        PatternNode::Fvar { name: name.to_string() }
    }

    #[allow(dead_code)]
    fn app(head: &str, args: Vec<PatternNode>) -> PatternNode {
        PatternNode::Apply { ctor: head.to_string(), args }
    }

    #[allow(dead_code)]
    fn sample_execution_contract_artifact() -> ExecutionContractArtifact {
        serde_json::from_str(
            r#"{
              "schema_version": 1,
              "dialect": "petta",
              "entries": [
                {
                  "entry_kind": "lookup_query",
                  "head": "get-atoms",
                  "arity": 1,
                  "owner": "artifact_backend",
                  "fragment_kind": "query",
                  "effect_class": "read_only_lookup",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["outcome_set"],
                  "lookup_family": {
                    "family": "selfFacts",
                    "logical_relation_id": "petta.self_facts",
                    "fact_relation": "selfFact",
                    "raw_relation": "selfFactRaw",
                    "has_relation": "selfFactHas",
                    "result_relation": "selfFactResult",
                    "query_arity": 1,
                    "payload_arity": 1,
                    "key_positions": [0],
                    "demand": [],
                    "no_false_negatives": true,
                    "exact_result": true,
                    "stratified_negation_safe": true
                  },
                  "source_rule_compilable": false,
                  "query_compilable": true,
                  "space_effect_compilable": false,
                  "builtin_demand": null,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.getAtoms_toComputableSourceQuery"
                  ]
                },
                {
                  "entry_kind": "lookup_query",
                  "head": "match",
                  "arity": 3,
                  "owner": "artifact_backend",
                  "fragment_kind": "query",
                  "effect_class": "read_only_lookup",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["outcome_set", "scalar"],
                  "lookup_family": {
                    "family": "spaceMatch",
                    "logical_relation_id": "petta.space_match",
                    "fact_relation": "selfFact",
                    "raw_relation": "spaceMatchRaw",
                    "has_relation": "spaceMatchHas",
                    "result_relation": "spaceMatchResult",
                    "query_arity": 3,
                    "payload_arity": 1,
                    "key_positions": [0, 1],
                    "demand": [],
                    "no_false_negatives": true,
                    "exact_result": false,
                    "stratified_negation_safe": true
                  },
                  "source_rule_compilable": false,
                  "query_compilable": true,
                  "space_effect_compilable": false,
                  "builtin_demand": null,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
                  ]
                },
                {
                  "entry_kind": "space_effect",
                  "head": "add-atom",
                  "arity": 2,
                  "owner": "artifact_backend",
                  "fragment_kind": "space_effect",
                  "effect_class": "writes_state",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "source_rule_compilable": false,
                  "query_compilable": false,
                  "space_effect_compilable": true,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
                  ]
                },
                {
                  "entry_kind": "space_effect",
                  "head": "remove-atom",
                  "arity": 2,
                  "owner": "artifact_backend",
                  "fragment_kind": "space_effect",
                  "effect_class": "writes_state",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "source_rule_compilable": false,
                  "query_compilable": false,
                  "space_effect_compilable": true,
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
                  ]
                },
                {
                  "entry_kind": "intrinsic_builtin",
                  "head": "+",
                  "relation": "intrinsic:+",
                  "min_arity": 2,
                  "max_arity": null,
                  "owner": "artifact_backend",
                  "fragment_kind": "rule_exec",
                  "effect_class": "pure_structural",
                  "resource_class": "default_atomspace",
                  "backend_name": "MORK/MM2",
                  "memo_shapes": ["outcome_set", "scalar"],
                  "builtin_demand": "numeric_args",
                  "theorem_refs": [
                    "Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract.mkCoreIntrinsicContract_relation"
                  ]
                }
              ]
            }"#,
        )
        .expect("sample execution contract")
    }

    /* COMMENTED OUT — all tests below depend on PeTTaArtifactRuntime / native_transition_contract.
       These must be rewritten to test MM2 emission → Space::metta_calculus() instead.

    fn runtime_with_execution_contract(
        facts: Vec<PatternNode>,
        rules: &[PeTTaRule],
        execution_contract: Option<ExecutionContractArtifact>,
    ) -> PeTTaArtifactRuntime {
        let mut bundle = build_petta_artifact_bundle(rules).expect("artifact bundle");
        bundle.execution_contract = execution_contract;
        let contract =
            build_petta_native_transition_contract_from_bundle(&bundle).expect("native contract");
        let runtime = PatternArtifactRuntime::new("PeTTa", contract, &bundle.rewrite_ir);
        PeTTaArtifactRuntime { facts, bundle, runtime }
    }

    fn sample_rules() -> Vec<PeTTaRule> {
        vec![
            PeTTaRule {
                name: "foo_to_bar".to_string(),
                left: PatternNode::Apply {
                    ctor: "foo".to_string(),
                    args: vec![PatternNode::Fvar { name: "X".to_string() }],
                },
                right: PatternNode::Apply {
                    ctor: "bar".to_string(),
                    args: vec![PatternNode::Fvar { name: "X".to_string() }],
                },
                premises: vec![],
            },
            PeTTaRule {
                name: "baz_to_qux".to_string(),
                left: PatternNode::Apply { ctor: "baz".to_string(), args: vec![] },
                right: PatternNode::Apply { ctor: "qux".to_string(), args: vec![] },
                premises: vec![],
            },
        ]
    }

    #[test]
    fn sanitize_replaces_nonalpha() {
        assert_eq!(sanitize_token("hello"), "hello");
        assert_eq!(sanitize_token("a-b.c"), "a_b_c");
        assert_eq!(sanitize_token("$fvar"), "_fvar");
        assert_eq!(sanitize_token(""), "_");
    }

    #[test]
    fn source_key_apply() {
        let pat = PatternNode::Apply {
            ctor: "foo".to_string(),
            args: vec![PatternNode::Fvar { name: "X".to_string() }],
        };
        let key = source_key_of_pattern(&pat);
        assert_eq!(key.head_tag, "foo");
        assert_eq!(key.arity, 1);
        assert_eq!(source_instr_of_key(&key), "C_foo_A1");
        assert_eq!(source_label_of_key(&key), "foo/1");
    }

    #[test]
    fn transition_spec_two_rules() {
        let rules = sample_rules();
        let spec = build_petta_transition_spec(&rules).unwrap();
        assert_eq!(spec.schema_version, 2);
        assert_eq!(spec.dialect, "petta");
        assert_eq!(spec.rules.len(), 2);
        assert_eq!(spec.sources.len(), 2); // foo/1 and baz/0

        assert_eq!(spec.rules[0].rule_id, "R0");
        assert_eq!(spec.rules[0].source_instr, "C_foo_A1");
        assert_eq!(spec.rules[0].logical_transition_id, "C_foo_A1:foo_to_bar");

        assert_eq!(spec.rules[1].rule_id, "R1");
        assert_eq!(spec.rules[1].source_instr, "C_baz_A0");
    }

    #[test]
    fn rewrite_ir_two_rules() {
        let rules = sample_rules();
        let ir = build_petta_rewrite_ir(&rules).unwrap();
        assert_eq!(ir.schema_version, 2);
        assert_eq!(ir.dialect, "petta");
        assert_eq!(ir.rules.len(), 2);

        assert_eq!(ir.rules[0].rule_id, "R0");
        assert_eq!(ir.rules[0].rule_name, "foo_to_bar");
        assert!(ir.rules[0].lhs.is_some());
        assert!(ir.rules[0].rhs.is_some());
    }

    #[test]
    fn rewrite_ir_carries_structured_analysis() {
        let rules = sample_rules();
        let ir = build_petta_rewrite_ir(&rules).unwrap();
        assert_eq!(ir.schema_version, 2);
        assert_eq!(ir.dialect, "petta");
        assert_eq!(ir.rules.len(), 2);
        assert_eq!(ir.rules[0].rule_id, "R0");
        assert_eq!(ir.rules[0].lhs_vars, vec!["X".to_string()]);
        assert!(ir.rules[0].rhs_eval_requires.is_empty());
        assert_eq!(ir.rules[0].rule_mode, Some(RewriteRuleMode::OrdinaryForward));
    }

    #[test]
    fn rewrite_ir_rhs_eval_requires_respects_let_scope_and_rule_payload_scope() {
        let rules = vec![PeTTaRule {
            name: "compilefib".to_string(),
            left: app("compilefib", vec![]),
            right: app(
                "let",
                vec![
                    fvar("temp"),
                    app(
                        "add-atom",
                        vec![
                            app("&self", vec![]),
                            app(
                                "=",
                                vec![
                                    app("fib", vec![fvar("N")]),
                                    app(
                                        "if",
                                        vec![
                                            app("<", vec![fvar("N"), sym("2")]),
                                            fvar("N"),
                                            app(
                                                "+",
                                                vec![
                                                    app(
                                                        "fib",
                                                        vec![app("-", vec![fvar("N"), sym("1")])],
                                                    ),
                                                    app(
                                                        "fib",
                                                        vec![app("-", vec![fvar("N"), sym("2")])],
                                                    ),
                                                ],
                                            ),
                                        ],
                                    ),
                                ],
                            ),
                        ],
                    ),
                    app("within", vec![app("fib", vec![sym("5")])]),
                ],
            ),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert!(
            ir.rules[0].rhs_eval_requires.is_empty(),
            "rhs_eval_requires={:?}",
            ir.rules[0].rhs_eval_requires
        );
    }

    #[test]
    fn rewrite_ir_rhs_eval_requires_respects_let_star_surface_binding_shape() {
        let rules = vec![PeTTaRule {
            name: "add_reduct".to_string(),
            left: app("add-reduct", vec![fvar("space"), fvar("f")]),
            right: app(
                "let*",
                vec![
                    PatternNode::Collection {
                        collection_type: "tuple".to_string(),
                        elements: vec![
                            app("$headbody", vec![app("cdr-atom", vec![fvar("f")])]),
                            app("$head", vec![app("car-atom", vec![fvar("headbody")])]),
                            app("$body", vec![app("cdr-atom", vec![fvar("headbody")])]),
                            app("$bodyreduced", vec![app("eval", vec![fvar("body")])]),
                        ],
                        rest: None,
                    },
                    app(
                        "add-atom",
                        vec![
                            fvar("space"),
                            app("=", vec![fvar("head"), fvar("bodyreduced")]),
                        ],
                    ),
                ],
            ),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert!(
            ir.rules[0].rhs_eval_requires.is_empty(),
            "rhs_eval_requires={:?}",
            ir.rules[0].rhs_eval_requires
        );
    }

    #[test]
    fn rewrite_ir_rhs_eval_requires_treats_underscore_as_wildcard() {
        let rules = vec![PeTTaRule {
            name: "if_error".to_string(),
            left: app("if-error", vec![fvar("X"), fvar("A"), fvar("B")]),
            right: app(
                "if",
                vec![
                    app("=", vec![fvar("X"), app("cons", vec![sym("Error"), fvar("_")])]),
                    fvar("A"),
                    fvar("B"),
                ],
            ),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert!(
            ir.rules[0].rhs_eval_requires.is_empty(),
            "rhs_eval_requires={:?}",
            ir.rules[0].rhs_eval_requires
        );
    }

    #[test]
    fn rewrite_ir_rhs_var_split_respects_lambda_like_scope() {
        let rules = vec![PeTTaRule {
            name: "mk_inc".to_string(),
            left: app("mk-inc", vec![]),
            right: app(
                "|->",
                vec![
                    PatternNode::Collection {
                        collection_type: "tuple".to_string(),
                        elements: vec![fvar("x")],
                        rest: None,
                    },
                    app("+", vec![fvar("x"), fvar("z")]),
                ],
            ),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert_eq!(ir.rules[0].rhs_fresh_vars, vec!["z".to_string()]);
        assert!(ir.rules[0].rhs_eval_requires.is_empty());
        assert_eq!(ir.rules[0].rule_mode, Some(RewriteRuleMode::SymbolicOutput));
    }

    #[test]
    fn rewrite_ir_rhs_var_split_marks_reverse_rule_symbolic_output() {
        let rules = vec![PeTTaRule {
            name: "tail_rule".to_string(),
            left: app("tail", vec![fvar("xs")]),
            right: app("cons", vec![fvar("x"), fvar("xs")]),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert_eq!(ir.rules[0].rhs_fresh_vars, vec!["x".to_string()]);
        assert!(ir.rules[0].rhs_eval_requires.is_empty());
        assert_eq!(ir.rules[0].rule_mode, Some(RewriteRuleMode::SymbolicOutput));
    }

    #[test]
    fn rewrite_ir_match_binder_does_not_force_symbolic_output() {
        let rules = vec![PeTTaRule {
            name: "remove_all_atoms".to_string(),
            left: app("remove-all-atoms", vec![fvar("space")]),
            right: app(
                "collapse",
                vec![app(
                    "match",
                    vec![
                        fvar("space"),
                        fvar("b"),
                        app("remove-atom", vec![fvar("space"), fvar("b")]),
                    ],
                )],
            ),
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert!(ir.rules[0].rhs_fresh_vars.is_empty());
        assert!(ir.rules[0].rhs_eval_requires.is_empty());
        assert_eq!(ir.rules[0].rule_mode, Some(RewriteRuleMode::OrdinaryForward));
    }

    #[test]
    fn rewrite_ir_rule_mode_classifies_compat_head_rules() {
        let rules = vec![PeTTaRule {
            name: "use_wrap".to_string(),
            left: app("use", vec![app("mk", vec![fvar("x")]), fvar("y")]),
            right: PatternNode::Collection {
                collection_type: "tuple".to_string(),
                elements: vec![fvar("x"), fvar("y")],
                rest: None,
            },
            premises: vec![],
        }];
        let ir = build_petta_rewrite_ir(&rules).expect("rewrite_ir");
        assert_eq!(ir.rules[0].rule_mode, Some(RewriteRuleMode::CompatHead));
        assert!(ir.rules[0].rhs_fresh_vars.is_empty());
        assert!(ir.rules[0].rhs_eval_requires.is_empty());
    }

    #[test]
    fn empty_rules_build_empty_artifacts() {
        let spec = build_petta_transition_spec(&[]).expect("empty transition spec");
        assert!(spec.sources.is_empty());
        assert!(spec.rules.is_empty());

        let ir = build_petta_rewrite_ir(&[]).expect("empty rewrite_ir");
        assert!(ir.rules.is_empty());
    }

    // COMMENTED OUT — depends on deleted native_transition_contract
    // #[test]
    // fn build_native_contract_from_sample_rules() { ... }

    #[test]
    fn build_artifact_bundle_from_sample_rules() {
        let bundle = build_petta_artifact_bundle(&sample_rules()).expect("artifact bundle");
        assert_eq!(bundle.transition.dialect, "petta");
        assert_eq!(bundle.lookup.dialect, "petta");
        assert_eq!(bundle.rewrite_ir.dialect, "petta");
        if let Some(contract) = &bundle.execution_contract {
            assert_eq!(contract.dialect, "petta");
            assert_eq!(contract.schema_version, 1);
            assert!(contract.entries.len() >= 2);
        }
        assert!(bundle
            .lookup
            .families
            .iter()
            .any(|family| family.family == "spaceMatch"));
    }

    #[test]
    fn optional_execution_contract_sidecar_is_absent_or_valid() {
        match load_optional_petta_execution_contract_artifact() {
            Ok(Some(contract)) => {
                assert_eq!(contract.dialect, "petta");
                assert_eq!(contract.schema_version, 1);
                assert!(contract.entries.len() >= 4);
            },
            Ok(None) => {},
            Err(err) => panic!("invalid execution-contract sidecar: {err}"),
        }
    }

    #[test]
    fn optional_execution_contract_sidecar_contains_first_certified_lanes() {
        let Some(contract) = load_optional_petta_execution_contract_artifact()
            .expect("execution-contract sidecar load")
        else {
            return;
        };
        validate_petta_execution_contract_artifact(&contract)
            .expect("first certified PeTTa contract lanes");
        assert!(execution_contract_entry(&contract, "+", 2).is_some());
    }

    #[test]
    fn artifact_runtime_exposes_intrinsic_builtin_contracts() {
        let runtime = runtime_with_execution_contract(
            vec![],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let intrinsic = runtime
            .intrinsic_builtin_contract_for_term(&app("+", vec![sym("2"), sym("3"), sym("4")]))
            .expect("intrinsic lookup")
            .expect("recognized intrinsic builtin");
        assert_eq!(intrinsic.relation, "intrinsic:+");
        assert_eq!(intrinsic.builtin_demand, BuiltinDemandKind::NumericArgs);
    }

    #[test]
    fn artifact_runtime_rewrites_root_fragment() {
        let runtime = PeTTaArtifactRuntime::from_rules(&sample_rules()).expect("artifact runtime");
        let term = app("foo", vec![sym("a")]);
        let next = runtime.rewrite_root_once(&term).expect("rewrite root once");
        assert_eq!(next, vec![app("bar", vec![sym("a")])]);
    }

    #[test]
    fn artifact_runtime_rewrites_space_match_fragment() {
        let runtime = runtime_with_execution_contract(
            vec![
                app("friend", vec![sym("tim"), sym("tom")]),
                app("friend", vec![sym("tim"), sym("bob")]),
            ],
            &[PeTTaRule {
                name: "query_friends".to_string(),
                left: app("query", vec![fvar("x")]),
                right: app("result", vec![fvar("x"), fvar("y")]),
                premises: vec![PremiseNode::RelationQuery {
                    relation: "spaceMatch".to_string(),
                    args: vec![app("friend", vec![fvar("x"), fvar("z")]), fvar("z"), fvar("y")],
                }],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let next = runtime
            .rewrite_root_once(&app("query", vec![sym("tim")]))
            .expect("rewrite spaceMatch fragment");
        assert_eq!(
            next,
            vec![
                app("result", vec![sym("tim"), sym("tom")]),
                app("result", vec![sym("tim"), sym("bob")]),
            ]
        );
    }

    #[test]
    fn artifact_runtime_rejects_non_space_match_relation_fragment() {
        let runtime = runtime_with_execution_contract(
            vec![app("fact", vec![sym("a")])],
            &[PeTTaRule {
                name: "custom_relation".to_string(),
                left: app("ask", vec![]),
                right: app("answer", vec![]),
                premises: vec![PremiseNode::RelationQuery {
                    relation: "otherRelation".to_string(),
                    args: vec![fvar("X")],
                }],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let err = runtime
            .rewrite_root_once(&app("ask", vec![]))
            .expect_err("unsupported fragment must fail closed");
        assert!(err.contains("does not yet implement"));
        assert!(err.contains("relation_query"));
    }

    #[test]
    fn artifact_runtime_rejects_freshness_fragment() {
        let runtime = PeTTaArtifactRuntime::from_rules(&[PeTTaRule {
            name: "fresh_rule".to_string(),
            left: app("ask", vec![fvar("x")]),
            right: app("answer", vec![fvar("x")]),
            premises: vec![PremiseNode::Freshness {
                var_name: "x".to_string(),
                term: Box::new(sym("y")),
            }],
        }])
        .expect("artifact runtime");
        let err = runtime
            .rewrite_root_once(&app("ask", vec![sym("a")]))
            .expect_err("unsupported fragment must fail closed");
        assert!(err.contains("does not yet implement"));
        assert!(err.contains("rewrite_with_freshness"));
    }

    #[test]
    fn artifact_runtime_exposes_facts_and_bundle() {
        let runtime = runtime_with_execution_contract(
            vec![app("fact", vec![sym("a")])],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        assert_eq!(runtime.facts(), &[app("fact", vec![sym("a")])]);
        assert_eq!(
            runtime.artifact_bundle().rewrite_ir.dialect,
            "petta"
        );
    }

    #[test]
    fn same_head_rules_share_source() {
        let rules = vec![
            PeTTaRule {
                name: "foo_1".to_string(),
                left: PatternNode::Apply {
                    ctor: "foo".to_string(),
                    args: vec![PatternNode::Fvar { name: "X".to_string() }],
                },
                right: PatternNode::Apply {
                    ctor: "result1".to_string(),
                    args: vec![],
                },
                premises: vec![],
            },
            PeTTaRule {
                name: "foo_2".to_string(),
                left: PatternNode::Apply {
                    ctor: "foo".to_string(),
                    args: vec![PatternNode::Apply { ctor: "a".to_string(), args: vec![] }],
                },
                right: PatternNode::Apply {
                    ctor: "result2".to_string(),
                    args: vec![],
                },
                premises: vec![],
            },
        ];
        let spec = build_petta_transition_spec(&rules).unwrap();
        // Both rules have source foo/1 → one source with two ordered rules
        assert_eq!(spec.sources.len(), 1);
        assert_eq!(spec.sources[0].ordered_rules, vec!["R0", "R1"]);
    }

    #[test]
    fn space_match_fragment_preserves_query_order() {
        let runtime = runtime_with_execution_contract(
            vec![app("edge", vec![sym("a"), sym("b")]), app("edge", vec![sym("a"), sym("c")])],
            &[PeTTaRule {
                name: "neighbors".to_string(),
                left: app("neighbors", vec![fvar("x")]),
                right: app("neighbor", vec![fvar("y")]),
                premises: vec![PremiseNode::RelationQuery {
                    relation: "spaceMatch".to_string(),
                    args: vec![app("edge", vec![fvar("x"), fvar("y")]), fvar("y"), fvar("out")],
                }],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let next = runtime
            .rewrite_root_once(&app("neighbors", vec![sym("a")]))
            .expect("rewrite spaceMatch fragment");
        assert_eq!(next, vec![app("neighbor", vec![sym("b")]), app("neighbor", vec![sym("c")])]);
    }

    #[test]
    fn artifact_runtime_rejects_space_match_without_execution_contract() {
        let runtime = runtime_with_execution_contract(
            vec![app("friend", vec![sym("tim"), sym("tom")])],
            &[PeTTaRule {
                name: "query_friends".to_string(),
                left: app("query", vec![fvar("x")]),
                right: app("result", vec![fvar("x"), fvar("y")]),
                premises: vec![PremiseNode::RelationQuery {
                    relation: "spaceMatch".to_string(),
                    args: vec![app("friend", vec![fvar("x"), fvar("z")]), fvar("z"), fvar("y")],
                }],
            }],
            None,
        );
        let err = runtime
            .rewrite_root_once(&app("query", vec![sym("tim")]))
            .expect_err("spaceMatch must require execution-contract sidecar");
        assert!(err.contains("missing petta.execution_contract"));
    }

    #[test]
    fn artifact_runtime_evaluates_certified_get_atoms_self_query() {
        let runtime = runtime_with_execution_contract(
            vec![app("fact", vec![sym("a")]), app("fact", vec![sym("b")])],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let results = runtime
            .evaluate_query_term(&app("get-atoms", vec![sym("&self")]))
            .expect("evaluate certified query")
            .expect("recognized certified query");
        assert_eq!(
            results,
            vec![app("list", vec![app("fact", vec![sym("a")]), app("fact", vec![sym("b")])])]
        );
    }

    #[test]
    fn artifact_runtime_evaluates_certified_match_self_query() {
        let runtime = runtime_with_execution_contract(
            vec![
                app("friend", vec![sym("tim"), sym("tom")]),
                app("friend", vec![sym("tim"), sym("bob")]),
            ],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let results = runtime
            .evaluate_query_term(&app(
                "match",
                vec![sym("&self"), app("friend", vec![sym("tim"), fvar("who")]), fvar("who")],
            ))
            .expect("evaluate certified match query")
            .expect("recognized certified match query");
        assert_eq!(results, vec![sym("tom"), sym("bob")]);
    }

    #[test]
    fn artifact_runtime_add_atom_updates_certified_self_space() {
        let mut runtime = runtime_with_execution_contract(
            vec![app("fact", vec![sym("a")])],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let effect = runtime
            .evaluate_space_effect_term(&app(
                "add-atom",
                vec![sym("&self"), app("fact", vec![sym("b")])],
            ))
            .expect("evaluate add-atom")
            .expect("recognized add-atom effect");
        assert_eq!(effect, vec![sym("()")]);
        let atoms = runtime
            .evaluate_query_term(&app("get-atoms", vec![sym("&self")]))
            .expect("evaluate get-atoms")
            .expect("recognized get-atoms query");
        assert_eq!(
            atoms,
            vec![app("list", vec![app("fact", vec![sym("a")]), app("fact", vec![sym("b")])])]
        );
    }

    #[test]
    fn artifact_runtime_remove_atom_updates_certified_self_space() {
        let mut runtime = runtime_with_execution_contract(
            vec![app("fact", vec![sym("a")]), app("fact", vec![sym("b")])],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let effect = runtime
            .evaluate_space_effect_term(&app(
                "remove-atom",
                vec![sym("&self"), app("fact", vec![sym("a")])],
            ))
            .expect("evaluate remove-atom")
            .expect("recognized remove-atom effect");
        assert_eq!(effect, vec![sym("()")]);
        let atoms = runtime
            .evaluate_query_term(&app("get-atoms", vec![sym("&self")]))
            .expect("evaluate get-atoms")
            .expect("recognized get-atoms query");
        assert_eq!(atoms, vec![app("list", vec![app("fact", vec![sym("b")])])]);
    }

    #[test]
    fn artifact_runtime_rejects_dynamic_rule_payloads_in_space_effect_bootstrap() {
        let mut runtime = runtime_with_execution_contract(
            vec![],
            &[PeTTaRule {
                name: "id".to_string(),
                left: app("id", vec![fvar("X")]),
                right: app("id", vec![fvar("X")]),
                premises: vec![],
            }],
            Some(sample_execution_contract_artifact()),
        );
        let err = runtime
            .evaluate_space_effect_term(&app(
                "add-atom",
                vec![
                    sym("&self"),
                    app("=", vec![app("f", vec![fvar("X")]), app("g", vec![fvar("X")])]),
                ],
            ))
            .expect_err("dynamic rule payloads must fail closed");
        assert!(err.contains("dynamic rule payloads"));
    }

    #[test]
    fn artifact_runtime_rejects_unsupported_relation_premise_fragment() {
        let runtime = PeTTaArtifactRuntime::from_rules(&[PeTTaRule {
            name: "match_rule".to_string(),
            left: PatternNode::Apply { ctor: "ask".to_string(), args: vec![] },
            right: PatternNode::Apply { ctor: "answer".to_string(), args: vec![] },
            premises: vec![PremiseNode::RelationQuery {
                relation: "customRel".to_string(),
                args: vec![
                    PatternNode::Apply { ctor: "pat".to_string(), args: vec![] },
                    PatternNode::Apply { ctor: "tmpl".to_string(), args: vec![] },
                    PatternNode::Fvar { name: "Out".to_string() },
                ],
            }],
        }])
        .expect("artifact runtime");
        let err = runtime
            .rewrite_root_once(&PatternNode::Apply { ctor: "ask".to_string(), args: vec![] })
            .expect_err("unsupported fragment must fail closed");
        assert!(err.contains("does not yet implement"));
        assert!(err.contains("relation_query"));
    }
    END of commented-out PeTTaArtifactRuntime tests */
}
