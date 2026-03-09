use crate::artifact_contract::{LookupArtifact, RewriteIRArtifact, TransitionArtifact};
use mettail_runtime::dispatch_ordered_rules;
use std::collections::HashMap;
use std::sync::OnceLock;

#[derive(Debug, Clone)]
pub struct NativeTransitionRuleMeta {
    pub rule_id: String,
    pub rule_name: String,
    pub logical_transition_id: String,
    pub source_instr: String,
    pub transition_kind: String,
    pub guard_family: String,
    pub effect_kind: String,
}

#[derive(Debug, Default)]
pub struct NativeTransitionContract {
    by_source_instr: HashMap<String, Vec<String>>,
    by_rule_id: HashMap<String, NativeTransitionRuleMeta>,
}

impl NativeTransitionContract {
    pub fn ordered_rules_for(&self, source_instr: &str) -> Option<&[String]> {
        self.by_source_instr
            .get(source_instr)
            .map(|rules| rules.as_slice())
    }

    pub fn ordered_rule_map(&self) -> &HashMap<String, Vec<String>> {
        &self.by_source_instr
    }

    pub fn rule(&self, rule_id: &str) -> Option<&NativeTransitionRuleMeta> {
        self.by_rule_id.get(rule_id)
    }
}

pub fn expect_rule_contract(
    dialect_name: &str,
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
            "{dialect_name} contract mismatch for rule '{}' (logical id '{}'): expected kind='{}' guard='{}' effect='{}', got kind='{}' guard='{}' effect='{}'",
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

pub fn dispatch_checked_source_rules<T: std::fmt::Display>(
    dialect_name: &str,
    contract: &NativeTransitionContract,
    source_instr: &str,
    mut apply: impl FnMut(&str, &NativeTransitionRuleMeta) -> Result<Vec<T>, String>,
) -> Result<Vec<(String, T)>, String> {
    let ordered = contract.ordered_rules_for(source_instr).ok_or_else(|| {
        format!(
            "{dialect_name} transition artifact missing source instruction '{}'",
            source_instr
        )
    })?;

    dispatch_ordered_rules(
        ordered,
        |rule| {
            let meta = contract.rule(rule).cloned().ok_or_else(|| {
                format!(
                    "{dialect_name} rewrite contract missing metadata for rule '{}' listed under source '{}'",
                    rule, source_instr
                )
            })?;
            if meta.source_instr != source_instr {
                return Err(format!(
                    "{dialect_name} rewrite contract mismatch: rule '{}' expected source '{}', got '{}'",
                    rule, source_instr, meta.source_instr
                ));
            }
            Ok(meta)
        },
        |rule, meta| apply(rule, meta),
    )
}

pub fn dispatch_active_source_step<T: std::fmt::Display>(
    dialect_name: &str,
    contract: &NativeTransitionContract,
    active_source: Result<Option<&str>, String>,
    apply: impl FnMut(&str, &NativeTransitionRuleMeta) -> Result<Vec<T>, String>,
) -> Result<Vec<(String, T)>, String> {
    let Some(source_instr) = active_source? else {
        return Ok(Vec::new());
    };
    dispatch_checked_source_rules(dialect_name, contract, source_instr, apply)
}

pub fn cached_contract_result<T>(
    slot: &'static OnceLock<Result<T, String>>,
    load: impl FnOnce() -> Result<T, String>,
) -> Result<&'static T, String> {
    match slot.get_or_init(load) {
        Ok(value) => Ok(value),
        Err(err) => Err(err.clone()),
    }
}

pub fn build_native_transition_contract(
    dialect_name: &str,
    transition: TransitionArtifact,
    lookup: LookupArtifact,
    rewrite_ir: RewriteIRArtifact,
    validate_lookup: impl FnOnce(&LookupArtifact) -> Result<(), String>,
) -> Result<NativeTransitionContract, String> {
    validate_lookup(&lookup)?;

    let mut rewrite_by_rule: HashMap<String, _> = HashMap::new();
    for rule in rewrite_ir.rules {
        let rid = rule.rule_id.clone();
        if rule.rule_name.trim().is_empty() {
            return Err(format!("{dialect_name} rewrite-ir has empty rule_name for rule '{rid}'"));
        }
        if rule.source_instr.trim().is_empty() {
            return Err(format!(
                "{dialect_name} rewrite-ir has empty source_instr for rule '{rid}'"
            ));
        }
        if rewrite_by_rule.insert(rid.clone(), rule).is_some() {
            return Err(format!("{dialect_name} rewrite-ir has duplicate rule id '{rid}'"));
        }
    }

    let mut by_rule_id = HashMap::new();
    for tr_rule in transition.rules {
        let rw = rewrite_by_rule.get(&tr_rule.rule_id).ok_or_else(|| {
            format!(
                "{dialect_name} rewrite contract mismatch: transition rule '{}' missing from rewrite-ir",
                tr_rule.rule_id
            )
        })?;
        if rw.source_instr != tr_rule.source_instr {
            return Err(format!(
                "{dialect_name} rewrite contract mismatch: rule '{}' source differs (transition='{}', rewrite_ir='{}')",
                tr_rule.rule_id, tr_rule.source_instr, rw.source_instr
            ));
        }
        if tr_rule.sem_key.transition_kind.trim().is_empty()
            || tr_rule.sem_key.guard_family.trim().is_empty()
            || tr_rule.sem_key.effect_kind.trim().is_empty()
        {
            return Err(format!(
                "{dialect_name} transition rule '{}' has incomplete semantic key",
                tr_rule.rule_id
            ));
        }
        let meta = NativeTransitionRuleMeta {
            rule_id: tr_rule.rule_id.clone(),
            rule_name: rw.rule_name.clone(),
            logical_transition_id: tr_rule.logical_transition_id.clone(),
            source_instr: tr_rule.source_instr.clone(),
            transition_kind: tr_rule.sem_key.transition_kind.clone(),
            guard_family: tr_rule.sem_key.guard_family.clone(),
            effect_kind: tr_rule.sem_key.effect_kind.clone(),
        };
        if by_rule_id.insert(tr_rule.rule_id.clone(), meta).is_some() {
            return Err(format!(
                "{dialect_name} transition artifact has duplicate rule id '{}'",
                tr_rule.rule_id
            ));
        }
    }

    for rid in rewrite_by_rule.keys() {
        if !by_rule_id.contains_key(rid) {
            return Err(format!(
                "{dialect_name} rewrite contract mismatch: rewrite-ir rule '{}' missing from transition artifact",
                rid
            ));
        }
    }

    let mut by_source_instr = HashMap::new();
    for src in transition.sources {
        if src.ordered_rules.is_empty() {
            return Err(format!(
                "{dialect_name} transition source '{}' has empty ordered_rules",
                src.source_instr
            ));
        }
        for rid in &src.ordered_rules {
            let meta = by_rule_id.get(rid).ok_or_else(|| {
                format!(
                    "{dialect_name} transition source '{}' references unknown rule '{}'",
                    src.source_instr, rid
                )
            })?;
            if meta.source_instr != src.source_instr {
                return Err(format!(
                    "{dialect_name} transition source '{}' references rule '{}' mapped to source '{}'",
                    src.source_instr, rid, meta.source_instr
                ));
            }
        }
        by_source_instr.insert(src.source_instr, src.ordered_rules);
    }

    Ok(NativeTransitionContract { by_source_instr, by_rule_id })
}
