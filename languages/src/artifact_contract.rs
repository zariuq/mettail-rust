use serde::de::DeserializeOwned;
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TransitionSource {
    pub source_instr: String,
    pub source_label: String,
    pub ordered_rules: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TransitionSemKey {
    pub source_instr_class: String,
    pub transition_kind: String,
    pub guard_family: String,
    pub effect_kind: String,
    pub dialect_ext: Option<String>,
    pub contracts: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TransitionRule {
    pub logical_transition_id: String,
    pub source_instr: String,
    pub source_label: String,
    pub rule_id: String,
    pub sem_key: TransitionSemKey,
    pub priority: u64,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TransitionArtifact {
    pub schema_version: u64,
    pub dialect: String,
    pub sources: Vec<TransitionSource>,
    pub rules: Vec<TransitionRule>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRRule {
    pub rule_id: String,
    pub rule_name: String,
    pub source_instr: String,
    pub source_label: String,
    pub priority: u64,
    pub left_repr: String,
    pub right_repr: String,
    pub premise_relations: Vec<String>,
    #[serde(default)]
    pub lhs: Option<PatternNode>,
    #[serde(default)]
    pub rhs: Option<PatternNode>,
    #[serde(default)]
    pub premises: Vec<PremiseNode>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRArtifact {
    pub schema_version: u64,
    pub dialect: String,
    pub rules: Vec<RewriteIRRule>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRV2PremiseVarFlow {
    pub premise_index: u64,
    pub premise_vars: Vec<String>,
    pub introduced_vars: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRV2RootUpdateHint {
    pub lhs_root_ctor: String,
    pub rhs_root_ctor: String,
    pub lhs_arity: u64,
    pub rhs_arity: u64,
    pub preserved_arg_positions: Vec<u64>,
    pub changed_arg_positions: Vec<u64>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRV2Rule {
    pub rule_id: String,
    pub rule_name: String,
    pub source_instr: String,
    pub source_label: String,
    pub priority: u64,
    pub lhs_vars: Vec<String>,
    pub premise_var_flow: Vec<RewriteIRV2PremiseVarFlow>,
    pub rhs_vars: Vec<String>,
    pub rhs_requires: Vec<String>,
    pub root_update: Option<RewriteIRV2RootUpdateHint>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RewriteIRV2Artifact {
    pub schema_version: u64,
    pub dialect: String,
    pub artifact_label: String,
    pub base_rewrite_ir_schema_version: u64,
    pub rules: Vec<RewriteIRV2Rule>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PatternNode {
    Bvar {
        index: u64,
    },
    Fvar {
        name: String,
    },
    Apply {
        ctor: String,
        args: Vec<PatternNode>,
    },
    Lambda {
        body: Box<PatternNode>,
    },
    MultiLambda {
        arity: u64,
        body: Box<PatternNode>,
    },
    Subst {
        body: Box<PatternNode>,
        repl: Box<PatternNode>,
    },
    Collection {
        collection_type: String,
        elements: Vec<PatternNode>,
        rest: Option<String>,
    },
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PremiseNode {
    Freshness {
        var_name: String,
        term: Box<PatternNode>,
    },
    Congruence {
        lhs: Box<PatternNode>,
        rhs: Box<PatternNode>,
    },
    RelationQuery {
        relation: String,
        args: Vec<PatternNode>,
    },
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupDemandArg {
    pub position: u64,
    pub mode: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupDemand {
    pub relation: String,
    pub logical_relation_id: String,
    pub scope_signature: String,
    pub arity: u64,
    pub args: Vec<LookupDemandArg>,
    pub usage_kind: String,
    pub negated_target: Option<String>,
    pub in_recursive_scc: bool,
    pub hot_path: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupContracts {
    pub no_false_negatives: bool,
    pub exact_result: bool,
    pub stratified_negation_safe: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupFamily {
    pub family: String,
    pub logical_relation_id: String,
    pub fact_relation: String,
    pub raw_relation: String,
    pub has_relation: String,
    pub result_relation: Option<String>,
    pub query_arity: u64,
    pub payload_arity: u64,
    pub key_positions: Vec<u64>,
    pub demand: Vec<LookupDemand>,
    pub contracts: LookupContracts,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupArtifact {
    pub schema_version: u64,
    pub dialect: String,
    pub families: Vec<LookupFamily>,
}

pub fn fnv1a64(text: &str) -> u64 {
    const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV64_PRIME: u64 = 1_099_511_628_211;
    text.bytes()
        .fold(FNV64_OFFSET, |h, b| (h ^ (b as u64)).wrapping_mul(FNV64_PRIME))
}

pub fn read_with_checksum(json_path: &Path, checksum_path: &Path) -> Result<String, String> {
    let json_text_raw = fs::read_to_string(json_path)
        .map_err(|e| format!("failed reading {}: {}", json_path.display(), e))?;
    let checksum_text_raw = fs::read_to_string(checksum_path)
        .map_err(|e| format!("failed reading {}: {}", checksum_path.display(), e))?;
    let json_text = json_text_raw.trim().to_string();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().map_err(|e| {
        format!("invalid checksum '{}' at {}: {}", checksum_text, checksum_path.display(), e)
    })?;
    let actual_checksum = fnv1a64(&json_text);
    if expected_checksum != actual_checksum {
        return Err(format!(
            "checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }
    Ok(json_text)
}

pub fn load_json_with_checksum<T: DeserializeOwned>(
    json_path: &Path,
    checksum_path: &Path,
    label: &str,
) -> Result<T, String> {
    let json_text = read_with_checksum(json_path, checksum_path)?;
    serde_json::from_str(&json_text)
        .map_err(|e| format!("invalid {} artifact {}: {}", label, json_path.display(), e))
}

pub fn parse_rule_ids_from_generated_language(path: &Path) -> Result<BTreeSet<String>, String> {
    let text = fs::read_to_string(path)
        .map_err(|e| format!("failed reading {}: {}", path.display(), e))?;
    let mut ids = BTreeSet::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        let Some(first_tok) = trimmed.split_whitespace().next() else {
            continue;
        };
        let candidate = first_tok.trim();
        let Some(digits) = candidate.strip_prefix('R') else {
            continue;
        };
        if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
            continue;
        }
        ids.insert(candidate.to_string());
    }
    if ids.is_empty() {
        return Err(format!(
            "no rewrite rule ids found in generated language file {}",
            path.display()
        ));
    }
    Ok(ids)
}

pub fn index_rewrite_ir_v2_rules_by_id(
    artifact: &RewriteIRV2Artifact,
) -> Result<BTreeMap<String, RewriteIRV2Rule>, String> {
    let mut indexed = BTreeMap::new();
    for rule in &artifact.rules {
      if indexed.insert(rule.rule_id.clone(), rule.clone()).is_some() {
            return Err(format!(
                "duplicate rewrite-ir-v2 rule_id '{}' in dialect {}",
                rule.rule_id, artifact.dialect
            ));
        }
    }
    Ok(indexed)
}
