use anyhow::{anyhow, bail, Context, Result};
use serde::Deserialize;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

const EXPECTED_LOOKUP_PLAN_SCHEMA_VERSION: u64 = 2;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LookupUsageKind {
    Enumerate,
    Exists,
    NegatedExists,
    AggregateInput,
}

impl LookupUsageKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Enumerate => "enumerate",
            Self::Exists => "exists",
            Self::NegatedExists => "negated_exists",
            Self::AggregateInput => "aggregate_input",
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum LookupArgMode {
    Bound,
    Free,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupDemandArg {
    pub position: u64,
    pub mode: LookupArgMode,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupDemandSignature {
    pub relation: String,
    pub logical_relation_id: String,
    pub scope_signature: String,
    pub arity: u64,
    pub args: Vec<LookupDemandArg>,
    pub usage_kind: LookupUsageKind,
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
pub struct LookupFamilyPlan {
    pub family: String,
    pub logical_relation_id: String,
    pub fact_relation: String,
    pub raw_relation: String,
    pub has_relation: String,
    pub result_relation: String,
    pub query_arity: u64,
    pub payload_arity: u64,
    pub key_positions: Vec<u64>,
    pub demand: Vec<LookupDemandSignature>,
    pub contracts: LookupContracts,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LookupPlanArtifact {
    pub schema_version: u64,
    pub dialect: String,
    pub families: Vec<LookupFamilyPlan>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedLookupPlan {
    pub artifact: LookupPlanArtifact,
    pub json_path: PathBuf,
    pub checksum_path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LookupRelationMetadata {
    pub logical_relation_id: String,
    pub scope_signature: String,
    pub usage_kind: Option<String>,
}

fn fnv1a64(text: &str) -> u64 {
    const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV64_PRIME: u64 = 1_099_511_628_211;
    text.bytes()
        .fold(FNV64_OFFSET, |h, b| (h ^ (b as u64)).wrapping_mul(FNV64_PRIME))
}

fn candidate_lookup_dirs() -> Vec<PathBuf> {
    if let Ok(from_env) = std::env::var("METTAIL_LOOKUP_PLAN_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    let mut dirs = Vec::new();
    dirs.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/lookup"));
    dirs.push(PathBuf::from("artifacts/lookup"));

    for prefix in ["..", "../..", "../../.."] {
        dirs.push(PathBuf::from(prefix).join("lean-projects/algorithms/artifacts/lookup"));
        dirs.push(PathBuf::from(prefix).join("lean-projects/mettapedia/artifacts/lookup"));
    }

    dirs.push(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/algorithms/artifacts/lookup"),
    );
    dirs.push(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/mettapedia/artifacts/lookup"),
    );
    dirs
}

fn lookup_plan_paths(base_dir: &Path, dialect_key: &str) -> (PathBuf, PathBuf) {
    let base = format!("{dialect_key}.lookup_plan");
    (base_dir.join(format!("{base}.json")), base_dir.join(format!("{base}.checksum")))
}

fn build_scope_signature(query_arity: u64, payload_arity: u64, key_positions: &[u64]) -> String {
    let mut parts = Vec::new();
    for pos in 0..query_arity {
        let marker = if key_positions.contains(&pos) {
            "b"
        } else {
            "f"
        };
        parts.push(format!("{marker}{pos}"));
    }
    for payload_pos in 0..payload_arity {
        let pos = query_arity + payload_pos;
        parts.push(format!("f{pos}"));
    }
    parts.join("+")
}

fn validate_lookup_plan(artifact: &LookupPlanArtifact, json_path: &Path) -> Result<()> {
    if artifact.families.is_empty() {
        bail!("invalid lookup plan at {}: families cannot be empty", json_path.display());
    }

    for family in &artifact.families {
        if family.family.trim().is_empty()
            || family.logical_relation_id.trim().is_empty()
            || family.fact_relation.trim().is_empty()
            || family.raw_relation.trim().is_empty()
            || family.has_relation.trim().is_empty()
            || family.result_relation.trim().is_empty()
        {
            bail!(
                "invalid lookup family '{}' at {}: relation ids must be non-empty",
                family.family,
                json_path.display()
            );
        }

        for key in &family.key_positions {
            if *key >= family.query_arity {
                bail!(
                    "invalid lookup family '{}' at {}: key position {} is out of query arity {}",
                    family.family,
                    json_path.display(),
                    key,
                    family.query_arity
                );
            }
        }

        for demand in &family.demand {
            if demand.relation.trim().is_empty()
                || demand.logical_relation_id.trim().is_empty()
                || demand.scope_signature.trim().is_empty()
            {
                bail!(
                    "invalid demand signature in family '{}' at {}: relation/logical_relation_id/scope_signature must be non-empty",
                    family.family,
                    json_path.display()
                );
            }

            if demand.args.len() as u64 != demand.arity {
                bail!(
                    "invalid demand signature '{}' in family '{}' at {}: args length {} does not match arity {}",
                    demand.relation,
                    family.family,
                    json_path.display(),
                    demand.args.len(),
                    demand.arity
                );
            }

            for arg in &demand.args {
                if arg.position >= demand.arity {
                    bail!(
                        "invalid demand signature '{}' in family '{}' at {}: arg position {} is out of arity {}",
                        demand.relation,
                        family.family,
                        json_path.display(),
                        arg.position,
                        demand.arity
                    );
                }
            }

            match demand.usage_kind {
                LookupUsageKind::NegatedExists => {
                    let Some(target) = demand.negated_target.as_deref() else {
                        bail!(
                            "invalid negated_exists demand '{}' in family '{}' at {}: missing negated_target",
                            demand.relation,
                            family.family,
                            json_path.display()
                        );
                    };
                    if target != family.has_relation {
                        bail!(
                            "invalid negated_exists demand '{}' in family '{}' at {}: negated_target '{}' must equal has_relation '{}'",
                            demand.relation,
                            family.family,
                            json_path.display(),
                            target,
                            family.has_relation
                        );
                    }
                },
                _ => {
                    if demand.negated_target.is_some() {
                        bail!(
                            "invalid demand '{}' in family '{}' at {}: negated_target is only valid for usage_kind=negated_exists",
                            demand.relation,
                            family.family,
                            json_path.display()
                        );
                    }
                },
            }
        }
    }
    Ok(())
}

fn load_from_paths(json_path: &Path, checksum_path: &Path) -> Result<LoadedLookupPlan> {
    let json_text_raw = fs::read_to_string(json_path)
        .with_context(|| format!("failed reading lookup plan json {}", json_path.display()))?;
    let checksum_text_raw = fs::read_to_string(checksum_path).with_context(|| {
        format!("failed reading lookup plan checksum {}", checksum_path.display())
    })?;
    let json_text = json_text_raw.trim();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().with_context(|| {
        format!(
            "invalid lookup plan checksum '{}' at {}",
            checksum_text,
            checksum_path.display()
        )
    })?;
    let actual_checksum = fnv1a64(json_text);
    if actual_checksum != expected_checksum {
        return Err(anyhow!(
            "lookup plan checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }

    let artifact: LookupPlanArtifact = serde_json::from_str(json_text)
        .with_context(|| format!("invalid lookup plan json payload at {}", json_path.display()))?;
    if artifact.schema_version != EXPECTED_LOOKUP_PLAN_SCHEMA_VERSION {
        bail!(
            "unsupported lookup plan schema_version {} at {} (expected {})",
            artifact.schema_version,
            json_path.display(),
            EXPECTED_LOOKUP_PLAN_SCHEMA_VERSION
        );
    }
    validate_lookup_plan(&artifact, json_path)?;

    Ok(LoadedLookupPlan {
        artifact,
        json_path: json_path.to_path_buf(),
        checksum_path: checksum_path.to_path_buf(),
    })
}

pub fn try_load_lookup_plan(dialect_key: &str) -> Result<Option<LoadedLookupPlan>> {
    let mut first_error: Option<anyhow::Error> = None;
    for dir in candidate_lookup_dirs() {
        let (json_path, checksum_path) = lookup_plan_paths(&dir, dialect_key);
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }

        match load_from_paths(&json_path, &checksum_path) {
            Ok(loaded) => return Ok(Some(loaded)),
            Err(e) => {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => Ok(None),
    }
}

pub fn relation_metadata_index(
    artifact: &LookupPlanArtifact,
) -> HashMap<String, LookupRelationMetadata> {
    let mut out = HashMap::new();

    for family in &artifact.families {
        let query_scope = build_scope_signature(family.query_arity, 0, &family.key_positions);
        let result_scope =
            build_scope_signature(family.query_arity, family.payload_arity, &family.key_positions);

        out.insert(
            family.raw_relation.clone(),
            LookupRelationMetadata {
                logical_relation_id: format!("{}.raw", family.logical_relation_id),
                scope_signature: result_scope.clone(),
                usage_kind: Some("enumerate".to_string()),
            },
        );

        out.insert(
            family.has_relation.clone(),
            LookupRelationMetadata {
                logical_relation_id: format!("{}.has", family.logical_relation_id),
                scope_signature: query_scope,
                usage_kind: Some("exists".to_string()),
            },
        );

        out.insert(
            family.result_relation.clone(),
            LookupRelationMetadata {
                logical_relation_id: format!("{}.result", family.logical_relation_id),
                scope_signature: result_scope,
                usage_kind: Some("enumerate".to_string()),
            },
        );

        for demand in &family.demand {
            out.insert(
                demand.relation.clone(),
                LookupRelationMetadata {
                    logical_relation_id: demand.logical_relation_id.clone(),
                    scope_signature: demand.scope_signature.clone(),
                    usage_kind: Some(demand.usage_kind.as_str().to_string()),
                },
            );
        }
    }

    out
}

/// Validate that the HE lookup-plan artifact satisfies the minimum
/// theory-gated contract required by the native MORK core backend.
pub fn validate_he_mork_backend_contract(artifact: &LookupPlanArtifact) -> Result<()> {
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        bail!("HE MORK backend contract requires dialect 'he', got '{}'", artifact.dialect);
    }

    let family = artifact
        .families
        .iter()
        .find(|f| f.family == "eqQuery" || f.logical_relation_id == "he.eq_query")
        .ok_or_else(|| anyhow!("HE MORK backend contract: missing eqQuery lookup family"))?;

    if !family.contracts.no_false_negatives {
        bail!("HE MORK backend contract: eqQuery family must guarantee no_false_negatives=true");
    }
    if !family.contracts.stratified_negation_safe {
        bail!(
            "HE MORK backend contract: eqQuery family must guarantee stratified_negation_safe=true"
        );
    }

    let has_negated_fallback = family.demand.iter().any(|d| {
        d.relation == "noEqQuery"
            && matches!(d.usage_kind, LookupUsageKind::NegatedExists)
            && d.negated_target.as_deref() == Some(family.has_relation.as_str())
    });
    if !has_negated_fallback {
        bail!(
            "HE MORK backend contract: missing noEqQuery negated_exists demand targeting '{}'",
            family.has_relation
        );
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        fnv1a64, relation_metadata_index, try_load_lookup_plan, validate_he_mork_backend_contract,
    };
    use crate::test_env::acquire_env_lock;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_artifact_dir(stem: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock should be after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        PathBuf::from(format!(".artifacts/test-runtime/{stem}_{pid}_{nanos}"))
    }

    #[test]
    fn fnv1a64_matches_lean_constants() {
        assert_eq!(fnv1a64(""), 14_695_981_039_346_656_037);
        assert_eq!(fnv1a64("abc"), 16_654_208_175_385_433_931);
    }

    #[test]
    fn try_load_lookup_plan_respects_env_dir_checksum_and_metadata() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("lookup_plan");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.lookup_plan.json");
        let checksum_path = dir.join("he.lookup_plan.checksum");
        let payload = r#"{
  "schema_version":2,
  "dialect":"he",
  "families":[{
    "family":"eqQuery",
    "logical_relation_id":"he.eq_query",
    "fact_relation":"spaceFact",
    "raw_relation":"eqQueryRaw",
    "has_relation":"eqQueryHas",
    "result_relation":"eqQueryResult",
    "query_arity":2,
    "payload_arity":1,
    "key_positions":[0,1],
    "demand":[
      {
        "relation":"noEqQuery",
        "logical_relation_id":"he.eq_query.fallback",
        "scope_signature":"b0+b1",
        "arity":2,
        "args":[{"position":0,"mode":"bound"},{"position":1,"mode":"bound"}],
        "usage_kind":"negated_exists",
        "negated_target":"eqQueryHas",
        "in_recursive_scc":false,
        "hot_path":true
      }
    ],
    "contracts":{"no_false_negatives":true,"exact_result":false,"stratified_negation_safe":true}
  }]
}"#;
        let checksum = fnv1a64(payload);
        fs::write(&json_path, format!("{payload}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum}\n")).expect("checksum should be writable");

        std::env::set_var("METTAIL_LOOKUP_PLAN_DIR", &dir);
        let loaded = try_load_lookup_plan("he")
            .expect("load should succeed")
            .expect("lookup plan should be found");
        assert_eq!(loaded.artifact.dialect, "he");

        let meta = relation_metadata_index(&loaded.artifact);
        let no_eq = meta
            .get("noEqQuery")
            .expect("metadata should include demand relation");
        assert_eq!(no_eq.logical_relation_id, "he.eq_query.fallback");
        assert_eq!(no_eq.scope_signature, "b0+b1");

        fs::write(&checksum_path, "0\n").expect("checksum should be writable");
        let err = try_load_lookup_plan("he").expect_err("mismatch should fail");
        assert!(err.to_string().contains("checksum mismatch"));

        std::env::remove_var("METTAIL_LOOKUP_PLAN_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn try_load_lookup_plan_rejects_unknown_fields_schema_mismatch_and_bad_negation_target() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("lookup_plan_bad_schema");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.lookup_plan.json");
        let checksum_path = dir.join("he.lookup_plan.checksum");

        let payload_unknown = r#"{
  "schema_version":2,
  "dialect":"he",
  "families":[],
  "extra":true
}"#;
        let checksum_unknown = fnv1a64(payload_unknown);
        fs::write(&json_path, format!("{payload_unknown}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_unknown}\n"))
            .expect("checksum should be writable");
        std::env::set_var("METTAIL_LOOKUP_PLAN_DIR", &dir);
        let err = try_load_lookup_plan("he").expect_err("unknown fields should fail");
        assert!(err.to_string().contains("invalid lookup plan json payload"));

        let payload_bad_schema = r#"{
  "schema_version":7,
  "dialect":"he",
  "families":[{
    "family":"eqQuery",
    "logical_relation_id":"he.eq_query",
    "fact_relation":"spaceFact",
    "raw_relation":"eqQueryRaw",
    "has_relation":"eqQueryHas",
    "result_relation":"eqQueryResult",
    "query_arity":2,
    "payload_arity":1,
    "key_positions":[0,1],
    "demand":[],
    "contracts":{"no_false_negatives":true,"exact_result":false,"stratified_negation_safe":true}
  }]
}"#;
        let checksum_bad_schema = fnv1a64(payload_bad_schema);
        fs::write(&json_path, format!("{payload_bad_schema}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_bad_schema}\n"))
            .expect("checksum should be writable");
        let err = try_load_lookup_plan("he").expect_err("schema mismatch should fail");
        assert!(err
            .to_string()
            .contains("unsupported lookup plan schema_version"));

        let payload_bad_negation = r#"{
  "schema_version":2,
  "dialect":"he",
  "families":[{
    "family":"eqQuery",
    "logical_relation_id":"he.eq_query",
    "fact_relation":"spaceFact",
    "raw_relation":"eqQueryRaw",
    "has_relation":"eqQueryHas",
    "result_relation":"eqQueryResult",
    "query_arity":2,
    "payload_arity":1,
    "key_positions":[0,1],
    "demand":[
      {
        "relation":"noEqQuery",
        "logical_relation_id":"he.eq_query.fallback",
        "scope_signature":"b0+b1",
        "arity":2,
        "args":[{"position":0,"mode":"bound"},{"position":1,"mode":"bound"}],
        "usage_kind":"negated_exists",
        "negated_target":null,
        "in_recursive_scc":false,
        "hot_path":true
      }
    ],
    "contracts":{"no_false_negatives":true,"exact_result":false,"stratified_negation_safe":true}
  }]
}"#;
        let checksum_bad_negation = fnv1a64(payload_bad_negation);
        fs::write(&json_path, format!("{payload_bad_negation}\n"))
            .expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_bad_negation}\n"))
            .expect("checksum should be writable");
        let err = try_load_lookup_plan("he").expect_err("missing negated target should fail");
        assert!(err.to_string().contains("missing negated_target"));

        std::env::remove_var("METTAIL_LOOKUP_PLAN_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn validate_he_mork_backend_contract_accepts_valid_plan_and_rejects_weak_contracts() {
        let ok_payload = r#"{
  "schema_version":2,
  "dialect":"he",
  "families":[{
    "family":"eqQuery",
    "logical_relation_id":"he.eq_query",
    "fact_relation":"spaceFact",
    "raw_relation":"eqQueryRaw",
    "has_relation":"eqQueryHas",
    "result_relation":"eqQueryResult",
    "query_arity":2,
    "payload_arity":1,
    "key_positions":[0,1],
    "demand":[
      {
        "relation":"noEqQuery",
        "logical_relation_id":"he.eq_query.fallback",
        "scope_signature":"b0+b1",
        "arity":2,
        "args":[{"position":0,"mode":"bound"},{"position":1,"mode":"bound"}],
        "usage_kind":"negated_exists",
        "negated_target":"eqQueryHas",
        "in_recursive_scc":false,
        "hot_path":true
      }
    ],
    "contracts":{"no_false_negatives":true,"exact_result":false,"stratified_negation_safe":true}
  }]
}"#;
        let ok: super::LookupPlanArtifact =
            serde_json::from_str(ok_payload).expect("valid payload should parse");
        validate_he_mork_backend_contract(&ok).expect("valid contract should pass");

        let bad_payload = ok_payload
            .replace("\"stratified_negation_safe\":true", "\"stratified_negation_safe\":false");
        let bad: super::LookupPlanArtifact =
            serde_json::from_str(&bad_payload).expect("bad payload should parse");
        let err = validate_he_mork_backend_contract(&bad).expect_err("weak contract must fail");
        assert!(err.to_string().contains("stratified_negation_safe=true"));
    }
}
