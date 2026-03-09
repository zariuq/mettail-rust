use crate::artifact_contract::load_json_with_checksum;
pub use crate::artifact_contract::{
    index_rewrite_ir_v2_rules_by_id,
    parse_rule_ids_from_generated_language, LookupArtifact, LookupContracts, LookupDemand,
    LookupDemandArg, LookupFamily, RewriteIRArtifact, RewriteIRRule, RewriteIRV2Artifact,
    RewriteIRV2Rule, TransitionArtifact, TransitionRule, TransitionSemKey, TransitionSource,
};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub const METTAHE_TRANSITION_SCHEMA_VERSION: u64 = 2;
pub const METTAHE_LOOKUP_SCHEMA_VERSION: u64 = 2;
pub const METTAHE_REWRITE_IR_SCHEMA_VERSION: u64 = 2;
pub const METTAHE_REWRITE_IR_V2_DRAFT_SCHEMA_VERSION: u64 = 1;

pub fn mettahe_generated_language_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/generated/mettahe_language_working.rs")
}

fn candidate_mettahe_transition_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Ok(from_env) = std::env::var("METTAIL_METTAHE_ARTIFACT_DIR") {
        dirs.push(PathBuf::from(from_env));
    }
    if let Ok(from_env) = std::env::var("METTAIL_TRANSITION_SPEC_DIR") {
        dirs.push(PathBuf::from(from_env));
    }
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

fn candidate_mettahe_lookup_dirs() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Ok(from_env) = std::env::var("METTAIL_METTAHE_LOOKUP_ARTIFACT_DIR") {
        dirs.push(PathBuf::from(from_env));
    }
    if let Ok(from_env) = std::env::var("METTAIL_LOOKUP_PLAN_DIR") {
        dirs.push(PathBuf::from(from_env));
    }
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

fn load_he_transition_from_dir(dir: &Path) -> Result<TransitionArtifact, String> {
    let json_path = dir.join("he.transition_spec.json");
    let checksum_path = dir.join("he.transition_spec.checksum");
    let artifact: TransitionArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "transition")?;
    if artifact.schema_version != METTAHE_TRANSITION_SCHEMA_VERSION {
        return Err(format!(
            "unsupported HE transition schema_version {} (expected {})",
            artifact.schema_version, METTAHE_TRANSITION_SCHEMA_VERSION
        ));
    }
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        return Err(format!(
            "transition artifact dialect mismatch: expected he, got {}",
            artifact.dialect
        ));
    }
    if artifact.sources.is_empty() || artifact.rules.is_empty() {
        return Err(format!(
            "transition artifact {} must have non-empty sources and rules",
            json_path.display()
        ));
    }
    Ok(artifact)
}

fn load_he_lookup_from_dir(dir: &Path) -> Result<LookupArtifact, String> {
    let json_path = dir.join("he.lookup_plan.json");
    let checksum_path = dir.join("he.lookup_plan.checksum");
    let artifact: LookupArtifact = load_json_with_checksum(&json_path, &checksum_path, "lookup")?;
    if artifact.schema_version != METTAHE_LOOKUP_SCHEMA_VERSION {
        return Err(format!(
            "unsupported HE lookup schema_version {} (expected {})",
            artifact.schema_version, METTAHE_LOOKUP_SCHEMA_VERSION
        ));
    }
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        return Err(format!(
            "lookup artifact dialect mismatch: expected he, got {}",
            artifact.dialect
        ));
    }
    if artifact.families.is_empty() {
        return Err(format!("lookup artifact {} has empty families", json_path.display()));
    }
    Ok(artifact)
}

fn load_he_rewrite_ir_from_dir(dir: &Path) -> Result<RewriteIRArtifact, String> {
    let json_path = dir.join("he.rewrite_ir.json");
    let checksum_path = dir.join("he.rewrite_ir.checksum");
    let artifact: RewriteIRArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "rewrite-ir")?;
    if artifact.schema_version != METTAHE_REWRITE_IR_SCHEMA_VERSION {
        return Err(format!(
            "unsupported HE rewrite-ir schema_version {} (expected {})",
            artifact.schema_version, METTAHE_REWRITE_IR_SCHEMA_VERSION
        ));
    }
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        return Err(format!(
            "rewrite-ir artifact dialect mismatch: expected he, got {}",
            artifact.dialect
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!("rewrite-ir artifact {} has empty rules", json_path.display()));
    }
    Ok(artifact)
}

fn load_he_rewrite_ir_v2_draft_from_dir(dir: &Path) -> Result<RewriteIRV2Artifact, String> {
    let json_path = dir.join("he.rewrite_ir_v2_draft.json");
    let checksum_path = dir.join("he.rewrite_ir_v2_draft.checksum");
    let artifact: RewriteIRV2Artifact =
        load_json_with_checksum(&json_path, &checksum_path, "rewrite-ir-v2-draft")?;
    if artifact.schema_version != METTAHE_REWRITE_IR_V2_DRAFT_SCHEMA_VERSION {
        return Err(format!(
            "unsupported HE rewrite-ir-v2-draft schema_version {} (expected {})",
            artifact.schema_version, METTAHE_REWRITE_IR_V2_DRAFT_SCHEMA_VERSION
        ));
    }
    if !artifact.dialect.eq_ignore_ascii_case("he") {
        return Err(format!(
            "rewrite-ir-v2-draft artifact dialect mismatch: expected he, got {}",
            artifact.dialect
        ));
    }
    if artifact.artifact_label != "rewrite_ir_v2_draft_sidecar" {
        return Err(format!(
            "rewrite-ir-v2-draft artifact label mismatch: expected rewrite_ir_v2_draft_sidecar, got {}",
            artifact.artifact_label
        ));
    }
    if artifact.base_rewrite_ir_schema_version != METTAHE_REWRITE_IR_SCHEMA_VERSION {
        return Err(format!(
            "rewrite-ir-v2-draft base schema mismatch: expected {}, got {}",
            METTAHE_REWRITE_IR_SCHEMA_VERSION, artifact.base_rewrite_ir_schema_version
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!(
            "rewrite-ir-v2-draft artifact {} has empty rules",
            json_path.display()
        ));
    }
    Ok(artifact)
}

pub fn load_mettahe_transition_artifact() -> Result<TransitionArtifact, String> {
    let mut first_error: Option<String> = None;
    for dir in candidate_mettahe_transition_dirs() {
        let json_path = dir.join("he.transition_spec.json");
        let checksum_path = dir.join("he.transition_spec.checksum");
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_he_transition_from_dir(&dir) {
            Ok(artifact) => return Ok(artifact),
            Err(err) => {
                if first_error.is_none() {
                    first_error = Some(err);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => {
            Err("missing HE transition artifact: expected he.transition_spec.json/checksum"
                .to_string())
        },
    }
}

pub fn load_mettahe_lookup_artifact() -> Result<LookupArtifact, String> {
    let mut first_error: Option<String> = None;
    for dir in candidate_mettahe_lookup_dirs() {
        let json_path = dir.join("he.lookup_plan.json");
        let checksum_path = dir.join("he.lookup_plan.checksum");
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_he_lookup_from_dir(&dir) {
            Ok(artifact) => return Ok(artifact),
            Err(err) => {
                if first_error.is_none() {
                    first_error = Some(err);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => {
            Err("missing HE lookup artifact: expected he.lookup_plan.json/checksum".to_string())
        },
    }
}

pub fn load_mettahe_rewrite_ir_artifact() -> Result<RewriteIRArtifact, String> {
    let mut first_error: Option<String> = None;
    for dir in candidate_mettahe_transition_dirs() {
        let json_path = dir.join("he.rewrite_ir.json");
        let checksum_path = dir.join("he.rewrite_ir.checksum");
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_he_rewrite_ir_from_dir(&dir) {
            Ok(artifact) => return Ok(artifact),
            Err(err) => {
                if first_error.is_none() {
                    first_error = Some(err);
                }
            },
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => {
            Err("missing HE rewrite-ir artifact: expected he.rewrite_ir.json/checksum".to_string())
        },
    }
}

pub fn load_optional_mettahe_rewrite_ir_v2_draft_artifact(
) -> Result<Option<RewriteIRV2Artifact>, String> {
    let mut first_error: Option<String> = None;
    for dir in candidate_mettahe_transition_dirs() {
        let json_path = dir.join("he.rewrite_ir_v2_draft.json");
        let checksum_path = dir.join("he.rewrite_ir_v2_draft.checksum");
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_he_rewrite_ir_v2_draft_from_dir(&dir) {
            Ok(artifact) => return Ok(Some(artifact)),
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

pub fn load_optional_mettahe_rewrite_ir_v2_draft_index(
) -> Result<Option<BTreeMap<String, RewriteIRV2Rule>>, String> {
    match load_optional_mettahe_rewrite_ir_v2_draft_artifact()? {
        Some(artifact) => index_rewrite_ir_v2_rules_by_id(&artifact).map(Some),
        None => Ok(None),
    }
}
