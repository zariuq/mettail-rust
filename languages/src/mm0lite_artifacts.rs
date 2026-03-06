use crate::artifact_contract::load_json_with_checksum;
pub use crate::artifact_contract::{
    parse_rule_ids_from_generated_language, LookupArtifact, LookupContracts, LookupDemand,
    LookupDemandArg, LookupFamily, RewriteIRArtifact, RewriteIRRule, TransitionArtifact,
    TransitionRule, TransitionSemKey, TransitionSource,
};
use std::path::{Path, PathBuf};

pub const MM0LITE_TRANSITION_SCHEMA_VERSION: u64 = 2;
pub const MM0LITE_LOOKUP_SCHEMA_VERSION: u64 = 2;
pub const MM0LITE_REWRITE_IR_SCHEMA_VERSION: u64 = 1;

pub fn mm0lite_artifact_dir() -> PathBuf {
    if let Ok(from_env) = std::env::var("METTAIL_MM0LITE_ARTIFACT_DIR") {
        return PathBuf::from(from_env);
    }
    for dir in candidate_mm0lite_artifact_dirs() {
        if has_mm0lite_core_artifacts(&dir) {
            return dir;
        }
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../lean-projects/mettapedia/artifacts/mm0lite")
}

pub fn mm0lite_generated_language_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/generated/mm0lite_language_working.rs")
}

fn candidate_mm0lite_artifact_dirs() -> Vec<PathBuf> {
    let mut dirs = vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/mettapedia/artifacts/mm0lite"),
        PathBuf::from("../../../lean-projects/mettapedia/artifacts/mm0lite"),
        PathBuf::from("../../lean-projects/mettapedia/artifacts/mm0lite"),
        PathBuf::from("../lean-projects/mettapedia/artifacts/mm0lite"),
    ];
    // Legacy bootstrap artifacts may be useful for isolated local development,
    // but must be explicitly opted in to avoid silent drift from Lean exports.
    if std::env::var("METTAIL_MM0LITE_ALLOW_BOOTSTRAP_ARTIFACTS")
        .map(|v| matches!(v.as_str(), "1" | "true" | "TRUE" | "yes" | "YES"))
        .unwrap_or(false)
    {
        dirs.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/mm0lite"));
        dirs.push(PathBuf::from("artifacts/mm0lite"));
    }
    dirs
}

fn has_mm0lite_core_artifacts(dir: &Path) -> bool {
    let required = [
        "mm0lite.transition_spec.json",
        "mm0lite.transition_spec.checksum",
        "mm0lite.lookup_plan.json",
        "mm0lite.lookup_plan.checksum",
        "mm0lite.rewrite_ir.json",
        "mm0lite.rewrite_ir.checksum",
    ];
    required.iter().all(|f| dir.join(f).exists())
}

pub fn load_mm0lite_transition_artifact(dir: &Path) -> Result<TransitionArtifact, String> {
    let json_path = dir.join("mm0lite.transition_spec.json");
    let checksum_path = dir.join("mm0lite.transition_spec.checksum");
    let artifact: TransitionArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "transition")?;
    if artifact.schema_version != MM0LITE_TRANSITION_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MM0Lite transition schema_version {} (expected {})",
            artifact.schema_version, MM0LITE_TRANSITION_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "mm0lite" {
        return Err(format!(
            "transition artifact dialect mismatch: expected mm0lite, got {}",
            artifact.dialect
        ));
    }
    Ok(artifact)
}

pub fn load_mm0lite_lookup_artifact(dir: &Path) -> Result<LookupArtifact, String> {
    let json_path = dir.join("mm0lite.lookup_plan.json");
    let checksum_path = dir.join("mm0lite.lookup_plan.checksum");
    let artifact: LookupArtifact = load_json_with_checksum(&json_path, &checksum_path, "lookup")?;
    if artifact.schema_version != MM0LITE_LOOKUP_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MM0Lite lookup schema_version {} (expected {})",
            artifact.schema_version, MM0LITE_LOOKUP_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "mm0lite" {
        return Err(format!(
            "lookup artifact dialect mismatch: expected mm0lite, got {}",
            artifact.dialect
        ));
    }
    Ok(artifact)
}

pub fn load_mm0lite_rewrite_ir_artifact(dir: &Path) -> Result<RewriteIRArtifact, String> {
    let json_path = dir.join("mm0lite.rewrite_ir.json");
    let checksum_path = dir.join("mm0lite.rewrite_ir.checksum");
    let artifact: RewriteIRArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "rewrite-ir")?;
    if artifact.schema_version != MM0LITE_REWRITE_IR_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MM0Lite rewrite-ir schema_version {} (expected {})",
            artifact.schema_version, MM0LITE_REWRITE_IR_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "mm0lite" {
        return Err(format!(
            "rewrite-ir artifact dialect mismatch: expected mm0lite, got {}",
            artifact.dialect
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!("rewrite-ir artifact {} has empty rules", json_path.display()));
    }
    Ok(artifact)
}
