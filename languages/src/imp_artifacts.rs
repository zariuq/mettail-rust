use crate::artifact_contract::load_json_with_checksum;
pub use crate::artifact_contract::{
    parse_rule_ids_from_generated_language, LookupArtifact, RewriteIRArtifact, TransitionArtifact,
};
use std::path::{Path, PathBuf};

pub const IMP_TRANSITION_SCHEMA_VERSION: u64 = 2;
pub const IMP_LOOKUP_SCHEMA_VERSION: u64 = 2;
pub const IMP_REWRITE_IR_SCHEMA_VERSION: u64 = 1;

pub fn imp_artifact_dir() -> PathBuf {
    if let Ok(from_env) = std::env::var("METTAIL_IMP_ARTIFACT_DIR") {
        return PathBuf::from(from_env);
    }
    for dir in candidate_imp_artifact_dirs() {
        if has_imp_core_artifacts(&dir) {
            return dir;
        }
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../lean-projects/mettapedia/artifacts/imp")
}

pub fn imp_generated_language_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/generated/imp_language_working.rs")
}

fn candidate_imp_artifact_dirs() -> Vec<PathBuf> {
    vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../lean-projects/mettapedia/artifacts/imp"),
        PathBuf::from("../../../lean-projects/mettapedia/artifacts/imp"),
        PathBuf::from("../../lean-projects/mettapedia/artifacts/imp"),
        PathBuf::from("../lean-projects/mettapedia/artifacts/imp"),
    ]
}

fn has_imp_core_artifacts(dir: &Path) -> bool {
    let required = [
        "imp.transition_spec.json",
        "imp.transition_spec.checksum",
        "imp.lookup_plan.json",
        "imp.lookup_plan.checksum",
        "imp.rewrite_ir.json",
        "imp.rewrite_ir.checksum",
    ];
    required.iter().all(|f| dir.join(f).exists())
}

pub fn load_imp_transition_artifact(dir: &Path) -> Result<TransitionArtifact, String> {
    let json_path = dir.join("imp.transition_spec.json");
    let checksum_path = dir.join("imp.transition_spec.checksum");
    let artifact: TransitionArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "transition")?;
    if artifact.schema_version != IMP_TRANSITION_SCHEMA_VERSION {
        return Err(format!(
            "unsupported IMP transition schema_version {} (expected {})",
            artifact.schema_version, IMP_TRANSITION_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "imp" {
        return Err(format!(
            "transition artifact dialect mismatch: expected imp, got {}",
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

pub fn load_imp_lookup_artifact(dir: &Path) -> Result<LookupArtifact, String> {
    let json_path = dir.join("imp.lookup_plan.json");
    let checksum_path = dir.join("imp.lookup_plan.checksum");
    let artifact: LookupArtifact = load_json_with_checksum(&json_path, &checksum_path, "lookup")?;
    if artifact.schema_version != IMP_LOOKUP_SCHEMA_VERSION {
        return Err(format!(
            "unsupported IMP lookup schema_version {} (expected {})",
            artifact.schema_version, IMP_LOOKUP_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "imp" {
        return Err(format!(
            "lookup artifact dialect mismatch: expected imp, got {}",
            artifact.dialect
        ));
    }
    Ok(artifact)
}

pub fn load_imp_rewrite_ir_artifact(dir: &Path) -> Result<RewriteIRArtifact, String> {
    let json_path = dir.join("imp.rewrite_ir.json");
    let checksum_path = dir.join("imp.rewrite_ir.checksum");
    let artifact: RewriteIRArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "rewrite-ir")?;
    if artifact.schema_version != IMP_REWRITE_IR_SCHEMA_VERSION {
        return Err(format!(
            "unsupported IMP rewrite-ir schema_version {} (expected {})",
            artifact.schema_version, IMP_REWRITE_IR_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "imp" {
        return Err(format!(
            "rewrite-ir artifact dialect mismatch: expected imp, got {}",
            artifact.dialect
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!("rewrite-ir artifact {} has empty rules", json_path.display()));
    }
    Ok(artifact)
}
