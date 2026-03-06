use crate::artifact_contract::load_json_with_checksum;
pub use crate::artifact_contract::{
    parse_rule_ids_from_generated_language, LookupArtifact, RewriteIRArtifact, TransitionArtifact,
};
use std::path::{Path, PathBuf};

pub const MINSKYLITE_TRANSITION_SCHEMA_VERSION: u64 = 2;
pub const MINSKYLITE_LOOKUP_SCHEMA_VERSION: u64 = 2;
pub const MINSKYLITE_REWRITE_IR_SCHEMA_VERSION: u64 = 1;

pub fn minskylite_artifact_dir() -> PathBuf {
    if let Ok(from_env) = std::env::var("METTAIL_MINSKYLITE_ARTIFACT_DIR") {
        return PathBuf::from(from_env);
    }
    for dir in candidate_minskylite_artifact_dirs() {
        if has_minskylite_core_artifacts(&dir) {
            return dir;
        }
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../lean-projects/mettapedia/artifacts/minskylite")
}

pub fn minskylite_generated_language_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/generated/minskylite_language_working.rs")
}

fn candidate_minskylite_artifact_dirs() -> Vec<PathBuf> {
    vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/mettapedia/artifacts/minskylite"),
        PathBuf::from("../../../lean-projects/mettapedia/artifacts/minskylite"),
        PathBuf::from("../../lean-projects/mettapedia/artifacts/minskylite"),
        PathBuf::from("../lean-projects/mettapedia/artifacts/minskylite"),
    ]
}

fn has_minskylite_core_artifacts(dir: &Path) -> bool {
    let required = [
        "minskylite.transition_spec.json",
        "minskylite.transition_spec.checksum",
        "minskylite.lookup_plan.json",
        "minskylite.lookup_plan.checksum",
        "minskylite.rewrite_ir.json",
        "minskylite.rewrite_ir.checksum",
    ];
    required.iter().all(|f| dir.join(f).exists())
}

pub fn load_minskylite_transition_artifact(dir: &Path) -> Result<TransitionArtifact, String> {
    let json_path = dir.join("minskylite.transition_spec.json");
    let checksum_path = dir.join("minskylite.transition_spec.checksum");
    let artifact: TransitionArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "transition")?;
    if artifact.schema_version != MINSKYLITE_TRANSITION_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MinskyLite transition schema_version {} (expected {})",
            artifact.schema_version, MINSKYLITE_TRANSITION_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "minskylite" {
        return Err(format!(
            "transition artifact dialect mismatch: expected minskylite, got {}",
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

pub fn load_minskylite_lookup_artifact(dir: &Path) -> Result<LookupArtifact, String> {
    let json_path = dir.join("minskylite.lookup_plan.json");
    let checksum_path = dir.join("minskylite.lookup_plan.checksum");
    let artifact: LookupArtifact = load_json_with_checksum(&json_path, &checksum_path, "lookup")?;
    if artifact.schema_version != MINSKYLITE_LOOKUP_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MinskyLite lookup schema_version {} (expected {})",
            artifact.schema_version, MINSKYLITE_LOOKUP_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "minskylite" {
        return Err(format!(
            "lookup artifact dialect mismatch: expected minskylite, got {}",
            artifact.dialect
        ));
    }
    Ok(artifact)
}

pub fn load_minskylite_rewrite_ir_artifact(dir: &Path) -> Result<RewriteIRArtifact, String> {
    let json_path = dir.join("minskylite.rewrite_ir.json");
    let checksum_path = dir.join("minskylite.rewrite_ir.checksum");
    let artifact: RewriteIRArtifact =
        load_json_with_checksum(&json_path, &checksum_path, "rewrite-ir")?;
    if artifact.schema_version != MINSKYLITE_REWRITE_IR_SCHEMA_VERSION {
        return Err(format!(
            "unsupported MinskyLite rewrite-ir schema_version {} (expected {})",
            artifact.schema_version, MINSKYLITE_REWRITE_IR_SCHEMA_VERSION
        ));
    }
    if artifact.dialect != "minskylite" {
        return Err(format!(
            "rewrite-ir artifact dialect mismatch: expected minskylite, got {}",
            artifact.dialect
        ));
    }
    if artifact.rules.is_empty() {
        return Err(format!("rewrite-ir artifact {} has empty rules", json_path.display()));
    }
    Ok(artifact)
}
