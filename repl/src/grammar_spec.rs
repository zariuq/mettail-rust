use anyhow::{anyhow, Context, Result};
use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};

const EXPECTED_GRAMMAR_SPEC_SCHEMA_VERSION: u64 = 2;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct GrammarToken {
    pub name: String,
    pub pattern: String,
    pub is_regex: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct GrammarProduction {
    pub lhs: String,
    pub rhs: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct GrammarSpec {
    pub schema_version: u64,
    pub dialect: String,
    pub start_symbol: String,
    pub eval_prefix_token: String,
    pub line_comment_start: Option<String>,
    pub sexpr_open: String,
    pub sexpr_close: String,
    pub tokens: Vec<GrammarToken>,
    pub productions: Vec<GrammarProduction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedGrammarSpec {
    pub spec: GrammarSpec,
    pub grammar_spec_json_path: PathBuf,
    pub grammar_spec_checksum_path: PathBuf,
    pub tree_sitter_grammar_js_path: PathBuf,
}

fn fnv1a64(text: &str) -> u64 {
    const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV64_PRIME: u64 = 1_099_511_628_211;
    text.bytes()
        .fold(FNV64_OFFSET, |h, b| (h ^ (b as u64)).wrapping_mul(FNV64_PRIME))
}

fn candidate_grammar_dirs() -> Vec<PathBuf> {
    if let Ok(from_env) = std::env::var("METTAIL_GRAMMAR_SPEC_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    if let Ok(from_env) = std::env::var("METTAIL_SYNTAX_SPEC_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    let mut dirs = Vec::new();
    dirs.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/syntax"));
    dirs.push(PathBuf::from("artifacts/syntax"));
    dirs.push(PathBuf::from("../lean-projects/algorithms/artifacts/syntax"));
    dirs.push(PathBuf::from("../../lean-projects/algorithms/artifacts/syntax"));
    dirs.push(PathBuf::from("../../../lean-projects/algorithms/artifacts/syntax"));
    dirs.push(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../../lean-projects/algorithms/artifacts/syntax"),
    );
    dirs
}

fn grammar_spec_paths(base_dir: &Path, dialect_key: &str) -> (PathBuf, PathBuf, PathBuf) {
    let base = format!("{dialect_key}.grammar_spec");
    (
        base_dir.join(format!("{base}.json")),
        base_dir.join(format!("{base}.checksum")),
        base_dir.join(format!("{dialect_key}.tree_sitter_grammar.js")),
    )
}

fn load_from_paths(
    grammar_spec_json_path: &Path,
    grammar_spec_checksum_path: &Path,
    tree_sitter_grammar_js_path: &Path,
) -> Result<LoadedGrammarSpec> {
    let json_text_raw = fs::read_to_string(grammar_spec_json_path).with_context(|| {
        format!("failed reading grammar spec json {}", grammar_spec_json_path.display())
    })?;
    let checksum_text_raw = fs::read_to_string(grammar_spec_checksum_path).with_context(|| {
        format!("failed reading grammar spec checksum {}", grammar_spec_checksum_path.display())
    })?;
    let json_text = json_text_raw.trim();
    let grammar_js_raw = fs::read_to_string(tree_sitter_grammar_js_path).with_context(|| {
        format!(
            "failed reading tree-sitter grammar artifact {}",
            tree_sitter_grammar_js_path.display()
        )
    })?;
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().with_context(|| {
        format!(
            "invalid grammar spec checksum '{}' at {}",
            checksum_text,
            grammar_spec_checksum_path.display()
        )
    })?;
    // Lean `GrammarSpec.checksum` hashes both artifacts:
    //   renderJson ++ "\n---\n" ++ renderTreeSitterJs
    // Exported JSON has an extra trailing newline, so we trim JSON before hashing.
    let actual_checksum = fnv1a64(&format!("{json_text}\n---\n{grammar_js_raw}"));
    if actual_checksum != expected_checksum {
        return Err(anyhow!(
            "grammar spec checksum mismatch for {}: expected {}, got {}",
            grammar_spec_json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }
    let spec: GrammarSpec = serde_json::from_str(json_text).with_context(|| {
        format!("invalid grammar spec json payload at {}", grammar_spec_json_path.display())
    })?;
    if spec.schema_version != EXPECTED_GRAMMAR_SPEC_SCHEMA_VERSION {
        return Err(anyhow!(
            "unsupported grammar spec schema_version {} at {} (expected {})",
            spec.schema_version,
            grammar_spec_json_path.display(),
            EXPECTED_GRAMMAR_SPEC_SCHEMA_VERSION
        ));
    }
    Ok(LoadedGrammarSpec {
        spec,
        grammar_spec_json_path: grammar_spec_json_path.to_path_buf(),
        grammar_spec_checksum_path: grammar_spec_checksum_path.to_path_buf(),
        tree_sitter_grammar_js_path: tree_sitter_grammar_js_path.to_path_buf(),
    })
}

pub fn try_load_grammar_spec(dialect_key: &str) -> Result<Option<LoadedGrammarSpec>> {
    let mut first_error: Option<anyhow::Error> = None;
    for dir in candidate_grammar_dirs() {
        let (json_path, checksum_path, grammar_js_path) = grammar_spec_paths(&dir, dialect_key);
        if !json_path.exists() || !checksum_path.exists() || !grammar_js_path.exists() {
            continue;
        }
        match load_from_paths(&json_path, &checksum_path, &grammar_js_path) {
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

#[cfg(test)]
mod tests {
    use super::try_load_grammar_spec;
    use crate::test_env::acquire_env_lock;
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn fnv1a64(text: &str) -> u64 {
        const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
        const FNV64_PRIME: u64 = 1_099_511_628_211;
        text.bytes()
            .fold(FNV64_OFFSET, |h, b| (h ^ (b as u64)).wrapping_mul(FNV64_PRIME))
    }

    fn unique_artifact_dir(stem: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock should be after unix epoch")
            .as_nanos();
        let pid = std::process::id();
        PathBuf::from(format!(".artifacts/test-runtime/{stem}_{pid}_{nanos}"))
    }

    #[test]
    fn try_load_grammar_spec_respects_env_dir_and_checksum() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("grammar_spec");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.grammar_spec.json");
        let checksum_path = dir.join("he.grammar_spec.checksum");
        let grammar_js_path = dir.join("he.tree_sitter_grammar.js");
        let payload = r#"{
  "schema_version":2,
  "dialect":"HE",
  "start_symbol":"program",
  "eval_prefix_token":"!",
  "line_comment_start":null,
  "sexpr_open":"(",
  "sexpr_close":")",
  "tokens":[],
  "productions":[]
}"#;
        let grammar_js = "module.exports = grammar({name: 'metta_he', rules: { source_file: $ => repeat($._top), _top: $ => $.atom, atom: $ => $.symbol, symbol: $ => /[^\\s()\\\";]+/ }});\n";
        let checksum = fnv1a64(&format!("{payload}\n---\n{grammar_js}"));
        fs::write(&json_path, format!("{payload}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum}\n")).expect("checksum should be writable");
        fs::write(&grammar_js_path, grammar_js).expect("grammar js should be writable");

        std::env::set_var("METTAIL_GRAMMAR_SPEC_DIR", &dir);
        let loaded = try_load_grammar_spec("he")
            .expect("load should succeed")
            .expect("spec should be found");
        assert_eq!(loaded.spec.dialect, "HE");

        fs::write(&checksum_path, "0\n").expect("checksum should be writable");
        let err = try_load_grammar_spec("he").expect_err("mismatch should fail");
        assert!(err.to_string().contains("checksum mismatch"));

        std::env::remove_var("METTAIL_GRAMMAR_SPEC_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_file(&grammar_js_path);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn try_load_grammar_spec_rejects_unknown_fields_and_schema_mismatch() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("grammar_spec_bad_schema");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.grammar_spec.json");
        let checksum_path = dir.join("he.grammar_spec.checksum");
        let grammar_js_path = dir.join("he.tree_sitter_grammar.js");
        let payload_unknown = r#"{
  "schema_version":2,
  "dialect":"HE",
  "start_symbol":"program",
  "eval_prefix_token":"!",
  "line_comment_start":null,
  "sexpr_open":"(",
  "sexpr_close":")",
  "tokens":[],
  "productions":[],
  "extra":true
}"#;
        let grammar_js = "module.exports = grammar({name: 'metta_he', rules: { source_file: $ => repeat($._top), _top: $ => $.atom, atom: $ => $.symbol, symbol: $ => /[^\\s()\\\";]+/ }});\n";
        let checksum_unknown = fnv1a64(&format!("{payload_unknown}\n---\n{grammar_js}"));
        fs::write(&json_path, format!("{payload_unknown}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_unknown}\n"))
            .expect("checksum should be writable");
        fs::write(&grammar_js_path, grammar_js).expect("grammar js should be writable");
        std::env::set_var("METTAIL_GRAMMAR_SPEC_DIR", &dir);
        let err = try_load_grammar_spec("he").expect_err("unknown fields should fail");
        assert!(
            err.to_string()
                .contains("invalid grammar spec json payload"),
            "unexpected error: {err}"
        );

        let payload_schema =
            payload_unknown.replace("\"schema_version\":2", "\"schema_version\":3");
        let payload_schema = payload_schema.replace(",\n  \"extra\":true", "");
        let checksum_schema = fnv1a64(&format!("{payload_schema}\n---\n{grammar_js}"));
        fs::write(&json_path, format!("{payload_schema}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_schema}\n"))
            .expect("checksum should be writable");
        let err = try_load_grammar_spec("he").expect_err("schema mismatch should fail");
        assert!(
            err.to_string()
                .contains("unsupported grammar spec schema_version"),
            "unexpected error: {err}"
        );

        std::env::remove_var("METTAIL_GRAMMAR_SPEC_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_file(&grammar_js_path);
        let _ = fs::remove_dir_all(&dir);
    }
}
