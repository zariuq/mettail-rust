use anyhow::{anyhow, Context, Result};
use serde::Deserialize;
use std::fs;
use std::path::{Path, PathBuf};

const MIN_SYNTAX_SPEC_SCHEMA_VERSION: u64 = 2;
const MAX_SYNTAX_SPEC_SCHEMA_VERSION: u64 = 3;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LexerSpec {
    pub line_comment_start: Option<String>,
    pub supports_string_literals: bool,
    pub string_delimiter: String,
    pub escape_char: String,
    pub sexpr_open: String,
    pub sexpr_close: String,
    pub allow_hash_in_symbol: bool,
    pub reserve_hash_in_variable: bool,
    pub trim_ascii_whitespace: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct EvalPrefixPolicy {
    pub prefix: String,
    pub allow_whitespace_after_prefix: bool,
    pub allow_newline_after_prefix: bool,
    pub bang_prefixed_word_is_symbol: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CommandHead {
    pub head: String,
    pub command: String,
    pub arity_min: u64,
    pub arity_max: Option<u64>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SugarAlias {
    pub alias: String,
    pub canonical: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct EvalSpaceAlias {
    pub head: String,
    pub canonical_head: String,
    pub arity: u64,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct LoweringHeads {
    pub relation_fact_head: String,
    pub builtin_fact_head: String,
}

impl Default for LoweringHeads {
    fn default() -> Self {
        Self {
            relation_fact_head: "relation!".to_string(),
            builtin_fact_head: "builtin!".to_string(),
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DispatchPolicy {
    pub fallback_unknown_head_to_fact: bool,
    pub fallback_arity_mismatch_to_fact: bool,
    pub fallback_unsupported_command_to_fact: bool,
}

impl Default for DispatchPolicy {
    fn default() -> Self {
        Self {
            fallback_unknown_head_to_fact: true,
            fallback_arity_mismatch_to_fact: true,
            fallback_unsupported_command_to_fact: true,
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct ProgramPolicy {
    pub explicit_query_only: bool,
    pub allow_implicit_last_query: bool,
    pub default_space: String,
}

impl Default for ProgramPolicy {
    fn default() -> Self {
        Self {
            explicit_query_only: true,
            allow_implicit_last_query: false,
            default_space: "&self".to_string(),
        }
    }
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct SyntaxSpec {
    pub schema_version: u64,
    pub dialect: String,
    pub lexer: LexerSpec,
    pub eval_prefix: EvalPrefixPolicy,
    #[serde(default)]
    pub lowering_heads: LoweringHeads,
    #[serde(default)]
    pub dispatch_policy: DispatchPolicy,
    #[serde(default)]
    pub program_policy: ProgramPolicy,
    pub command_heads: Vec<CommandHead>,
    #[serde(default)]
    pub head_aliases: Vec<SugarAlias>,
    #[serde(default)]
    pub eval_space_aliases: Vec<EvalSpaceAlias>,
    #[serde(default)]
    pub predicate_special_heads: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedSyntaxSpec {
    pub spec: SyntaxSpec,
    pub json_path: PathBuf,
    pub checksum_path: PathBuf,
}

/// FNV-1a hash over Unicode codepoints (matching Lean's `checksumText`).
fn fnv1a64(text: &str) -> u64 {
    const FNV64_OFFSET: u64 = 14_695_981_039_346_656_037;
    const FNV64_PRIME: u64 = 1_099_511_628_211;
    text.chars()
        .fold(FNV64_OFFSET, |h, c| (h ^ (c as u64)).wrapping_mul(FNV64_PRIME))
}

fn candidate_syntax_dirs() -> Vec<PathBuf> {
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

fn syntax_spec_paths(base_dir: &Path, dialect_key: &str) -> (PathBuf, PathBuf) {
    let base = format!("{dialect_key}.syntax_spec");
    (base_dir.join(format!("{base}.json")), base_dir.join(format!("{base}.checksum")))
}

fn load_from_paths(json_path: &Path, checksum_path: &Path) -> Result<LoadedSyntaxSpec> {
    let json_text_raw = fs::read_to_string(json_path)
        .with_context(|| format!("failed reading syntax spec json {}", json_path.display()))?;
    let checksum_text_raw = fs::read_to_string(checksum_path).with_context(|| {
        format!("failed reading syntax spec checksum {}", checksum_path.display())
    })?;
    let json_text = json_text_raw.trim();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().with_context(|| {
        format!(
            "invalid syntax spec checksum '{}' at {}",
            checksum_text,
            checksum_path.display()
        )
    })?;
    let actual_checksum = fnv1a64(json_text);
    if actual_checksum != expected_checksum {
        return Err(anyhow!(
            "syntax spec checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }
    let spec: SyntaxSpec = serde_json::from_str(json_text)
        .with_context(|| format!("invalid syntax spec json payload at {}", json_path.display()))?;
    if spec.schema_version < MIN_SYNTAX_SPEC_SCHEMA_VERSION
        || spec.schema_version > MAX_SYNTAX_SPEC_SCHEMA_VERSION
    {
        return Err(anyhow!(
            "unsupported syntax spec schema_version {} at {} (expected {}-{})",
            spec.schema_version,
            json_path.display(),
            MIN_SYNTAX_SPEC_SCHEMA_VERSION,
            MAX_SYNTAX_SPEC_SCHEMA_VERSION
        ));
    }
    Ok(LoadedSyntaxSpec {
        spec,
        json_path: json_path.to_path_buf(),
        checksum_path: checksum_path.to_path_buf(),
    })
}

pub fn try_load_syntax_spec(dialect_key: &str) -> Result<Option<LoadedSyntaxSpec>> {
    let mut first_error: Option<anyhow::Error> = None;
    for dir in candidate_syntax_dirs() {
        let (json_path, checksum_path) = syntax_spec_paths(&dir, dialect_key);
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

// ═══════════════════════════════════════════════════════════════════════
// AtomEncodingSpec: surface S-expression ↔ core runtime term lowering
// ═══════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct OperatorAlias {
    pub surface_symbol: String,
    pub constructor_label: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum IntEncoding {
    #[serde(rename = "prefixed")]
    Prefixed { prefix: String, neg_marker: String },
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum StringEncoding {
    #[serde(rename = "prefixed")]
    Prefixed { prefix: String },
    #[serde(rename = "hex_prefixed")]
    HexPrefixed { prefix: String },
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct SymbolEscaping {
    pub safe_pattern: String,
    pub escape_prefix: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct SugarFormEntry {
    pub head: String,
    pub constructor_label: String,
    pub arity: u64,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct AtomEncodingSpec {
    pub symbol_wrapper: String,
    pub variable_wrapper: String,
    pub variable_wraps_name: bool,
    pub int_wrapper: String,
    pub string_wrapper: String,
    pub expr_cons: String,
    pub expr_nil: String,
    pub int_encoding: IntEncoding,
    pub string_encoding: StringEncoding,
    pub symbol_escaping: SymbolEscaping,
    pub operator_aliases: Vec<OperatorAlias>,
    #[serde(default)]
    pub type_keywords: Vec<OperatorAlias>,
    #[serde(default)]
    pub boolean_literals: Vec<OperatorAlias>,
    #[serde(default)]
    pub sugar_forms: Vec<SugarFormEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedAtomEncoding {
    pub spec: AtomEncodingSpec,
    pub json_path: PathBuf,
    pub checksum_path: PathBuf,
}

fn atom_encoding_paths(base_dir: &Path, dialect_key: &str) -> (PathBuf, PathBuf) {
    let base = format!("{dialect_key}.atom_encoding");
    (
        base_dir.join(format!("{base}.json")),
        base_dir.join(format!("{base}.checksum")),
    )
}

fn load_atom_encoding_from_paths(
    json_path: &Path,
    checksum_path: &Path,
) -> Result<LoadedAtomEncoding> {
    let json_text_raw = fs::read_to_string(json_path)
        .with_context(|| format!("failed reading atom encoding json {}", json_path.display()))?;
    let checksum_text_raw = fs::read_to_string(checksum_path).with_context(|| {
        format!(
            "failed reading atom encoding checksum {}",
            checksum_path.display()
        )
    })?;
    let json_text = json_text_raw.trim();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().with_context(|| {
        format!(
            "invalid atom encoding checksum '{}' at {}",
            checksum_text,
            checksum_path.display()
        )
    })?;
    let actual_checksum = fnv1a64(json_text);
    if actual_checksum != expected_checksum {
        return Err(anyhow!(
            "atom encoding checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }
    let spec: AtomEncodingSpec = serde_json::from_str(json_text).with_context(|| {
        format!(
            "invalid atom encoding json payload at {}",
            json_path.display()
        )
    })?;
    Ok(LoadedAtomEncoding {
        spec,
        json_path: json_path.to_path_buf(),
        checksum_path: checksum_path.to_path_buf(),
    })
}

pub fn try_load_atom_encoding(dialect_key: &str) -> Result<Option<LoadedAtomEncoding>> {
    let mut first_error: Option<anyhow::Error> = None;
    for dir in candidate_syntax_dirs() {
        let (json_path, checksum_path) = atom_encoding_paths(&dir, dialect_key);
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_atom_encoding_from_paths(&json_path, &checksum_path) {
            Ok(loaded) => return Ok(Some(loaded)),
            Err(e) => {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => Ok(None),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// DisplayProfile: internal runtime state → human-readable output
// ═══════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum DisplaySegment {
    #[serde(rename = "lit")]
    Lit { text: String },
    #[serde(rename = "param")]
    Param { name: String },
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct DisplayEntry {
    pub constructor_label: String,
    pub segments: Vec<DisplaySegment>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct DisplayProfile {
    pub name: String,
    pub entries: Vec<DisplayEntry>,
    #[serde(default)]
    pub raw_fallback: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoadedDisplayProfile {
    pub profile: DisplayProfile,
    pub json_path: PathBuf,
    pub checksum_path: PathBuf,
}

fn display_profile_paths(base_dir: &Path, dialect_key: &str) -> (PathBuf, PathBuf) {
    let base = format!("{dialect_key}.display_profile");
    (
        base_dir.join(format!("{base}.json")),
        base_dir.join(format!("{base}.checksum")),
    )
}

fn load_display_profile_from_paths(
    json_path: &Path,
    checksum_path: &Path,
) -> Result<LoadedDisplayProfile> {
    let json_text_raw = fs::read_to_string(json_path).with_context(|| {
        format!(
            "failed reading display profile json {}",
            json_path.display()
        )
    })?;
    let checksum_text_raw = fs::read_to_string(checksum_path).with_context(|| {
        format!(
            "failed reading display profile checksum {}",
            checksum_path.display()
        )
    })?;
    let json_text = json_text_raw.trim();
    let checksum_text = checksum_text_raw.trim();
    let expected_checksum: u64 = checksum_text.parse().with_context(|| {
        format!(
            "invalid display profile checksum '{}' at {}",
            checksum_text,
            checksum_path.display()
        )
    })?;
    let actual_checksum = fnv1a64(json_text);
    if actual_checksum != expected_checksum {
        return Err(anyhow!(
            "display profile checksum mismatch for {}: expected {}, got {}",
            json_path.display(),
            expected_checksum,
            actual_checksum
        ));
    }
    let profile: DisplayProfile = serde_json::from_str(json_text).with_context(|| {
        format!(
            "invalid display profile json payload at {}",
            json_path.display()
        )
    })?;
    Ok(LoadedDisplayProfile {
        profile,
        json_path: json_path.to_path_buf(),
        checksum_path: checksum_path.to_path_buf(),
    })
}

pub fn try_load_display_profile(dialect_key: &str) -> Result<Option<LoadedDisplayProfile>> {
    let mut first_error: Option<anyhow::Error> = None;
    for dir in candidate_syntax_dirs() {
        let (json_path, checksum_path) = display_profile_paths(&dir, dialect_key);
        if !json_path.exists() || !checksum_path.exists() {
            continue;
        }
        match load_display_profile_from_paths(&json_path, &checksum_path) {
            Ok(loaded) => return Ok(Some(loaded)),
            Err(e) => {
                if first_error.is_none() {
                    first_error = Some(e);
                }
            }
        }
    }
    match first_error {
        Some(err) => Err(err),
        None => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::{fnv1a64, try_load_atom_encoding, try_load_display_profile, try_load_syntax_spec};
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
    fn try_load_syntax_spec_respects_env_dir_and_checksum() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("syntax_spec");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.syntax_spec.json");
        let checksum_path = dir.join("he.syntax_spec.checksum");
        let payload = r#"{
  "schema_version":2,
  "dialect":"HE",
  "lexer":{
    "line_comment_start":";",
    "supports_string_literals":true,
    "string_delimiter":"\"",
    "escape_char":"\\",
    "sexpr_open":"(",
    "sexpr_close":")",
    "allow_hash_in_symbol":true,
    "reserve_hash_in_variable":true,
    "trim_ascii_whitespace":true
  },
  "eval_prefix":{
    "prefix":"!",
    "allow_whitespace_after_prefix":true,
    "allow_newline_after_prefix":true,
    "bang_prefixed_word_is_symbol":true
  },
  "command_heads":[]
}"#;
        let checksum = fnv1a64(payload);
        fs::write(&json_path, format!("{payload}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum}\n")).expect("checksum should be writable");

        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &dir);
        let loaded = try_load_syntax_spec("he")
            .expect("load should succeed")
            .expect("spec should be found");
        assert_eq!(loaded.spec.dialect, "HE");
        assert!(loaded.spec.eval_prefix.bang_prefixed_word_is_symbol);

        fs::write(&checksum_path, "0\n").expect("checksum should be writable");
        let err = try_load_syntax_spec("he").expect_err("mismatch should fail");
        assert!(err.to_string().contains("checksum mismatch"));

        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn try_load_syntax_spec_rejects_unknown_fields_and_schema_mismatch() {
        let _guard = acquire_env_lock();
        let dir = unique_artifact_dir("syntax_spec_bad_schema");
        fs::create_dir_all(&dir).expect("artifact dir should be creatable");
        let json_path = dir.join("he.syntax_spec.json");
        let checksum_path = dir.join("he.syntax_spec.checksum");
        let payload_unknown = r#"{
  "schema_version":2,
  "dialect":"HE",
  "lexer":{
    "line_comment_start":";",
    "supports_string_literals":true,
    "string_delimiter":"\"",
    "escape_char":"\\",
    "sexpr_open":"(",
    "sexpr_close":")",
    "allow_hash_in_symbol":true,
    "reserve_hash_in_variable":true,
    "trim_ascii_whitespace":true
  },
  "eval_prefix":{
    "prefix":"!",
    "allow_whitespace_after_prefix":true,
    "allow_newline_after_prefix":true,
    "bang_prefixed_word_is_symbol":true
  },
  "command_heads":[],
  "unknown_field":true
}"#;
        let checksum_unknown = fnv1a64(payload_unknown);
        fs::write(&json_path, format!("{payload_unknown}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_unknown}\n"))
            .expect("checksum should be writable");
        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &dir);
        let err = try_load_syntax_spec("he").expect_err("unknown fields should fail");
        assert!(
            err.to_string().contains("invalid syntax spec json payload"),
            "unexpected error: {err}"
        );

        let payload_schema =
            payload_unknown.replace("\"schema_version\":2", "\"schema_version\":99");
        let payload_schema = payload_schema.replace(",\n  \"unknown_field\":true", "");
        let checksum_schema = fnv1a64(&payload_schema);
        fs::write(&json_path, format!("{payload_schema}\n")).expect("json should be writable");
        fs::write(&checksum_path, format!("{checksum_schema}\n"))
            .expect("checksum should be writable");
        let err = try_load_syntax_spec("he").expect_err("schema mismatch should fail");
        assert!(
            err.to_string()
                .contains("unsupported syntax spec schema_version"),
            "unexpected error: {err}"
        );

        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
        let _ = fs::remove_file(&json_path);
        let _ = fs::remove_file(&checksum_path);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn try_load_atom_encoding_from_bundled_artifact() {
        let _guard = acquire_env_lock();
        let artifact_dir =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/syntax");
        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &artifact_dir);
        let loaded = try_load_atom_encoding("he")
            .expect("load should succeed")
            .expect("he atom encoding should be found");
        assert_eq!(loaded.spec.symbol_wrapper, "SymAtom");
        assert_eq!(loaded.spec.variable_wrapper, "VarAtom");
        assert!(loaded.spec.variable_wraps_name);
        assert_eq!(loaded.spec.expr_cons, "ExprCons");
        assert_eq!(loaded.spec.expr_nil, "ExprNil");
        assert!(!loaded.spec.operator_aliases.is_empty());
        assert!(!loaded.spec.type_keywords.is_empty());
        assert!(!loaded.spec.boolean_literals.is_empty());
        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
    }

    #[test]
    fn try_load_display_profile_from_bundled_artifact() {
        let _guard = acquire_env_lock();
        let artifact_dir =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("artifacts/syntax");
        std::env::set_var("METTAIL_SYNTAX_SPEC_DIR", &artifact_dir);
        let loaded = try_load_display_profile("he")
            .expect("load should succeed")
            .expect("he display profile should be found");
        assert_eq!(loaded.profile.name, "surface");
        assert!(!loaded.profile.entries.is_empty());
        std::env::remove_var("METTAIL_SYNTAX_SPEC_DIR");
    }
}
