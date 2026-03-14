use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn candidate_grammar_dirs(manifest_dir: &Path) -> Vec<PathBuf> {
    if let Ok(from_env) = env::var("METTAIL_GRAMMAR_SPEC_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    if let Ok(from_env) = env::var("METTAIL_SYNTAX_SPEC_DIR") {
        return vec![PathBuf::from(from_env)];
    }
    vec![
        manifest_dir.join("artifacts/syntax"),
        manifest_dir.join("../lean-projects/algorithms/artifacts/syntax"),
        manifest_dir.join("../../lean-projects/algorithms/artifacts/syntax"),
        manifest_dir.join("../../../lean-projects/algorithms/artifacts/syntax"),
    ]
}

fn find_grammar_js(manifest_dir: &Path, dialect: &str) -> Result<PathBuf, String> {
    let filename = format!("{dialect}.tree_sitter_grammar.js");
    for dir in candidate_grammar_dirs(manifest_dir) {
        let path = dir.join(&filename);
        if path.exists() {
            return Ok(path);
        }
    }
    Err(format!(
        "missing Lean-generated grammar artifact '{}'; set METTAIL_GRAMMAR_SPEC_DIR or regenerate via lean export",
        filename
    ))
}

fn tree_sitter_bin() -> String {
    env::var("METTAIL_TREE_SITTER_BIN").unwrap_or_else(|_| "tree-sitter".to_string())
}

fn generate_and_compile_dialect(
    manifest_dir: &Path,
    out_dir: &Path,
    dialect: &str,
) -> Result<(), String> {
    let grammar_js = find_grammar_js(manifest_dir, dialect)?;
    println!("cargo:rerun-if-changed={}", grammar_js.display());

    let dialect_out = out_dir.join("tree_sitter").join(dialect);
    fs::create_dir_all(&dialect_out).map_err(|e| {
        format!("failed creating tree-sitter build dir {}: {e}", dialect_out.display())
    })?;

    let grammar_out = dialect_out.join("grammar.js");
    let grammar_src = fs::read(&grammar_js)
        .map_err(|e| format!("failed reading {}: {e}", grammar_js.display()))?;
    fs::write(&grammar_out, &grammar_src)
        .map_err(|e| format!("failed writing {}: {e}", grammar_out.display()))?;

    let output = Command::new(tree_sitter_bin())
        .current_dir(&dialect_out)
        .arg("generate")
        .output()
        .map_err(|e| format!("failed to run tree-sitter generate for dialect '{dialect}': {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
        return Err(format!(
            "tree-sitter generate failed for dialect '{dialect}' in {}: {}{}{}",
            dialect_out.display(),
            stderr,
            if !stderr.is_empty() && !stdout.is_empty() {
                " | "
            } else {
                ""
            },
            stdout
        ));
    }

    let src_dir = dialect_out.join("src");
    let parser_c = src_dir.join("parser.c");
    if !parser_c.exists() {
        return Err(format!(
            "tree-sitter parser generation did not produce {}",
            parser_c.display()
        ));
    }

    let mut cc_build = cc::Build::new();
    cc_build
        .include(&src_dir)
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs")
        .file(&parser_c);
    let scanner_c = src_dir.join("scanner.c");
    if scanner_c.exists() {
        cc_build.file(scanner_c);
    }
    cc_build.compile(&format!("tree-sitter-metta-{dialect}"));

    Ok(())
}

fn main() {
    println!("cargo:rerun-if-env-changed=METTAIL_GRAMMAR_SPEC_DIR");
    println!("cargo:rerun-if-env-changed=METTAIL_SYNTAX_SPEC_DIR");
    println!("cargo:rerun-if-env-changed=METTAIL_TREE_SITTER_BIN");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));

    for dialect in ["he", "petta"] {
        if let Err(e) = generate_and_compile_dialect(&manifest_dir, &out_dir, dialect) {
            panic!("{e}");
        }
    }
}
