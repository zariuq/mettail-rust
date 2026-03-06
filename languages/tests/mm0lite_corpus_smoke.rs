use mettail_languages::mm0lite_from_lean::{
    parse_mm0_theorem_facts, run_mm0lite_mork_backend, with_mm0_theorem_facts, MM0LiteLanguage,
};
use mettail_runtime::Language;

#[derive(Debug, Clone)]
struct Case {
    case_id: String,
    db_file: String,
    state_file: String,
    expect_mettail_exit: bool,
    expect_mettail_verified: bool,
}

fn fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("mm0lite")
}

fn load_cases() -> Vec<Case> {
    let csv_path = fixture_dir().join("cases.csv");
    let text = std::fs::read_to_string(&csv_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", csv_path.display()));
    let mut out = Vec::new();
    for (line_no, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with("case_id,") {
            continue;
        }
        let cols = line.split(',').map(|s| s.trim()).collect::<Vec<_>>();
        assert!(
            cols.len() >= 6,
            "invalid case csv at line {}: expected >= 6 columns, got {}",
            line_no + 1,
            cols.len()
        );
        out.push(Case {
            case_id: cols[0].to_string(),
            db_file: cols[1].to_string(),
            state_file: cols[2].to_string(),
            expect_mettail_exit: cols[3] == "0",
            expect_mettail_verified: cols[4] == "1",
        });
    }
    out
}

fn eval_case(case: &Case) -> Result<bool, String> {
    let db_src = std::fs::read_to_string(fixture_dir().join(&case.db_file))
        .map_err(|e| format!("db read failed for {}: {e}", case.db_file))?;
    let facts = parse_mm0_theorem_facts(&db_src)?;
    let state_src = std::fs::read_to_string(fixture_dir().join(&case.state_file))
        .map_err(|e| format!("state read failed for {}: {e}", case.state_file))?;
    let normalized_state = state_src
        .lines()
        .map(|line| line.split("--").next().unwrap_or_default().trim())
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    if normalized_state.is_empty() {
        return Err(format!("state file '{}' was empty", case.state_file));
    }
    mettail_runtime::clear_var_cache();
    let lang = MM0LiteLanguage;
    let term = lang
        .parse_term(&normalized_state)
        .map_err(|e| format!("state parse failed: {e}"))?;
    let results = with_mm0_theorem_facts(&facts, || run_mm0lite_mork_backend(term.as_ref()))
        .map_err(|e| format!("mork execution failed: {e}"))?;
    let verified = results
        .normal_forms()
        .iter()
        .any(|nf| nf.display.contains("verified"));
    Ok(verified)
}

#[cfg(feature = "mork-backend")]
#[test]
fn mm0lite_fixture_corpus_matches_expected_outcomes() {
    let cases = load_cases();
    assert!(!cases.is_empty(), "fixture corpus should not be empty");
    for case in &cases {
        let got = eval_case(case);
        match (case.expect_mettail_exit, got) {
            (false, Ok(v)) => {
                panic!("case '{}' expected failure but succeeded (verified={v})", case.case_id)
            },
            (true, Err(e)) => panic!("case '{}' expected success but failed: {e}", case.case_id),
            (false, Err(_)) => {},
            (true, Ok(v)) => assert_eq!(
                v, case.expect_mettail_verified,
                "case '{}' verified mismatch",
                case.case_id
            ),
        }
    }
}
