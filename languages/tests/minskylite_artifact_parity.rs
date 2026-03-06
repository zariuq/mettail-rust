use std::collections::BTreeSet;

use mettail_languages::minskylite_artifacts::{
    load_minskylite_lookup_artifact, load_minskylite_rewrite_ir_artifact,
    load_minskylite_transition_artifact, minskylite_artifact_dir,
    minskylite_generated_language_path, parse_rule_ids_from_generated_language,
};

#[test]
fn minskylite_lookup_artifact_loads_and_is_empty_for_current_core() {
    let dir = minskylite_artifact_dir();
    let artifact =
        load_minskylite_lookup_artifact(&dir).expect("MinskyLite lookup artifact should parse");
    assert_eq!(artifact.dialect, "minskylite");
    assert!(
        artifact.families.is_empty(),
        "MinskyLite core semantics should not declare lookup families yet"
    );
}

#[test]
fn minskylite_transition_artifact_loads_and_is_self_consistent() {
    let dir = minskylite_artifact_dir();
    let artifact = load_minskylite_transition_artifact(&dir)
        .expect("MinskyLite transition artifact should parse");
    assert_eq!(artifact.dialect, "minskylite");
    assert!(!artifact.sources.is_empty(), "sources should not be empty");
    assert!(!artifact.rules.is_empty(), "rules should not be empty");

    let rule_ids: BTreeSet<String> = artifact.rules.iter().map(|r| r.rule_id.clone()).collect();
    for src in &artifact.sources {
        assert!(
            !src.ordered_rules.is_empty(),
            "source {} should have ordered rules",
            src.source_instr
        );
        for rid in &src.ordered_rules {
            assert!(
                rule_ids.contains(rid),
                "source {} references unknown rule {}",
                src.source_instr,
                rid
            );
        }
    }
}

#[test]
fn minskylite_transition_ids_match_generated_language_rules() {
    let dir = minskylite_artifact_dir();
    let transition = load_minskylite_transition_artifact(&dir)
        .expect("MinskyLite transition artifact should parse");
    let generated_ids =
        parse_rule_ids_from_generated_language(&minskylite_generated_language_path())
            .expect("generated MinskyLite language should contain rewrite rule ids");
    let artifact_ids: BTreeSet<String> =
        transition.rules.iter().map(|r| r.rule_id.clone()).collect();

    assert_eq!(
        artifact_ids, generated_ids,
        "MinskyLite transition rule ids must match generated language rewrites"
    );
}

#[test]
fn minskylite_rewrite_ir_loads_and_matches_transition_artifact() {
    let dir = minskylite_artifact_dir();
    let transition = load_minskylite_transition_artifact(&dir)
        .expect("MinskyLite transition artifact should parse");
    let rewrite_ir = load_minskylite_rewrite_ir_artifact(&dir)
        .expect("MinskyLite rewrite-ir artifact should parse");

    let transition_ids: BTreeSet<String> =
        transition.rules.iter().map(|r| r.rule_id.clone()).collect();
    let rewrite_ids: BTreeSet<String> =
        rewrite_ir.rules.iter().map(|r| r.rule_id.clone()).collect();
    assert_eq!(
        transition_ids, rewrite_ids,
        "MinskyLite transition and rewrite-ir rule ids must match"
    );

    for tr in &transition.rules {
        let rw = rewrite_ir
            .rules
            .iter()
            .find(|rw| rw.rule_id == tr.rule_id)
            .expect("rule id should exist in rewrite-ir");
        assert_eq!(
            rw.source_instr, tr.source_instr,
            "rule '{}' source mismatch between transition and rewrite-ir artifacts",
            tr.rule_id
        );
        assert!(
            !rw.rule_name.trim().is_empty(),
            "rewrite-ir rule_name should be non-empty for rule '{}'",
            tr.rule_id
        );
    }
}
