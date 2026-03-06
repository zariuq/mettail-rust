use std::collections::BTreeSet;

use mettail_languages::mm0lite_artifacts::{
    load_mm0lite_lookup_artifact, load_mm0lite_rewrite_ir_artifact,
    load_mm0lite_transition_artifact, mm0lite_artifact_dir, mm0lite_generated_language_path,
    parse_rule_ids_from_generated_language,
};

#[test]
fn mm0lite_lookup_artifact_loads_and_exposes_thm_lookup_family() {
    let dir = mm0lite_artifact_dir();
    let artifact =
        load_mm0lite_lookup_artifact(&dir).expect("MM0-lite lookup artifact should parse");
    assert_eq!(artifact.dialect, "mm0lite");
    assert!(!artifact.families.is_empty(), "lookup families should not be empty");

    let family = artifact
        .families
        .iter()
        .find(|f| f.family == "thmConcl")
        .expect("thmConcl family should exist");
    assert_eq!(family.logical_relation_id, "mm0lite.thm_concl");
    assert_eq!(family.query_arity, 1);
    assert_eq!(family.payload_arity, 1);
    assert!(
        family
            .demand
            .iter()
            .any(|d| d.logical_relation_id == "mm0lite.thm_concl.result"),
        "result demand signature missing"
    );
}

#[test]
fn mm0lite_transition_artifact_loads_and_is_self_consistent() {
    let dir = mm0lite_artifact_dir();
    let artifact =
        load_mm0lite_transition_artifact(&dir).expect("MM0-lite transition artifact should parse");
    assert_eq!(artifact.dialect, "mm0lite");
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
fn mm0lite_transition_ids_match_generated_language_rules() {
    let dir = mm0lite_artifact_dir();
    let transition =
        load_mm0lite_transition_artifact(&dir).expect("MM0-lite transition artifact should parse");
    let generated_ids = parse_rule_ids_from_generated_language(&mm0lite_generated_language_path())
        .expect("generated MM0-lite language should contain rewrite rule ids");
    let artifact_ids: BTreeSet<String> =
        transition.rules.iter().map(|r| r.rule_id.clone()).collect();

    assert_eq!(
        artifact_ids, generated_ids,
        "MM0-lite transition rule ids must match generated language rewrites"
    );
}

#[test]
fn mm0lite_rewrite_ir_loads_and_matches_transition_artifact() {
    let dir = mm0lite_artifact_dir();
    let transition =
        load_mm0lite_transition_artifact(&dir).expect("MM0-lite transition artifact should parse");
    let rewrite_ir =
        load_mm0lite_rewrite_ir_artifact(&dir).expect("MM0-lite rewrite-ir artifact should parse");

    let transition_ids: BTreeSet<String> =
        transition.rules.iter().map(|r| r.rule_id.clone()).collect();
    let rewrite_ids: BTreeSet<String> =
        rewrite_ir.rules.iter().map(|r| r.rule_id.clone()).collect();
    assert_eq!(
        transition_ids, rewrite_ids,
        "MM0-lite transition and rewrite-ir rule ids must match"
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
