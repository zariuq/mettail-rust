use std::collections::BTreeSet;

use codex_imp_harness::imp_artifacts::{
    imp_artifact_dir, imp_generated_language_path, load_imp_lookup_artifact,
    load_imp_rewrite_ir_artifact, load_imp_transition_artifact,
    parse_rule_ids_from_generated_language,
};

#[test]
fn imp_lookup_artifact_loads_and_exposes_store_get_family() {
    let dir = imp_artifact_dir();
    let artifact = load_imp_lookup_artifact(&dir).expect("IMP lookup artifact should parse");
    assert_eq!(artifact.dialect, "imp");
    let family = artifact
        .families
        .iter()
        .find(|f| f.family == "storeGet")
        .expect("storeGet family should exist");
    assert_eq!(family.logical_relation_id, "imp.store_get");
    assert_eq!(family.query_arity, 2);
    assert_eq!(family.payload_arity, 1);
    assert!(family.contracts.exact_result);
    assert!(family.contracts.no_false_negatives);
}

#[test]
fn imp_transition_artifact_loads_and_is_self_consistent() {
    let dir = imp_artifact_dir();
    let artifact = load_imp_transition_artifact(&dir).expect("IMP transition artifact should parse");
    assert_eq!(artifact.dialect, "imp");
    assert!(!artifact.sources.is_empty());
    assert!(!artifact.rules.is_empty());

    let rule_ids: BTreeSet<String> = artifact.rules.iter().map(|r| r.rule_id.clone()).collect();
    for src in &artifact.sources {
        assert!(!src.ordered_rules.is_empty(), "source {} should have rules", src.source_instr);
        for rid in &src.ordered_rules {
            assert!(rule_ids.contains(rid), "source {} references unknown rule {}", src.source_instr, rid);
        }
    }
}

#[test]
fn imp_transition_ids_match_generated_language_rules() {
    let dir = imp_artifact_dir();
    let transition = load_imp_transition_artifact(&dir).expect("IMP transition artifact should parse");
    let generated_ids = parse_rule_ids_from_generated_language(&imp_generated_language_path())
        .expect("generated IMP language should contain rewrite ids");
    let artifact_ids: BTreeSet<String> = transition.rules.iter().map(|r| r.rule_id.clone()).collect();
    assert_eq!(artifact_ids, generated_ids, "IMP transition rule ids must match generated language rewrites");
}

#[test]
fn imp_rewrite_ir_loads_and_matches_transition_artifact() {
    let dir = imp_artifact_dir();
    let transition = load_imp_transition_artifact(&dir).expect("IMP transition artifact should parse");
    let rewrite_ir = load_imp_rewrite_ir_artifact(&dir).expect("IMP rewrite-ir artifact should parse");

    let transition_ids: BTreeSet<String> = transition.rules.iter().map(|r| r.rule_id.clone()).collect();
    let rewrite_ids: BTreeSet<String> = rewrite_ir.rules.iter().map(|r| r.rule_id.clone()).collect();
    assert_eq!(transition_ids, rewrite_ids, "IMP transition and rewrite-ir rule ids must match");

    for tr in &transition.rules {
        let rw = rewrite_ir
            .rules
            .iter()
            .find(|rw| rw.rule_id == tr.rule_id)
            .expect("rule id should exist in rewrite-ir");
        assert_eq!(rw.source_instr, tr.source_instr, "rule '{}' source mismatch", tr.rule_id);
        assert!(!rw.rule_name.trim().is_empty(), "rule_name should be non-empty for '{}')", tr.rule_id);
    }
}
