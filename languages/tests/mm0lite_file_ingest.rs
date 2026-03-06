use mettail_languages::mm0lite_from_lean::{
    parse_mm0_formula, parse_mm0_theorem_facts, MM0LiteLanguage,
};
use mettail_runtime::Language;

#[test]
fn parse_mm0_formula_implication_chain() {
    let parsed = parse_mm0_formula("(P -> (Q -> R))").expect("formula should parse");
    assert_eq!(format!("{}", parsed), "(P -> (Q -> R))");
}

#[test]
fn parse_mm0_formula_accepts_variable_aliases() {
    let parsed = parse_mm0_formula("(a -> (b -> c))").expect("formula should parse");
    assert_eq!(format!("{}", parsed), "(P -> (Q -> R))");
}

#[test]
fn parse_mm0_theorem_facts_from_realish_mm0_source() {
    let src = r#"
delimiter $ ( ) $;
provable sort wff;
term P: wff; term Q: wff; term R: wff;
term imp: wff > wff > wff;
infixr imp: $->$ prec 25;
axiom thm_imp_p_q: $ P -> Q $;
axiom thm_imp_q_r: $ Q -> R $;
"#;
    let facts = parse_mm0_theorem_facts(src).expect("MM0 source should produce facts");
    assert!(facts
        .iter()
        .any(|(name, f)| name == "thm_imp_p_q" && format!("{}", f) == "(P -> Q)"));
    assert!(facts
        .iter()
        .any(|(name, f)| name == "thm_imp_q_r" && format!("{}", f) == "(Q -> R)"));
}

#[cfg(feature = "mork-backend")]
#[test]
fn mm0lite_mork_uses_loaded_theorem_facts() {
    use mettail_languages::mm0lite_from_lean::{run_mm0lite_mork_backend, with_mm0_theorem_facts};

    let lang = MM0LiteLanguage;
    let term = lang
        .parse_term("state [ use thm_imp_p_q :: [ mp :: [] ] ] Q { P ; {} } pending")
        .expect("state should parse");

    let bad_db = parse_mm0_theorem_facts("axiom thm_imp_p_q: $ P -> R $;")
        .expect("bad db should still parse");
    let bad = with_mm0_theorem_facts(&bad_db, || {
        run_mm0lite_mork_backend(term.as_ref()).expect("mork run should succeed")
    });
    assert!(
        !bad.normal_forms()
            .iter()
            .any(|nf| nf.display.contains("verified")),
        "unexpected verification with mismatched theorem facts: {:?}",
        bad.normal_forms()
            .iter()
            .map(|nf| nf.display.clone())
            .collect::<Vec<_>>()
    );

    let good_db =
        parse_mm0_theorem_facts("axiom thm_imp_p_q: $ P -> Q $;").expect("good db should parse");
    let good = with_mm0_theorem_facts(&good_db, || {
        run_mm0lite_mork_backend(term.as_ref()).expect("mork run should succeed")
    });
    assert!(
        good.normal_forms()
            .iter()
            .any(|nf| nf.display.contains("verified")),
        "expected verification with matching theorem facts, got: {:?}",
        good.normal_forms()
            .iter()
            .map(|nf| nf.display.clone())
            .collect::<Vec<_>>()
    );
}
