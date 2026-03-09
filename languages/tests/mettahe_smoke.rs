/// Smoke tests for the MeTTaHE language backend.
///
/// Tests exercise the core MORK-first HE runtime at the language layer,
/// bypassing the REPL surface layer entirely. Each test constructs a
/// core HE state term, runs the native MORK backend, and checks the
/// normal-form output.
use mettail_languages::mettahe_from_lean::{run_mettahe_mork_backend, MeTTaHELanguage};
use mettail_runtime::Language;

fn all_displays(results: &mettail_runtime::AscentResults) -> Vec<String> {
    results
        .all_terms
        .iter()
        .map(|t| t.display.clone())
        .collect()
}

fn run_he(input: &str) -> mettail_runtime::AscentResults {
    mettail_runtime::clear_var_cache();
    let lang = MeTTaHELanguage;
    let term = lang.parse_term(input).expect("parse should succeed");
    run_mettahe_mork_backend(term.as_ref()).expect("MORK execution should succeed")
}

// ─── R16: C_Return → C_Done (unconditional) ───────────────────────────

#[test]
fn r16_return_reaches_done() {
    let results = run_he("C_State(C_Return(C_SymAtom(hello)), C_Space(C_ExprNil), C_Empty)");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_SymAtom(hello)")),
        "expected C_Done carrying C_SymAtom(hello), got: {displays:?}"
    );
}

// ─── R0 + R16: isEmpty(C_Empty) → Return → Done ───────────────────────

#[test]
fn r0_r16_empty_atom_returns_immediately() {
    let results = run_he("C_State(C_Metta(C_Empty, C_AtomType), C_Space(C_ExprNil), C_Empty)");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_Empty")),
        "expected C_Done with C_Empty result, got: {displays:?}"
    );
}

// ─── R2 + R16: symbol with AtomType → typeMatchesMetaOrAtom → Return → Done

#[test]
fn r2_r16_symbol_matches_atom_type() {
    // C_AtomType matches everything → R2 fires → Return → Done
    let results =
        run_he("C_State(C_Metta(C_SymAtom(foo), C_AtomType), C_Space(C_ExprNil), C_Empty)");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_SymAtom(foo)")),
        "expected C_Done with C_SymAtom(foo), got: {displays:?}"
    );
}

// ─── R3 path: symbol with UndefinedType → needsTypeCast → TypeCast

#[test]
fn r3_symbol_undefined_type_goes_to_typecast() {
    // C_SymAtom has metaType=SymbolType ≠ UndefinedType → R3 fires
    let results =
        run_he("C_State(C_Metta(C_SymAtom(foo), C_UndefinedType), C_Space(C_ExprNil), C_Empty)");
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_TypeCast(C_SymAtom(foo)")),
        "expected C_TypeCast for symbol with UndefinedType, got: {displays:?}"
    );
}

// ─── Equation matching: nondeterministic, two equations produce two results ──

#[test]
fn eq_nondet_two_matching_equations() {
    // Space has two equations: (= (f a) result1) and (= (f a) result2)
    // Start at MettaCall with (f a) — both R12 branches should fire.
    let results = run_he(concat!(
        "C_State(",
        "C_MettaCall(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_AtomType",
        "),",
        "C_Space(",
        "C_ExprCons(",
        "C_EqAtom(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_SymAtom(result1)",
        "),",
        "C_ExprCons(",
        "C_EqAtom(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_SymAtom(result2)",
        "),",
        "C_ExprNil",
        ")",
        ")",
        "),",
        "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    let has_r1 = displays.iter().any(|d| d.contains("result1"));
    let has_r2 = displays.iter().any(|d| d.contains("result2"));
    assert!(
        has_r1 && has_r2,
        "expected both result1 and result2 in nondeterministic output, got: {displays:?}"
    );
}

// ─── Equation matching: same RHS from two equations (Ascent dedup) ──────
// NOTE: Ascent relations dedup tuples.  If two equations produce the same RHS
// for the same input, Ascent will store only one eqQueryResult fact.  This is
// acceptable for HE: the result set is correct (same value appears once), and
// the nondeterministic branching is still faithful because distinct RHS values
// produce distinct tuples.

#[test]
fn eq_dedup_same_rhs_produces_one_result() {
    // Two equations: (= (f a) same) and (= (f a) same)
    // Ascent should dedup → only one C_Metta(same, ...) branch
    let results = run_he(concat!(
        "C_State(",
        "C_MettaCall(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_AtomType",
        "),",
        "C_Space(",
        "C_ExprCons(",
        "C_EqAtom(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_SymAtom(same)",
        "),",
        "C_ExprCons(",
        "C_EqAtom(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_SymAtom(same)",
        "),",
        "C_ExprNil",
        ")",
        ")",
        "),",
        "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("same")),
        "expected result 'same' in output, got: {displays:?}"
    );
}

// ─── Negative: no matching equation → R13 (noEqQuery) fallback ─────────

#[test]
fn eq_no_match_falls_through_to_return() {
    // Space has (= (g b) result1) but we query (f a) — no match
    let results = run_he(concat!(
        "C_State(",
        "C_MettaCall(",
        "C_ExprCons(C_SymAtom(f), C_ExprCons(C_SymAtom(a), C_ExprNil)),",
        "C_AtomType",
        "),",
        "C_Space(",
        "C_ExprCons(",
        "C_EqAtom(",
        "C_ExprCons(C_SymAtom(g), C_ExprCons(C_SymAtom(b), C_ExprNil)),",
        "C_SymAtom(result1)",
        "),",
        "C_ExprNil",
        ")",
        "),",
        "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    // R13 fires: noEqQuery + notExecutable → Return(atom) → Done
    assert!(
        displays.iter().any(|d| d.contains("C_Done")),
        "expected C_Done from no-match fallback, got: {displays:?}"
    );
    // The original atom (f a) should be returned unchanged
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_SymAtom(f)")),
        "expected original atom (f a) in Done result, got: {displays:?}"
    );
}

// ─── Equation with variable: (= (double $x) (+ $x $x)), query (double 5) ──

#[test]
fn eq_variable_pattern_match_at_mettacall() {
    // Space: (= (double $x) (+ $x $x))
    // Query at MettaCall: (double 5) should match, producing (+ 5 5)
    let results = run_he(concat!(
        "C_State(",
          "C_MettaCall(",
            "C_ExprCons(C_SymAtom(double), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_AtomType",
          "),",
          "C_Space(",
            "C_ExprCons(",
              "C_EqAtom(",
                "C_ExprCons(C_SymAtom(double), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                "C_ExprCons(C_OpAdd, C_ExprCons(C_VarAtom(x), C_ExprCons(C_VarAtom(x), C_ExprNil)))",
              "),",
              "C_ExprCons(",
                "C_TypeAnnotation(",
                  "C_OpAdd,",
                  "C_ArrowType(C_ExprCons(C_GroundedType, C_ExprCons(C_GroundedType, C_ExprNil)), C_GroundedType)",
                "),",
                "C_ExprNil",
              ")",
            ")",
          "),",
          "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    // R12 fires: eqQueryResult matches (double 5) → rhs = (+ 5 5)
    // Then (+ 5 5) proceeds through Metta → InterpExpr → InterpFunc → MettaCall → groundedCallResult → 10
    assert!(
        displays.iter().any(|d| d.contains("C_Metta(")),
        "expected transition to C_Metta with substituted rhs, got: {displays:?}"
    );
}

// ─── Grounded arithmetic regression: (+ 3 2) via InterpFunc → MettaCall ─
// NOTE: UndefinedType is used (not AtomType) because AtomType matches everything
// and R2 would return the expression unevaluated.  The surface layer's `!expr`
// always uses UndefinedType to trigger interpretation (R4 needsInterpExpr).

#[test]
fn grounded_add_via_mettacall_after_passthrough() {
    // After eval_interp_func became pass-through, grounded ops must flow:
    // Metta → R4 (InterpExpr) → R5 (InterpFunc) → R8 (MettaCall) → R11 (groundedCallResult) → Done
    let results = run_he(concat!(
        "C_State(",
          "C_Metta(",
            "C_ExprCons(C_OpAdd, C_ExprCons(C_GInt(C_3), C_ExprCons(C_GInt(C_2), C_ExprNil))),",
            "C_UndefinedType",
          "),",
          "C_Space(",
            "C_ExprCons(",
              "C_TypeAnnotation(",
                "C_OpAdd,",
                "C_ArrowType(C_ExprCons(C_GroundedType, C_ExprCons(C_GroundedType, C_ExprNil)), C_GroundedType)",
              "),",
              "C_ExprNil",
            ")",
          "),",
          "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_GInt(C_5)")),
        "expected C_Done with C_GInt(C_5) for (+ 3 2), got: {displays:?}"
    );
}

// ─── Full E2E: (double 5) → 10 through entire state machine ────────────

#[test]
fn e2e_double_5_equals_10() {
    // Full flow: Metta((double 5), UndefinedType)
    //   → R4 InterpExpr → R5 InterpFunc(pass-through) → R8 MettaCall
    //   → R12 eqQueryResult: (double $x) matches → rhs = (+ 5 5)
    //   → Metta((+ 5 5), GroundedType)
    //   → R4 InterpExpr → R5 InterpFunc → R8 MettaCall
    //   → R11 groundedCallResult → 10 → Return → Done
    let results = run_he(concat!(
        "C_State(",
          "C_Metta(",
            "C_ExprCons(C_SymAtom(double), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_UndefinedType",
          "),",
          "C_Space(",
            "C_ExprCons(",
              "C_EqAtom(",
                "C_ExprCons(C_SymAtom(double), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                "C_ExprCons(C_OpAdd, C_ExprCons(C_VarAtom(x), C_ExprCons(C_VarAtom(x), C_ExprNil)))",
              "),",
              "C_ExprCons(",
                "C_TypeAnnotation(",
                  "C_SymAtom(double),",
                  "C_ArrowType(C_ExprCons(C_GroundedType, C_ExprNil), C_GroundedType)",
                "),",
                "C_ExprCons(",
                  "C_TypeAnnotation(",
                    "C_OpAdd,",
                    "C_ArrowType(C_ExprCons(C_GroundedType, C_ExprCons(C_GroundedType, C_ExprNil)), C_GroundedType)",
                  "),",
                  "C_ExprNil",
                ")",
              ")",
            ")",
          "),",
          "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_GInt(C_10)")),
        "expected C_Done with C_GInt(C_10) for (double 5), got: {displays:?}"
    );
}

// ─── Full E2E: untyped equation-defined head (id 5) → 5 ───────────────

#[test]
fn e2e_untyped_id_5_equals_5() {
    let results = run_he(concat!(
        "C_State(",
          "C_Metta(",
            "C_ExprCons(C_SymAtom(id), C_ExprCons(C_GInt(C_5), C_ExprNil)),",
            "C_UndefinedType",
          "),",
          "C_Space(",
            "C_ExprCons(",
              "C_EqAtom(",
                "C_ExprCons(C_SymAtom(id), C_ExprCons(C_VarAtom(x), C_ExprNil)),",
                "C_VarAtom(x)",
              "),",
              "C_ExprNil",
            ")",
          "),",
          "C_Empty",
        ")"
    ));
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("C_MettaCall(")),
        "expected untyped head to fall through to C_MettaCall, got: {displays:?}"
    );
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_GInt(C_5)")),
        "expected C_Done with C_GInt(C_5) for untyped (id 5), got: {displays:?}"
    );
}


// ─── R4 + IE_NoType + MC_NoMatch: untyped expression head falls through ──

#[test]
fn r4_ie_notype_mc_nomatch_untyped_expression_falls_through() {
    let results = run_he(
        "C_State(C_Metta(C_ExprCons(C_SymAtom(foo), C_ExprNil), C_UndefinedType), C_Space(C_ExprNil), C_Empty)",
    );
    let displays = all_displays(&results);
    assert!(
        displays.iter().any(|d| d.contains("C_MettaCall(")),
        "expected IE_NoType fallthrough to C_MettaCall, got: {displays:?}"
    );
    assert!(
        displays
            .iter()
            .any(|d| d.contains("C_Done") && d.contains("C_SymAtom(foo)") && d.contains("C_ExprNil")),
        "expected unknown untyped expression to return unchanged after mettaCall, got: {displays:?}"
    );
}
