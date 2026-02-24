import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.MeTTaIL.Export

open Mettapedia.OSLF.MeTTaIL.Export

/-- Premise-free MeTTaMinimal subset that current mettail-rust ingestion supports.
This keeps the same signature but exports only unconditional rewrites. -/
def mettaMinimalExport : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  let base := Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal
  { base with rewrites := base.rewrites.filter (fun rw => rw.premises.isEmpty) }

/-- Round-trip smoke input term for MeTTaMinimalState.
Uses `StepEval` (no external premise environment required). -/
def mettaMinimalInput : String :=
  "C_State(C_Eval(C_ATrue), C_AFalse, C_ATrue)"

/-- Expected one-step rewrite result from `StepEval`. -/
def mettaMinimalExpected : String :=
  "C_State(C_Return(C_ATrue), C_AFalse, C_ATrue)"

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run scripts/lean/ExportMeTTaMinimalRoundTrip.lean"
    , "  lake env lean --run scripts/lean/ExportMeTTaMinimalRoundTrip.lean <lang_out> <input_out> <expected_out>"
    ]

/--
Emit round-trip artifacts for the Lean->Rust MeTTaMinimal loop.

- No args: print all artifacts to stdout.
- 3 args: write language macro text, input term, expected output term to files.
-/
def main (args : List String) : IO UInt32 := do
  let rendered := renderLanguage mettaMinimalExport
  match args with
  | [] =>
      IO.println "=== LANGUAGE ==="
      IO.println rendered
      IO.println "=== INPUT ==="
      IO.println mettaMinimalInput
      IO.println "=== EXPECTED ==="
      IO.println mettaMinimalExpected
      pure 0
  | [langOut, inputOut, expectedOut] =>
      IO.FS.writeFile langOut (rendered ++ "\n")
      IO.FS.writeFile inputOut (mettaMinimalInput ++ "\n")
      IO.FS.writeFile expectedOut (mettaMinimalExpected ++ "\n")
      pure 0
  | _ =>
      IO.eprintln usage
      pure 1
