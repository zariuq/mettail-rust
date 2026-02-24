#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
METTAPEDIA_DIR="${METTAPEDIA_DIR:-$ROOT/../../lean-projects/mettapedia}"
ARTIFACT_DIR="$ROOT/.artifacts/mettaminimal_roundtrip"

mkdir -p "$ARTIFACT_DIR"

LANG_TXT="$ARTIFACT_DIR/language.txt"
INPUT_TXT="$ARTIFACT_DIR/input.txt"
EXPECTED_TXT="$ARTIFACT_DIR/expected.txt"

echo "[1/4] Exporting MeTTaMinimal artifacts from Lean"
(
  ulimit -v 6291456
  export LEAN_NUM_THREADS=1
  export LAKE_JOBS=1
  cd "$METTAPEDIA_DIR"
  lake env lean --run "$ROOT/scripts/lean/ExportMeTTaMinimalRoundTrip.lean" \
    "$LANG_TXT" "$INPUT_TXT" "$EXPECTED_TXT"
)

INPUT_TERM="$(tr -d '\r\n' < "$INPUT_TXT")"
EXPECTED_TERM="$(tr -d '\r\n' < "$EXPECTED_TXT")"
BIN_PATH="$ROOT/target/debug/mettaminimal_roundtrip"

echo "[2/4] Regenerating Rust language module from Lean export"
cat > "$ROOT/languages/src/mettaminimal_from_lean.rs" <<'RS'
#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
RS
cat "$LANG_TXT" >> "$ROOT/languages/src/mettaminimal_from_lean.rs"
printf '\n' >> "$ROOT/languages/src/mettaminimal_from_lean.rs"

if ! rg -q "^language!" "$LANG_TXT"; then
  echo "ERROR: expected Lean language export in $LANG_TXT" >&2
  exit 1
fi

echo "[3/4] Building round-trip checker"
(
  ulimit -v 6291456
  cd "$ROOT"
  cargo build -q -p mettail-languages --bin mettaminimal_roundtrip
)

echo "[4/4] Comparing Rust rewrite result to Lean expected output"
(
  ulimit -v 6291456
  cd "$ROOT"
  "$BIN_PATH" "$INPUT_TERM" "$EXPECTED_TERM"
)

echo "MeTTaMinimal round-trip passed."
