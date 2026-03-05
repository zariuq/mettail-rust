#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARTIFACT_DIR="${ROOT_DIR}/repl/artifacts/syntax"
ALGORITHMS_DIR="${ALGORITHMS_DIR:-${ROOT_DIR}/../../lean-projects/algorithms}"
TMP_DIR="${ROOT_DIR}/.artifacts/.syntax_sync_tmp"

REQUIRED_FILES=(
  he.syntax_spec.json
  he.syntax_spec.checksum
  he.grammar_spec.json
  he.grammar_spec.checksum
  he.tree_sitter_grammar.js
  he.parser_probe.snapshot
  he.parser_probe.checksum
  petta.syntax_spec.json
  petta.syntax_spec.checksum
  petta.grammar_spec.json
  petta.grammar_spec.checksum
  petta.tree_sitter_grammar.js
  petta.parser_probe.snapshot
  petta.parser_probe.checksum
)

require_artifact_files() {
  for file in "${REQUIRED_FILES[@]}"; do
    if [[ ! -f "${ARTIFACT_DIR}/${file}" ]]; then
      echo "missing syntax artifact: ${ARTIFACT_DIR}/${file}" >&2
      exit 1
    fi
  done
}

verify_artifact_checksums() {
  python3 - "${ARTIFACT_DIR}" <<'PY'
import pathlib
import sys

base = pathlib.Path(sys.argv[1])

FNV64_OFFSET = 14695981039346656037
FNV64_PRIME = 1099511628211

def fnv1a64(text: str) -> int:
    h = FNV64_OFFSET
    for b in text.encode("utf-8"):
        h = (h ^ b) * FNV64_PRIME
        h &= 0xFFFFFFFFFFFFFFFF
    return h

def read(path: pathlib.Path) -> str:
    return path.read_text(encoding="utf-8")

for dialect in ("he", "petta"):
    syntax_json = read(base / f"{dialect}.syntax_spec.json").strip()
    syntax_expected = int(read(base / f"{dialect}.syntax_spec.checksum").strip())
    syntax_actual = fnv1a64(syntax_json)
    if syntax_actual != syntax_expected:
        raise SystemExit(
            f"syntax checksum mismatch for {dialect}: expected {syntax_expected}, got {syntax_actual}"
        )

    grammar_json = read(base / f"{dialect}.grammar_spec.json").strip()
    grammar_js = read(base / f"{dialect}.tree_sitter_grammar.js")
    grammar_expected = int(read(base / f"{dialect}.grammar_spec.checksum").strip())
    grammar_actual = fnv1a64(f"{grammar_json}\n---\n{grammar_js}")
    if grammar_actual != grammar_expected:
        raise SystemExit(
            f"grammar checksum mismatch for {dialect}: expected {grammar_expected}, got {grammar_actual}"
        )

    parser_probe_snapshot = read(base / f"{dialect}.parser_probe.snapshot")
    # Lean exports snapshot ++ "\n", but checksum covers snapshot text without the trailing newline.
    if parser_probe_snapshot.endswith("\n"):
        parser_probe_snapshot = parser_probe_snapshot[:-1]
    parser_probe_expected = int(read(base / f"{dialect}.parser_probe.checksum").strip())
    parser_probe_actual = fnv1a64(parser_probe_snapshot)
    if parser_probe_actual != parser_probe_expected:
        raise SystemExit(
            f"parser probe checksum mismatch for {dialect}: expected {parser_probe_expected}, got {parser_probe_actual}"
        )

print("syntax artifacts checksum verification passed")
PY
}

compare_with_lean_exports() {
  rm -rf "${TMP_DIR}"
  mkdir -p "${TMP_DIR}"
  trap 'rm -rf "${TMP_DIR}"' EXIT

  (
    cd "${ALGORITHMS_DIR}"
    ulimit -v 6291456 || true
    lake exe simpleMeTTa syntax-spec export-all "${TMP_DIR}"
    lake exe simpleMeTTa syntax-spec export-grammar-all "${TMP_DIR}"
    lake exe simpleMeTTa syntax-spec check-parser-drift-all "${TMP_DIR}"
  )

  for file in "${REQUIRED_FILES[@]}"; do
    if ! diff -u "${TMP_DIR}/${file}" "${ARTIFACT_DIR}/${file}"; then
      echo >&2
      echo "syntax export sync check failed for ${file}." >&2
      echo "Regenerate with Lean and sync repl/artifacts/syntax." >&2
      exit 1
    fi
  done

  echo "syntax export sync check passed (compared with Lean export)"
}

require_artifact_files
verify_artifact_checksums

if [[ -d "${ALGORITHMS_DIR}" ]] && [[ -f "${ALGORITHMS_DIR}/Algorithms/MeTTa/Simple/Main.lean" ]]; then
  compare_with_lean_exports
else
  echo "lean algorithms checkout not available at ${ALGORITHMS_DIR}; checksum-only validation completed."
fi
