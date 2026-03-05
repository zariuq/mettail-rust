#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUST_PATH="${ROOT_DIR}/languages/src/generated/mettahe_language_working.rs"
ARTIFACT_PATH="${ROOT_DIR}/.artifacts/mettahe.generated.rs"
METTAPEDIA_DIR="${METTAPEDIA_DIR:-${ROOT_DIR}/../../lean-projects/mettapedia}"

if [[ ! -f "${RUST_PATH}" ]]; then
  echo "missing Rust generated file: ${RUST_PATH}" >&2
  exit 1
fi

TMP_RUST_BLOCK="${ROOT_DIR}/.artifacts/.mettahe_sync_rust_block.txt"
TMP_ART_BLOCK="${ROOT_DIR}/.artifacts/.mettahe_sync_artifact_block.txt"
TMP_ART_RAW="${ROOT_DIR}/.artifacts/.mettahe_sync_artifact_raw.txt"
trap 'rm -f "${TMP_RUST_BLOCK}" "${TMP_ART_BLOCK}" "${TMP_ART_RAW}"' EXIT

if [[ -d "${METTAPEDIA_DIR}" ]] && [[ -f "${METTAPEDIA_DIR}/Mettapedia/OSLF/Tools/ExportMeTTaHE.lean" ]]; then
  (
    cd "${METTAPEDIA_DIR}"
    ulimit -v 6291456 || true
    lake env lean --run Mettapedia/OSLF/Tools/ExportMeTTaHE.lean > "${TMP_ART_RAW}"
  )
elif [[ -f "${ARTIFACT_PATH}" ]]; then
  cp "${ARTIFACT_PATH}" "${TMP_ART_RAW}"
else
  echo "missing Lean source and fallback artifact for HE export sync." >&2
  echo "Expected either METTAPEDIA_DIR=${METTAPEDIA_DIR} or ${ARTIFACT_PATH}." >&2
  exit 1
fi

sed -E 's/[[:space:]]+$//' "${RUST_PATH}" \
  | sed '/^[[:space:]]*$/d' > "${TMP_RUST_BLOCK}"

sed -E 's/[[:space:]]+$//' "${TMP_ART_RAW}" \
  | sed '/^[[:space:]]*$/d' > "${TMP_ART_BLOCK}"

if ! diff -u "${TMP_ART_BLOCK}" "${TMP_RUST_BLOCK}"; then
  echo >&2
  echo "mettahe export sync check failed." >&2
  echo "Regenerate .artifacts/mettahe.generated.rs from ExportMeTTaHE.lean and sync languages/src/generated/mettahe_language_working.rs." >&2
  exit 1
fi

echo "mettahe export sync check passed."
