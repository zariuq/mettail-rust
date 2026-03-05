#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 <cargo-args...>" >&2
  echo "example: $0 check -p mettail-repl --tests" >&2
  exit 2
fi

: "${METTAIL_LOWMEM_VMEM_KB:=8388608}"
: "${CARGO_BUILD_JOBS:=1}"

base_rustflags="-C debuginfo=0 -C codegen-units=1"
if [[ "${METTAIL_LOWMEM_USE_CRANELIFT:-0}" == "1" ]]; then
  base_rustflags="-Z codegen-backend=cranelift ${base_rustflags}"
fi

RUSTFLAGS="${RUSTFLAGS:-$base_rustflags}"

ulimit -v "${METTAIL_LOWMEM_VMEM_KB}"
export CARGO_BUILD_JOBS
export RUSTFLAGS

exec cargo "$@"
