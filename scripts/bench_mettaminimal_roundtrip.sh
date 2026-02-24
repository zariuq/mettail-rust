#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RUNS="${1:-3}"

if ! [[ "$RUNS" =~ ^[0-9]+$ ]] || [ "$RUNS" -lt 1 ]; then
  echo "Usage: $0 [runs>=1]" >&2
  exit 2
fi

ARTIFACT_DIR="$ROOT/.artifacts/mettaminimal_roundtrip"
TIMES_FILE="$ARTIFACT_DIR/bench_times_seconds.txt"
LAST_TIME_FILE="$ARTIFACT_DIR/.bench_last_time_seconds.txt"

mkdir -p "$ARTIFACT_DIR"
: > "$TIMES_FILE"

echo "Benchmark: MeTTaMinimal Lean->Rust roundtrip"
echo "Runs: $RUNS"

for i in $(seq 1 "$RUNS"); do
  LOG_FILE="$ARTIFACT_DIR/bench_run_${i}.log"
  echo "[${i}/${RUNS}] ./scripts/roundtrip_mettaminimal.sh"
  (
    ulimit -v 6291456
    export LEAN_NUM_THREADS=1
    export LAKE_JOBS=1
    /usr/bin/time -f "%e" -o "$LAST_TIME_FILE" \
      "$ROOT/scripts/roundtrip_mettaminimal.sh"
  ) > "$LOG_FILE" 2>&1
  SEC="$(tr -d '\r\n' < "$LAST_TIME_FILE")"
  echo "$SEC" >> "$TIMES_FILE"
  echo "  elapsed_s=$SEC"
done

awk '
NR == 1 { min = $1; max = $1; sum = $1 }
NR > 1  {
  if ($1 < min) min = $1
  if ($1 > max) max = $1
  sum += $1
}
END {
  avg = sum / NR
  printf("Summary: runs=%d min_s=%.3f avg_s=%.3f max_s=%.3f\n", NR, min, avg, max)
}
' "$TIMES_FILE"

echo "Times file: $TIMES_FILE"
