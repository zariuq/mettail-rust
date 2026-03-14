#!/usr/bin/env python3
"""Classify direct-runner PeTTa TSV results by strict failure signature.

This is intentionally stricter than a naive TSV `status == PASS` check.
Some corpus runs historically produced rows marked `PASS` while the captured
detail still contained backend/runtime errors. Progress accounting should treat
those rows as failures until the backend output is actually clean.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path


RULES: list[tuple[str, str]] = [
    ("timeout", "TIMEOUT after"),
    ("missing_file", "No such file or directory"),
    ("stack_overflow", "stack overflow"),
    ("unknown_space", "unknown space"),
    ("numeric_demand", "not a number"),
    ("numeric_float_only", "expected floating-point arguments"),
    ("unbound_rhs_vars", "unbound rhs vars"),
    ("uncertified_head", "execution contract does not certify"),
    ("scope_contract", "scope contract"),
    ("type_query", " got: Type"),
    ("unsupported_foreign", "tracking foreign import without parsing"),
    ("unsupported_import_target", "surface file import into"),
    (
        "unsupported_mm2_fragment",
        "currently supports rewrite_ir rules in the premise-free/spaceMatch fragment",
    ),
    (
        "unsupported_nested_grounded_lane",
        "currently only lowered as a top-level host I/O lane",
    ),
    (
        "unsupported_nested_grounded_lane",
        "currently only lowered as a top-level host reflection lane",
    ),
]

FAIL_SIGNALS: list[str] = [
    "TIMEOUT after",
    "[error]",
    "[FAIL]",
    'test(s) failed',
    "Error:",
    "fatal runtime error",
]


def effective_status(raw_status: str, detail: str) -> str:
    if any(signal in detail for signal in FAIL_SIGNALS):
        return "FAIL"
    return raw_status or "FAIL"


def classify(detail: str) -> str:
    for label, needle in RULES:
        if needle in detail:
            return label
    if "[FAIL]" in detail or 'test(s) failed' in detail:
        return "wrong_value"
    if "[error]" in detail:
        return "backend_error_output"
    if "Error:" in detail:
        return "other_error"
    return "other"


def first_error_line(detail: str) -> str:
    for chunk in detail.split(" ["):
        text = chunk.strip()
        if not text:
            continue
        if (
            "TIMEOUT after" in text
            or "[error]" in text
            or "Error:" in text
            or "FAIL" in text
            or "fatal runtime error" in text
        ):
            return text
    return detail.strip()


def canonical_bucket(detail: str) -> str:
    bucket = classify(detail)
    if bucket == "other":
        return "other_error"
    return bucket


def strict_pass(detail: str) -> bool:
    return not any(signal in detail for signal in FAIL_SIGNALS)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Classify PeTTa direct-runner TSV results by strict error signature."
    )
    parser.add_argument("input_tsv", type=Path)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    rows: list[dict[str, str]] = []
    with args.input_tsv.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            row = {k: (v or "") for k, v in row.items()}
            row["strict_status"] = effective_status(row.get("status", ""), row.get("detail", ""))
            if row["strict_status"] == "FAIL":
                row["error_class"] = canonical_bucket(row.get("detail", ""))
                row["first_error_line"] = first_error_line(row.get("detail", ""))
            else:
                row["error_class"] = "pass"
                row["first_error_line"] = ""
            rows.append(row)

    out_path = args.output or args.input_tsv.with_suffix(".classified.tsv")
    fieldnames = list(rows[0].keys()) if rows else [
        "file",
        "status",
        "strict_status",
        "error_class",
        "first_error_line",
    ]
    with out_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    counts = Counter(row["error_class"] for row in rows)
    strict_counts = Counter(row["strict_status"] for row in rows)
    print(f"wrote {out_path}")
    print("strict_status")
    for label, count in sorted(strict_counts.items()):
        print(f"{label}\t{count}")
    print("error_class")
    for label, count in sorted(counts.items()):
        print(f"{label}\t{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
