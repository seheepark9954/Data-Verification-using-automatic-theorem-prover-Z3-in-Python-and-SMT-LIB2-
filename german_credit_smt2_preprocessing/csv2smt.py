#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CSV (20 features + 1 label) -> SMT-LIB2 encoder
- Input : german_numeric.csv  (comma-separated, 1000x21, last col = label in {1,2})
- Output: SMT-LIB2 with D : Array Int (Array Int Real), O : Array Int Real
"""

import csv, sys, argparse, math

FEATURES = 20  # fixed for this dataset

def as_real(x: str) -> str:
    """SMT-LIB Real literal (append .0 for integers)."""
    v = x.strip()
    if v.lower() in {"nan", "inf", "+inf", "-inf"}:
        raise ValueError(f"Unsupported numeric literal: {v}")
    # allow scientific or decimal forms
    try:
        _ = float(v)
    except Exception as e:
        raise ValueError(f"Non-numeric cell: {v}") from e
    if any(c in v for c in ".eE"):
        return v
    return v + ".0"

def row_array(values):
    """Build one (Array Int Real) row via nested store; default 0.0."""
    base = "((as const (Array Int Real)) 0.0)"
    expr = base
    for j, v in enumerate(values):
        expr = f"(store {expr} {j} {v})"
    return expr

def encode(csv_path: str, out_path: str | None, limit_rows: int | None, map_label_12_to_01: bool):
    rows = []
    with open(csv_path, newline="") as f:
        rdr = csv.reader(f)
        for r in rdr:
            if not r: 
                continue
            r = [c.strip() for c in r]
            # skip empty-only lines
            if all(c == "" for c in r):
                continue
            rows.append(r)
            if limit_rows and len(rows) >= limit_rows:
                break

    if not rows:
        print("Empty CSV.", file=sys.stderr)
        sys.exit(1)

    # Validate width
    width = len(rows[0])
    if width != FEATURES + 1:
        print(f"[ERROR] Expected {FEATURES+1} columns (20 feats + 1 label), got {width}.", file=sys.stderr)
        sys.exit(2)
    for idx, r in enumerate(rows):
        if len(r) != width:
            print(f"[ERROR] Row {idx} has width {len(r)} != {width}.", file=sys.stderr)
            sys.exit(3)

    m = len(rows)
    n = FEATURES

    # Convert rows
    D_rows = []
    O_vals = []
    for r in rows:
        feats = [as_real(x) for x in r[:FEATURES]]
        lab_raw = r[FEATURES].strip()
        if map_label_12_to_01:
            if lab_raw == "1":
                lab = "1.0"
            elif lab_raw == "2":
                lab = "0.0"
            else:
                lab = as_real(lab_raw)
        else:
            lab = as_real(lab_raw)
        D_rows.append(row_array(feats))
        O_vals.append(lab)

    # Write SMT-LIB
    out = open(out_path, "w") if out_path else sys.stdout
    try:
        w = out.write
        w("(set-logic QF_AUFLIRA)\n")
        w(f"(define-fun m () Int {m})\n")
        w(f"(define-fun n () Int {n})\n")
        w("(declare-const D (Array Int (Array Int Real)))\n")
        for i, row in enumerate(D_rows):
            w(f"(assert (= (select D {i}) {row}))\n")
        # labels
        init = "((as const (Array Int Real)) 0.0)"
        arr = init
        for i, v in enumerate(O_vals):
            arr = f"(store {arr} {i} {v})"
        w("(declare-const O (Array Int Real))\n")
        w(f"(assert (= O {arr}))\n")
        # helpers
        w("(define-fun feat ((i Int) (j Int)) Real (select (select D i) j))\n")
        w("(define-fun label ((i Int)) Real (select O i))\n")
    finally:
        if out is not sys.stdout:
            out.close()

def main():
    ap = argparse.ArgumentParser(description="Encode german_numeric.csv (20 feats + 1 label) to SMT-LIB2")
    ap.add_argument("csv", help="german_numeric.csv (comma-separated)")
    ap.add_argument("-o", "--output", help="output .smt2 (default: stdout)")
    ap.add_argument("--limit-rows", type=int, default=None, help="use only first K rows (e.g., 50)")
    ap.add_argument("--label-map12-to-01", action="store_true",
                    help="map labels: 1->1.0, 2->0.0 (binary 1/0)")
    args = ap.parse_args()

    encode(args.csv, args.output, args.limit_rows, args.label_map12_to_01)

if __name__ == "__main__":
    main()