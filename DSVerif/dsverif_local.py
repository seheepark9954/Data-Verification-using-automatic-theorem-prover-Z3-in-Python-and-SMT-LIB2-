#!/usr/bin/env python3
# Mini DSVerif runner: CSV + properties -> Z3
# - The last column = label (cast to Int), the others = features (Real)
# - D: (Array Int (Array Int Real))  with  D[i][j] = features[i][j]
# - O: (Array Int Int)               with  O[i]     = label[i]
# - m = number of samples, n = number of features, l/L = number of classes (injected as constants)
# - If a property file has no set-logic, default to AUFLIRA

import argparse, csv, glob, os
from z3 import Solver, Z3Exception

def load_dataset(csv_path):
    """Read CSV -> (features, labels). Features are floats, label is rounded to int."""
    feats, labels = [], []
    with open(csv_path) as f:
        rdr = csv.reader(f)
        for line_no, row in enumerate(rdr, 1):
            row = [x.strip() for x in row if x.strip() != ""]
            if not row:
                continue
            try:
                nums = [float(x) for x in row]
            except ValueError as e:
                raise RuntimeError(f"[CSV parse] line {line_no}: {row} -> {e}")
            *xs, y = nums
            feats.append(xs)
            labels.append(int(round(y)))  # label as integer
    if not feats:
        raise RuntimeError(f"No data in {csv_path}")
    d0 = len(feats[0])
    for i, r in enumerate(feats):
        if len(r) != d0:
            raise RuntimeError(f"Row {i} feature length {len(r)} != {d0}")
    return feats, labels

def smt_row_array(vals):
    """Build SMT-LIB array literal (Array Int Real) using nested store from a list of numbers."""
    base = "((as const (Array Int Real)) 0.0)"
    expr = base
    for j, v in enumerate(vals):
        sv = f"{v:.12g}"
        if "." not in sv and "e" not in sv and "E" not in sv:
            sv += ".0"
        expr = f"(store {expr} {j} {sv})"
    return expr

def smt_define_data(features, labels):
    """Emit SMT-LIB assertions to define D and O from Python lists."""
    # Inject D
    lines = ["(declare-const D (Array Int (Array Int Real)))"]
    for i, row in enumerate(features):
        lines.append(f"(assert (= (select D {i}) {smt_row_array(row)}))")
    # Inject O (labels)
    lines.append("(declare-const O (Array Int Int))")
    for i, y in enumerate(labels):
        lines.append(f"(assert (= (select O {i}) {y}))")
    return "\n".join(lines) + "\n"

def make_prelude(m, n, classes, prop_txt):
    """Emit constants m,n,l/L and default min/max/d only if not defined in the property."""
    pre = [
        f"(define-fun m () Int {m})",
        f"(define-fun n () Int {n})",
        f"(define-fun l () Int {classes})",
        f"(define-fun L () Int {classes})",  # in case a property refers to uppercase L as a count
    ]
    def not_defined(name: str) -> bool:
        t = prop_txt
        return (f"(define-fun {name} " not in t) and (f"(declare-const {name} " not in t)
    if not_defined("min"): pre.append("(define-fun min () Real (- 1.0))")
    if not_defined("max"): pre.append("(define-fun max () Real 1.0)")
    if not_defined("d"):   pre.append("(define-fun d () Real 1.0)")
    return "\n".join(pre) + "\n"

def maybe_add_logic(prop_txt: str) -> str:
    """Add a default logic header if the property file doesn't provide one."""
    return "" if "(set-logic" in prop_txt else "(set-logic AUFLIRA)\n"

def main():
    ap = argparse.ArgumentParser(description="Mini DSVerif runner with Z3")
    ap.add_argument("--csv", default="dataset.csv")
    ap.add_argument("--props", default="properties")
    ap.add_argument("--prop", help="run a single property (e.g., properties/min_max)")
    args = ap.parse_args()

    feats, labels = load_dataset(args.csv)
    m, n = len(feats), len(feats[0])
    classes = len(set(labels))

    data_blob = smt_define_data(feats, labels)

    targets = [args.prop] if args.prop else sorted(
        p for p in glob.glob(os.path.join(args.props, "*")) if os.path.isfile(p)
    )
    if not targets:
        print(f"[WARN] No property files found in '{args.props}'"); return

    for pf in targets:
        try:
            prop_txt = open(pf, "r").read()
        except Exception as e:
            print(f"{pf}: READ ERROR -> {e}"); continue

        s = Solver()
        blob = maybe_add_logic(prop_txt) + make_prelude(m, n, classes, prop_txt) + data_blob + prop_txt + "\n(check-sat)"
        try:
            s.from_string(blob)
        except Z3Exception as e:
            print(f"{pf}: PARSE ERROR -> {e}"); continue

        res = s.check()
        print(f"{pf}: {res}")

if __name__ == "__main__":
    main()
