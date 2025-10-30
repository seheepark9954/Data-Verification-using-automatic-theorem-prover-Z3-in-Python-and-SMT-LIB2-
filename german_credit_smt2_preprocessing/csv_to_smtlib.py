#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
csv_to_smtlib.py
----------------
Convert a numeric CSV (rows = samples, columns = features) into array-based SMT-LIB v2.

- Produces:
  (set-logic QF_AUFLIRA)
  (define-fun m () Int <num_rows>)
  (define-fun n () Int <num_cols>)
  (declare-const D (Array Int (Array Int Real)))
  (define-fun rowN ((x0 Real) ... (xN-1 Real)) (Array Int Real) ...)
  (assert (= (select D i) (rowN v0 ... vN-1)))  ; for each row i

Default element sort is Real (safe for Int/Float). If you know it's all Int, you can use --force-int.
Missing cells can be filled with --fillna VALUE (default: error on missing).

Usage:
  python csv_to_smtlib.py input.csv -o output.smt2
  python csv_to_smtlib.py input.csv -o output.smt2 --symbol D --logic QF_AUFLIRA
  python csv_to_smtlib.py input.csv -o output.smt2 --fillna 0
  python csv_to_smtlib.py input.csv -o output.smt2 --no-header

Author: ChatGPT
"""
import csv
import math
import argparse
from typing import List, Tuple, Optional

def try_float(s: str) -> Optional[float]:
    try:
        # Allow empty strings to be handled by caller
        if s is None or s == "":
            return None
        return float(s)
    except ValueError:
        return None

def detect_header(first_row: List[str]) -> bool:
    """Heuristic: if every cell in first_row parses as number -> no header.
       Otherwise, assume header present.
    """
    for cell in first_row:
        if try_float(cell) is None:
            return True  # header present
    return False  # no header

def read_csv_numeric(path: str, assume_header: Optional[bool]) -> Tuple[List[List[float]], int, bool, List[str]]:
    """Return (rows, ncols, header_present, header_names). Rows is list of float lists."""
    with open(path, 'r', newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        all_rows = [row for row in reader if any(cell.strip() for cell in row)]
    if not all_rows:
        raise ValueError("CSV appears to be empty.")
    first_row = all_rows[0]

    header_present = detect_header(first_row) if assume_header is None else assume_header
    header = first_row if header_present else [f"c{i}" for i in range(len(first_row))]

    data_rows = all_rows[1:] if header_present else all_rows
    # Convert to floats (promote ints)
    numeric_rows: List[List[float]] = []
    for r_idx, row in enumerate(data_rows):
        vals: List[float] = []
        for c_idx, cell in enumerate(row):
            cell = cell.strip()
            if cell == "":
                # Missing; signal with None for now
                vals.append(float('nan'))
                continue
            num = try_float(cell)
            if num is None:
                raise ValueError(f"Non-numeric value at row {r_idx+1}{' (after header)' if header_present else ''}, col {c_idx+1}: {cell!r}")
            vals.append(num)
        numeric_rows.append(vals)

    # Normalize width to the maximum number of columns observed; fill trailing NaN if shorter rows
    max_cols = max(len(r) for r in numeric_rows) if numeric_rows else len(header)
    if header_present and len(header) < max_cols:
        # pad header auto-names for missing trailing columns
        header = list(header) + [f"c{i}" for i in range(len(header), max_cols)]
    elif not header_present:
        header = [f"c{i}" for i in range(max_cols)]

    for r in numeric_rows:
        if len(r) < max_cols:
            r += [float('nan')] * (max_cols - len(r))

    return numeric_rows, max_cols, header_present, header

def fill_na(rows: List[List[float]], fill_value: Optional[float]) -> None:
    if fill_value is None:
        # verify no NaN present
        for i, r in enumerate(rows):
            for j, v in enumerate(r):
                if isinstance(v, float) and math.isnan(v):
                    raise ValueError(f"Missing value at row {i+1}, col {j+1}. Use --fillna to supply a value.")
    else:
        for i, r in enumerate(rows):
            for j, v in enumerate(r):
                if isinstance(v, float) and math.isnan(v):
                    rows[i][j] = fill_value

def smt_escape_real(x: float) -> str:
    # Render ints as "42" and reals as e.g. "3.14"
    if math.isfinite(x) and float(x).is_integer():
        return str(int(x))
    # SMT-LIB prefers decimal (avoid scientific if possible)
    s = f"{x:.12g}"
    # Ensure decimal point if not integer representation
    if '.' not in s and 'e' not in s and 'E' not in s:
        s += ".0"
    return s

def build_row_fun(ncols: int, sort_elem: str) -> str:
    params = " ".join(f"(x{i} {sort_elem})" for i in range(ncols))
    # Build nested stores: ((as const (Array Int Real)) 0.0) then store 0..n-1
    inner = "((as const (Array Int {s})) {zero})".format(s=sort_elem, zero="0" if sort_elem=="Int" else "0.0")
    for i in range(ncols):
        inner = f"(store {inner} {i} x{i})"
    return f"(define-fun row{ncols} ({params}) (Array Int {sort_elem})\n  {inner}\n)"

def generate_smt(rows: List[List[float]], ncols: int, symbol: str, logic: str, force_int: bool, header_names: List[str]) -> str:
    nrows = len(rows)
    # Determine element sort: Int only if all numbers are integers and force_int or implied.
    def is_all_int() -> bool:
        for r in rows:
            for v in r:
                if not float(v).is_integer():
                    return False
        return True

    sort_elem = "Int" if force_int or (is_all_int() and logic.upper() != "QF_AUFLIRA") else "Real"
    # If user picked QF_AUFLIRA but asks Int, it's also fine; AUFLIRA supports Int & Real arrays.

    # Header comment
    header_comment = ["; ---- Auto-generated from CSV ----",
                      f"; rows (m) = {nrows}",
                      f"; cols (n) = {ncols}",
                      f"; column names: {', '.join(header_names)}"]

    parts = []
    parts.append(f"(set-logic {logic})")
    parts.extend(header_comment)
    parts.append("")
    parts.append("(declare-const {sym} (Array Int (Array Int {sort})))".format(sym=symbol, sort=sort_elem))
    parts.append(f"(define-fun m () Int {nrows})")
    parts.append(f"(define-fun n () Int {ncols})")
    parts.append("")
    parts.append(build_row_fun(ncols, sort_elem))
    parts.append("")

    # Row asserts
    for i, row in enumerate(rows):
        values = " ".join(smt_escape_real(v) if sort_elem=="Real" else str(int(v)) for v in row)
        parts.append(f"(assert (= (select {symbol} {i}) (row{ncols} {values})))")

    smt = "\n".join(parts) + "\n"
    return smt

def main():
    ap = argparse.ArgumentParser(description="Convert a numeric CSV to array-based SMT-LIB v2 (SMT-LIB arrays of rows).")
    ap.add_argument("input_csv", help="Path to input CSV (numeric).")
    ap.add_argument("-o", "--output", required=True, help="Output .smt2 file path.")
    ap.add_argument("--symbol", default="D", help="Dataset symbol name (default: D).")
    ap.add_argument("--logic", default="QF_AUFLIRA", help="SMT-LIB logic to set (default: QF_AUFLIRA).")
    ap.add_argument("--no-header", action="store_true", help="Treat first row as data, not header.")
    ap.add_argument("--header", action="store_true", help="Treat first row explicitly as header.")
    ap.add_argument("--fillna", type=float, default=None, help="Fill missing/blank cells with this numeric value.")
    ap.add_argument("--force-int", action="store_true", help="Force element sort to Int when all values are integral.")
    args = ap.parse_args()

    if args.header and args.no_header:
        raise SystemExit("--header and --no-header are mutually exclusive.")

    assume_header = True if args.header else (False if args.no_header else None)

    rows, ncols, header_present, header_names = read_csv_numeric(args.input_csv, assume_header)
    fill_na(rows, args.fillna)

    # If force-int requested but data has non-integers, we will still output Real (to be safe)
    # Force-int only applies when every value is an integer.
    smt_text = generate_smt(rows, ncols, symbol=args.symbol, logic=args.logic, force_int=args.force_int, header_names=header_names)

    with open(args.output, "w", encoding="utf-8") as fo:
        fo.write(smt_text)

    print(f"Wrote SMT-LIB to: {args.output}")
    print(f"m={len(rows)}, n={ncols}, symbol={args.symbol}, logic={args.logic}, header_present={header_present}")

if __name__ == "__main__":
    main()
