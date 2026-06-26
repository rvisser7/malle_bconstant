#!/usr/bin/env python3
"""
check_against_lmfdb.py  --  Cross-check the generated b-constant data files
against what is already in the LMFDB (db.gps_transitive).

For every (label, column) cell it classifies the datum as:
  * only in our files   (we have a value, LMFDB has NULL / no such column)
  * only in the LMFDB   (LMFDB has a value, our file has \\N)
  * in both, agreeing
  * in both, DISAGREEING  <-- the critical case; logged loudly + nonzero exit

A cell counts as "present" in a file when it is not \\N, and "present" in the
LMFDB when the column exists and the value is not None.  (\\N in malle_wang_b /
malle_b_status is a legitimate "undetermined" result, so it is treated as
"no concrete value to compare" rather than agreement.)

The LMFDB access is isolated in fetch_lmfdb_degree(); everything else is pure
and unit-testable without a database connection.
"""

import os
import re
import sys
import glob
import argparse
from dataclasses import dataclass, field

BCOLS = ["malle_b", "malle_turkelli_b", "malle_wang_b", "malle_b_status",
         "malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp",
         "malle_b_status_prp"]
COLUMNS = ["label"] + BCOLS
NULL = r"\N"


# --------------------------------------------------------------------------
#  Pure helpers (no LMFDB dependency)
# --------------------------------------------------------------------------
def parse_file(path):
    """Return {label: {col: int|None}} for a single malle_b_<n>.txt file."""
    with open(path) as f:
        lines = f.read().split("\n")
    rows = {}
    for ln in lines[2:]:                      # skip header + types lines
        if ln.strip() == "":
            continue
        cells = ln.split("|")
        if len(cells) != len(COLUMNS):
            raise ValueError(f"{path}: row has {len(cells)} cols, expected "
                             f"{len(COLUMNS)}: {ln!r}")
        label = cells[0]
        rows[label] = {c: (None if v == NULL else int(v))
                       for c, v in zip(BCOLS, cells[1:])}
    return rows


def find_files(data_dir, name_pattern):
    """Map degree -> path for every file matching the name pattern."""
    rx = re.compile("^" + re.escape(name_pattern).replace(r"\{n\}", r"(\d+)") + "$")
    out = {}
    for p in sorted(glob.glob(os.path.join(data_dir, "*"))):
        m = rx.match(os.path.basename(p))
        if m:
            out[int(m.group(1))] = p
    return out


@dataclass
class ColStat:
    only_files: int = 0
    only_lmfdb: int = 0
    agree: int = 0
    disagree: list = field(default_factory=list)   # (label, file_val, lmfdb_val)

    def merge(self, other):
        self.only_files += other.only_files
        self.only_lmfdb += other.only_lmfdb
        self.agree += other.agree
        self.disagree.extend(other.disagree)


def compare_degree(file_rows, lmfdb_rows):
    """Compare one degree. file_rows/lmfdb_rows are {label: {col: int|None}}.

    LMFDB rows need only contain the columns that actually exist; a missing key
    is read as None (i.e. LMFDB has no value for that cell).
    """
    stats = {c: ColStat() for c in BCOLS}
    labels_f, labels_l = set(file_rows), set(lmfdb_rows)
    only_f_labels = labels_f - labels_l
    only_l_labels = labels_l - labels_f

    for label in labels_f & labels_l:
        fv, lv = file_rows[label], lmfdb_rows[label]
        for c in BCOLS:
            f, l = fv.get(c), lv.get(c)
            if f is None and l is None:
                continue
            if f is not None and l is None:
                stats[c].only_files += 1
            elif f is None and l is not None:
                stats[c].only_lmfdb += 1
            elif f == l:
                stats[c].agree += 1
            else:
                stats[c].disagree.append((label, f, l))

    # Cells belonging to labels present on only one side are "only there".
    for label in only_f_labels:
        for c in BCOLS:
            if file_rows[label].get(c) is not None:
                stats[c].only_files += 1
    for label in only_l_labels:
        for c in BCOLS:
            if lmfdb_rows[label].get(c) is not None:
                stats[c].only_lmfdb += 1

    return stats, only_f_labels, only_l_labels


# --------------------------------------------------------------------------
#  LMFDB access (isolated so the rest stays testable)
# --------------------------------------------------------------------------
def get_table(table_name):
    from lmfdb import db                      # lazy: only needed for a real run
    return getattr(db, table_name)


def lmfdb_columns(table):
    """The set of column names that actually exist on the table."""
    ct = getattr(table, "col_type", None)
    if isinstance(ct, dict):
        return set(ct)
    cols = set(getattr(table, "search_cols", []) or [])
    cols |= set(getattr(table, "extra_cols", []) or [])
    return cols


def fetch_lmfdb_degree(table, n, present_bcols, degree_col):
    """Return {label: {col: value|None}} for all groups of degree n."""
    proj = ["label"] + list(present_bcols)
    rows = {}
    for r in table.search({degree_col: n}, projection=proj):
        rows[r["label"]] = {c: r.get(c) for c in present_bcols}
    return rows


# --------------------------------------------------------------------------
#  Reporting
# --------------------------------------------------------------------------
def print_report(global_stats, only_f_total, only_l_total, present_bcols, log_path):
    missing_cols = [c for c in BCOLS if c not in present_bcols]
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    if missing_cols:
        print("Columns not (yet) present in the LMFDB table -- every value we "
              "have for these is necessarily 'only in files':")
        print("   " + ", ".join(missing_cols))
    if only_f_total:
        print(f"\nGroup labels in our files but absent from the LMFDB table: "
              f"{len(only_f_total)}")
    if only_l_total:
        print(f"Group labels in the LMFDB table but with no file row: "
              f"{len(only_l_total)}")

    print(f"\n{'column':<22}{'only files':>12}{'only lmfdb':>12}"
          f"{'agree':>10}{'DISAGREE':>10}")
    print("-" * 66)
    total_disagree = 0
    for c in BCOLS:
        s = global_stats[c]
        total_disagree += len(s.disagree)
        print(f"{c:<22}{s.only_files:>12}{s.only_lmfdb:>12}"
              f"{s.agree:>10}{len(s.disagree):>10}")

    if total_disagree == 0:
        print("\nNo disagreements. Every overlapping cell matches. \u2713")
        return 0

    # ---- the critical case -------------------------------------------------
    print("\n" + "!" * 70)
    print(f"!!!  CRITICAL: {total_disagree} cell(s) DISAGREE between files and "
          f"LMFDB  !!!")
    print("!" * 70)
    with open(log_path, "w") as log:
        log.write("column|label|file_value|lmfdb_value\n")
        for c in BCOLS:
            for (label, f, l) in global_stats[c].disagree:
                line = f"{c}|{label}|{f}|{l}"
                print("   MISMATCH  " + line)
                log.write(line + "\n")
    print(f"\nFull mismatch list written to: {log_path}")
    return 1


# --------------------------------------------------------------------------
#  Main
# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data-dir", default="../malle_new_product2")
    ap.add_argument("--name", default="degree{n}.txt",
                    help="data filename pattern, must contain {n}")
    ap.add_argument("--degrees", default=None,
                    help="optional filter, e.g. '1-19,23,25,28'; default: all "
                         "files found")
    ap.add_argument("--table", default="gps_transitive",
                    help="LMFDB table name (default: gps_transitive)")
    ap.add_argument("--degree-col", default="n",
                    help="column holding the degree in that table (default: n)")
    ap.add_argument("--log", default="bconstant_mismatches.log")
    args = ap.parse_args()

    files = find_files(args.data_dir, args.name)
    if args.degrees:
        wanted = set(parse_degrees(args.degrees))
        files = {n: p for n, p in files.items() if n in wanted}
    if not files:
        print("No data files found.")
        return 0

    table = get_table(args.table)
    present_bcols = [c for c in BCOLS if c in lmfdb_columns(table)]
    print(f"Comparing {len(files)} file(s) against db.{args.table}.")
    print(f"b-columns present in LMFDB: {present_bcols or '(none yet)'}")

    global_stats = {c: ColStat() for c in BCOLS}
    only_f_total, only_l_total = set(), set()

    for n in sorted(files):
        file_rows = parse_file(files[n])
        lmfdb_rows = fetch_lmfdb_degree(table, n, present_bcols, args.degree_col)
        stats, of, ol = compare_degree(file_rows, lmfdb_rows)
        for c in BCOLS:
            global_stats[c].merge(stats[c])
        only_f_total |= {f"{n}:{x}" for x in of}
        only_l_total |= {f"{n}:{x}" for x in ol}
        nd = sum(len(stats[c].disagree) for c in BCOLS)
        flag = f"  <-- {nd} DISAGREE" if nd else ""
        print(f"  degree {n:>2}: {len(file_rows)} file rows, "
              f"{len(lmfdb_rows)} lmfdb rows{flag}")

    rc = print_report(global_stats, only_f_total, only_l_total,
                      present_bcols, args.log)
    sys.exit(rc)


def parse_degrees(spec):
    spec, _, excl = spec.partition(":")
    excluded = {int(x) for x in excl.split(",") if x.strip()} if excl else set()
    out = []
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-")
            out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return [d for d in out if d not in excluded]


if __name__ == "__main__":
    main()
