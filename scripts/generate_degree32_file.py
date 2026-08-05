#!/usr/bin/env python3
"""Generate degree<n>.txt containing ONLY the degree-n transitive group labels
that are present in the LMFDB (db.gps_transitive), with every b-constant column
initialised to \\N.

Motivation: degree 32 has ~2.8 million transitive groups, but only a subset are
in the LMFDB, so we cannot just enumerate 1..NumberOfTransitiveGroups(32).  We
ask the LMFDB which labels exist and write exactly those, sorted by T-number.

The LMFDB access is isolated in fetch_labels(); the formatting is pure and was
unit-tested without a database connection.
"""

import argparse

COLUMNS = ["label", "malle_b", "malle_turkelli_b", "malle_wang_b", "malle_b_status",
           "malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp",
           "malle_b_status_prp"]
HEADER = "|".join(COLUMNS)
TYPES = "text|" + "|".join(["smallint"] * (len(COLUMNS) - 1))
NULL = r"\N"


def t_number(label):
    """'32T12' -> 12 (used to sort labels numerically by T-number)."""
    return int(label.split("T", 1)[1])


def build_file_text(labels):
    """Return (text, n_rows) for the data file given an iterable of labels."""
    rows = sorted(set(labels), key=t_number)
    null_row = "|".join([NULL] * (len(COLUMNS) - 1))
    lines = [HEADER, TYPES, ""] + [f"{lab}|{null_row}" for lab in rows]
    return "\n".join(lines) + "\n", len(rows)


def fetch_labels(n, table_name, degree_col):
    """All degree-n transitive-group labels present in the LMFDB."""
    from lmfdb import db                       # lazy: only needed for a real run
    table = getattr(db, table_name)
    return [r["label"] for r in table.search({degree_col: n}, projection=["label"])]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--degree", type=int, default=32)
    ap.add_argument("--out", default=None, help="output file (default: degree<n>.txt)")
    ap.add_argument("--table", default="gps_transitive")
    ap.add_argument("--degree-col", default="n",
                    help="column holding the degree in that table (default: n)")
    args = ap.parse_args()

    out = args.out or f"degree{args.degree}.txt"
    labels = fetch_labels(args.degree, args.table, args.degree_col)
    text, count = build_file_text(labels)
    with open(out, "w") as f:
        f.write(text)
    if count:
        ts = sorted(t_number(l) for l in set(labels))
        print(f"Wrote {count} degree-{args.degree} labels to {out} "
              f"(T-numbers {ts[0]}..{ts[-1]}).")
    else:
        print(f"No degree-{args.degree} groups found in db.{args.table}; "
              f"wrote header-only {out}.")


if __name__ == "__main__":
    main()
