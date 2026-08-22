#!/usr/bin/env python3
"""Report how many entries still need computing in each b-constant column,
per degree, across the data files (default name pattern: degree<n>.txt).

This is pure local-file analysis -- no LMFDB connection is needed. For each
degree it counts, per column, how many rows are still \\N.

Note on the Wang columns: malle_b and malle_turkelli_b are always written
together the moment a group is computed, so their \\N counts equal the number
of groups not yet computed in that ordering. malle_wang_b can additionally be
\\N as a *final* result (Wang's b undetermined), so its \\N count may exceed the
real "still to compute" number. The actionable per-ordering remaining count is
therefore the malle_b (resp. malle_b_prp) column.
"""

import os
import argparse

# scripts/ lives one level below the repo root; the data files are in data/.
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR = os.path.join(REPO_ROOT, "data")

COLUMNS = ["label", "malle_b", "malle_turkelli_b", "malle_wang_b", "malle_b_status",
           "malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp",
           "malle_b_status_prp"]
NULL = r"\N"

# The six b-constant value columns shown in the table, grouped by ordering.
DISC_COLS = ["malle_b", "malle_turkelli_b", "malle_wang_b"]
PRP_COLS = ["malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp"]
VALUE_COLS = DISC_COLS + PRP_COLS
SENTINEL = {"disc": "malle_b", "prp": "malle_b_prp"}


def count_file(path):
    """Return (n_rows, {column: count_of_\\N}) for one data file."""
    counts = {c: 0 for c in COLUMNS[1:]}
    total = 0
    with open(path) as f:
        lines = f.read().split("\n")
    for ln in lines[2:]:                       # skip header + types lines
        if ln.strip() == "":
            continue
        cells = ln.split("|")
        if len(cells) != len(COLUMNS):
            raise ValueError(f"{path}: row has {len(cells)} cols, expected "
                             f"{len(COLUMNS)}: {ln!r}")
        total += 1
        for c, v in zip(COLUMNS[1:], cells[1:]):
            if v == NULL:
                counts[c] += 1
    return total, counts


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data-dir", default=DATA_DIR,
                    help="folder holding the degree<n>.txt files "
                         "(default: the repo's data/ folder)")
    ap.add_argument("--name", default="degree{n}.txt",
                    help="data filename pattern, must contain {n} "
                         "(default: degree{n}.txt)")
    ap.add_argument("--min-degree", type=int, default=1)
    ap.add_argument("--max-degree", type=int, default=47)
    ap.add_argument("--pending-only", action="store_true",
                    help="show only degrees with work remaining")
    args = ap.parse_args()

    # Column layout for the table.
    short = {"malle_b": "malle", "malle_turkelli_b": "turk", "malle_wang_b": "wang",
             "malle_b_prp": "malle", "malle_turkelli_b_prp": "turk",
             "malle_wang_b_prp": "wang"}
    w = 8  # numeric column width

    def hr(ch="-"):
        return ch * (6 + 9 + 1 + 3 * w + 3 + 3 * w)

    # Header: two rows, grouping disc vs prp.
    print(f"Remaining \\N entries per b-constant column "
          f"(file pattern: {args.name})")
    print(f"Data folder: {os.path.abspath(args.data_dir)}\n")
    grp = (f"{'':>6}{'':>9} | {'discriminant order':^{3*w}} | "
           f"{'prod. ramified primes':^{3*w}}")
    print(grp)
    cols = (f"{'deg':>6}{'groups':>9} | "
            + "".join(f"{short[c]:>{w}}" for c in DISC_COLS) + " | "
            + "".join(f"{short[c]:>{w}}" for c in PRP_COLS))
    print(cols)
    print(hr())

    totals = {c: 0 for c in VALUE_COLS}
    total_groups = 0
    missing = []

    for n in range(args.min_degree, args.max_degree + 1):
        path = os.path.join(args.data_dir, args.name.format(n=n))
        if not os.path.exists(path):
            missing.append(n)
            continue
        rows, counts = count_file(path)
        total_groups += rows
        for c in VALUE_COLS:
            totals[c] += counts[c]

        pending = any(counts[c] for c in VALUE_COLS)
        if args.pending_only and not pending:
            continue

        line = (f"{n:>6}{rows:>9} | "
                + "".join(f"{counts[c]:>{w}}" for c in DISC_COLS) + " | "
                + "".join(f"{counts[c]:>{w}}" for c in PRP_COLS))
        print(line + ("" if pending else "   (complete)"))

    print(hr())
    tline = (f"{'TOTAL':>6}{total_groups:>9} | "
             + "".join(f"{totals[c]:>{w}}" for c in DISC_COLS) + " | "
             + "".join(f"{totals[c]:>{w}}" for c in PRP_COLS))
    print(tline)

    # Actionable summary (sentinel-based).
    disc_remaining = totals[SENTINEL["disc"]]
    prp_remaining = totals[SENTINEL["prp"]]
    print(f"\nGroups still to compute:  discriminant order = {disc_remaining}, "
          f"product of ramified primes = {prp_remaining}.")
    print("(= the 'malle' column in each block; the 'wang' column may be larger "
          "because an\n undetermined Wang's b is a final \\N, not pending work.)")
    if missing:
        rng = ", ".join(map(str, missing))
        print(f"\nNo data file found for degree(s): {rng}")


if __name__ == "__main__":
    main()
