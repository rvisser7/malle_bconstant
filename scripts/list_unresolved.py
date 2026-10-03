#!/usr/bin/env python3
"""
list_unresolved.py  --  list the groups whose b_M and b_T are computed but
whose Wang b_W is still \\N, in one or both orderings.

    python3 scripts/list_unresolved.py                      # disc ordering, all degrees
    python3 scripts/list_unresolved.py --ordering prp --degrees 20-24
    python3 scripts/list_unresolved.py --ordering both --summary
    python3 scripts/list_unresolved.py --labels-only > todo.txt
    python3 run_parallel.py --retry-unresolved --labels-file todo.txt

Default output is one line per group, label|b_M|b_T|gap|status, sorted by
degree and index, where gap = b_T - b_M is the width of the range b_W can
still lie in.  --labels-only prints bare labels, in the format
run_parallel.py --labels-file and the Magma diagnostics expect.
"""

import os
import sys
import argparse

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)
from run_parallel import COLUMNS, NULL, ORDERINGS, read_data, parse_degrees  # noqa: E402


def unresolved_rows(path, ordering):
    """Yield (label, b_M, b_T, status) for rows of one ordering where b_M and
    b_T are filled in but b_W is \\N."""
    _, _, rows = read_data(path)
    bm, bt, bw, st = (COLUMNS.index(c) for c in ORDERINGS[ordering]["cols"])
    for r in rows:
        if r[bm] != NULL and r[bt] != NULL and r[bw] == NULL:
            yield r[0], int(r[bm]), int(r[bt]), r[st]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ordering", choices=sorted(ORDERINGS) + ["both"], default="disc")
    ap.add_argument("--degrees", default="1-47",
                    help="e.g. '1-47:32' (1..47 except 32) or '20,24'; default 1-47")
    ap.add_argument("--data-dir", default=os.path.join(REPO_ROOT, "data"))
    ap.add_argument("--name", default="degree{n}.txt")
    ap.add_argument("--min-gap", type=int, default=1,
                    help="only groups with b_T - b_M >= this (default 1)")
    ap.add_argument("--labels-only", action="store_true",
                    help="print bare labels only (for --labels-file)")
    ap.add_argument("--summary", action="store_true",
                    help="print counts per degree instead of the list")
    args = ap.parse_args()

    orderings = sorted(ORDERINGS) if args.ordering == "both" else [args.ordering]
    for ordering in orderings:
        per_degree = {}
        listing = []
        for n in parse_degrees(args.degrees):
            path = os.path.join(args.data_dir, args.name.format(n=n))
            if not os.path.exists(path):
                continue
            hits = [h for h in unresolved_rows(path, ordering)
                    if h[2] - h[1] >= args.min_gap]
            if hits:
                per_degree[n] = len(hits)
                listing.extend(hits)

        if args.summary:
            print(f"# {ordering} ordering: b_M, b_T known, b_W = \\N")
            for n, c in per_degree.items():
                print(f"{n:>4}  {c}")
            print(f"total {sum(per_degree.values())}")
            continue
        if not args.labels_only:
            print(f"# {ordering} ordering: label|b_M|b_T|gap|status")
        for label, bM, bT, st in listing:
            if args.labels_only:
                print(label)
            else:
                print(f"{label}|{bM}|{bT}|{bT - bM}|{st}")


if __name__ == "__main__":
    main()
