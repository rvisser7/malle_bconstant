#!/usr/bin/env python3
"""
set_status_4.py  --  apply status code 4 to the data files.

run_parallel.py sets malle_b_status from the relationship between b_M, b_W and
b_T, and leaves it \\N when the bracket [L, U] settles neither comparison. That
is a different thing from "we know Turkelli's constant but not Wang's", which
is the case the LMFDB display wants to distinguish, so the convention adds

    4 : malle_turkelli_b is known, malle_wang_b is not

This script is the downstream pass that run_parallel.py's b_values() docstring
refers to. It was referenced but never committed, so it is written here.

A row is given status 4, in a given ordering block, exactly when

    malle_turkelli_b  is not \\N
    malle_wang_b      is     \\N
    malle_b_status    is     \\N

Codes 0-3 are never overwritten: 3 in particular is legitimately set while
malle_wang_b is still \\N, since [L, U] can prove b_M < b_W < b_T without
pinning b_W down.

Usage:
    python3 scripts/set_status_4.py --dry-run
    python3 scripts/set_status_4.py
    python3 scripts/set_status_4.py --ordering prp
"""

import argparse
import os
import sys
import tempfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR = os.path.join(REPO_ROOT, "data")
NULL = r"\N"

COLUMNS = [
    "label",
    "malle_b", "malle_turkelli_b", "malle_wang_b", "malle_b_status",
    "malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp", "malle_b_status_prp",
]

BLOCKS = {
    "disc": ("malle_turkelli_b", "malle_wang_b", "malle_b_status"),
    "prp":  ("malle_turkelli_b_prp", "malle_wang_b_prp", "malle_b_status_prp"),
}


def read_data(path):
    with open(path, encoding="utf-8") as f:
        lines = f.read().replace("\r\n", "\n").split("\n")
    header, types = lines[0], lines[1]
    rows = []
    for ln in lines[2:]:
        if ln.strip() == "":
            continue
        cells = ln.split("|")
        if len(cells) != len(COLUMNS):
            raise ValueError("%s: row has %d cols, expected %d: %r"
                             % (path, len(cells), len(COLUMNS), ln))
        rows.append(cells)
    return header, types, rows


def write_data(path, header, types, rows):
    text = "\n".join([header, types, ""] + ["|".join(r) for r in rows]) + "\n"
    d = os.path.dirname(os.path.abspath(path))
    fd, tmp = tempfile.mkstemp(dir=d, prefix=".tmp_", suffix=".txt")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data-dir", default=DATA_DIR)
    ap.add_argument("--ordering", choices=["disc", "prp", "both"], default="both")
    ap.add_argument("--min-degree", type=int, default=1)
    ap.add_argument("--max-degree", type=int, default=47)
    ap.add_argument("--dry-run", action="store_true",
                    help="report what would change and write nothing")
    args = ap.parse_args()

    blocks = list(BLOCKS) if args.ordering == "both" else [args.ordering]
    offsets = {name: COLUMNS.index(name) for name in COLUMNS}

    grand = 0
    for n in range(args.min_degree, args.max_degree + 1):
        path = os.path.join(args.data_dir, "degree%d.txt" % n)
        if not os.path.exists(path):
            continue
        header, types, rows = read_data(path)

        changed = 0
        for r in rows:
            for block in blocks:
                tcol, wcol, scol = (offsets[c] for c in BLOCKS[block])
                if r[tcol] != NULL and r[wcol] == NULL and r[scol] == NULL:
                    r[scol] = "4"
                    changed += 1

        grand += changed
        if changed:
            print("degree %2d: %6d cells set to 4%s"
                  % (n, changed, " (dry run)" if args.dry_run else ""))
            if not args.dry_run:
                write_data(path, header, types, rows)

    print("\n%d cells%s" % (grand, " would be set" if args.dry_run else " set"),
          file=sys.stderr)


if __name__ == "__main__":
    main()
