#!/usr/bin/env python3
"""
witnesses.py  --  compare verified witness fields with the data files.

Reads data/witnesses/verified_<ordering>.txt, written by
magma/verify_witnesses_<ordering>.m (see data/witnesses/README.md), and
classifies every witness against the stored row for its label:

  no-gain    b_witness <= b_M: proves nothing new.
  consistent b_W is stored exactly and b_witness <= b_W.
  settles    b_W is unknown and b_witness = b_T, so b_W = b_T.
  raises     b_W is unknown and b_M < b_witness < b_T: the lower bound goes
             up, but whether the bracket now closes needs the upper bound,
             which the data files do not store -- recompute the row.
  CONFLICT   b_witness exceeds a stored exact b_W or b_T, or the witness's
             b_M / b_T disagree with the stored ones.  Something is wrong,
             either in the data or in the code: investigate.
  ERROR      the Magma verification itself failed for this witness.

    python3 scripts/witnesses.py --ordering prp
    python3 scripts/witnesses.py --ordering prp --apply
    python3 scripts/witnesses.py --ordering prp --write-labels raise.txt
    python3 run_parallel.py --ordering prp --retry-unresolved --labels-file raise.txt

--apply writes only the "settles" rows (b_W := b_T, status 1, or 0 if
b_M = b_T), and writes nothing at all if there is any CONFLICT.  Exits 1 if
any CONFLICT is found.
"""

import os
import sys
import argparse
from collections import defaultdict

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)
from run_parallel import (COLUMNS, NULL, ORDERINGS, read_data, write_data,  # noqa: E402
                          b_values, load_witnesses)

WITNESS_DIR = os.path.join(REPO_ROOT, "data", "witnesses")


def verified_path(ordering, witness_dir=WITNESS_DIR):
    return os.path.join(witness_dir, f"verified_{ordering}.txt")


def classify(stored, w):
    """stored = (b_M, b_T, wang, status) strings from the data file;
    w = (b_witness, b_M, b_T, exact, source).  Returns (verdict, detail)."""
    bw, wbM, wbT, _, _ = w
    sM, sT, sW, _ = stored
    if sM == NULL or sT == NULL:
        return "not-computed", "row has no b_M/b_T yet"
    sM, sT = int(sM), int(sT)
    if (wbM, wbT) != (sM, sT):
        return "CONFLICT", (f"witness Galois group gives b_M={wbM}, b_T={wbT}; "
                            f"data file has b_M={sM}, b_T={sT}")
    if bw > sT:
        return "CONFLICT", f"b_witness={bw} > b_T={sT}"
    if bw <= sM:
        return "no-gain", f"b_witness={bw} <= b_M={sM}"
    if sW != NULL:
        if bw > int(sW):
            return "CONFLICT", f"b_witness={bw} > stored b_W={sW}"
        return "consistent", f"b_witness={bw} <= stored b_W={sW}"
    if bw == sT:
        return "settles", f"b_W = b_T = {sT}"
    return "raises", f"b_W >= {bw} (b_M={sM}, b_T={sT}); recompute to close"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ordering", choices=sorted(ORDERINGS), required=True)
    ap.add_argument("--data-dir", default=os.path.join(REPO_ROOT, "data"))
    ap.add_argument("--witness-dir", default=WITNESS_DIR)
    ap.add_argument("--apply", action="store_true",
                    help="write b_W = b_T for every 'settles' row")
    ap.add_argument("--write-labels", default=None, metavar="PATH",
                    help="write the 'raises' labels to PATH, one per line, for "
                         "run_parallel.py --retry-unresolved --labels-file")
    args = ap.parse_args()

    cfg = ORDERINGS[args.ordering]
    offs = [COLUMNS.index(c) for c in cfg["cols"]]
    best, errors = load_witnesses(verified_path(args.ordering, args.witness_dir))
    if not best and not errors:
        print(f"No verified witnesses for the {args.ordering} ordering "
              f"(run magma/verify_witnesses_{args.ordering}.m first).")
        return

    by_degree = defaultdict(list)
    for label in set(best) | set(errors):
        by_degree[int(label.split("T", 1)[0])].append(label)

    tally = defaultdict(int)
    raise_labels = []
    pending = []          # (path, header, types, rows) to write if --apply
    for n in sorted(by_degree):
        path = os.path.join(args.data_dir, f"degree{n}.txt")
        if not os.path.exists(path):
            for label in by_degree[n]:
                print(f"[MISSING ] {label}: {path} not found")
                tally["missing"] += 1
            continue
        header, types, rows = read_data(path)
        idx = {r[0]: r for r in rows}
        changed = False
        for label in sorted(by_degree[n], key=lambda s: int(s.split("T", 1)[1])):
            for msg in errors.get(label, []):
                print(f"[ERROR   ] {label}: {msg}")
                tally["ERROR"] += 1
            if label not in best:
                continue
            row = idx.get(label)
            if row is None:
                print(f"[MISSING ] {label}: no such row in {path}")
                tally["missing"] += 1
                continue
            stored = [row[o] for o in offs]
            verdict, detail = classify(stored, best[label])
            tally[verdict] += 1
            print(f"[{verdict:<9}] {label} ({best[label][4]}): {detail}")
            if verdict == "raises":
                raise_labels.append(label)
            if verdict == "settles" and args.apply:
                bM, bT = int(stored[0]), int(stored[1])
                vals = b_values(bM, bT, bT, bT)
                for o, v in zip(offs, vals):
                    row[o] = v
                changed = True
        if changed:
            pending.append((path, header, types, rows))

    if args.write_labels is not None:
        with open(args.write_labels, "w", encoding="utf-8") as fh:
            fh.write("".join(f"{lab}\n" for lab in raise_labels))
        print(f"\nWrote {len(raise_labels)} label(s) to {args.write_labels}")

    if args.apply:
        if tally.get("CONFLICT"):
            print("\n--apply: NOTHING written, because there are conflicts. "
                  "Resolve them first.")
        else:
            for path, header, types, rows in pending:
                write_data(path, header, types, rows)
            print(f"\n--apply: wrote {tally.get('settles', 0)} row(s) in "
                  f"{len(pending)} file(s).")

    print("\n" + ", ".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if tally.get("CONFLICT"):
        sys.exit(1)


if __name__ == "__main__":
    main()
