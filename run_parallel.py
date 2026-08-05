#!/usr/bin/env python3
"""
run_parallel.py  --  Fill the Malle b-constant columns in the data files by calling
Magma only for the groups still marked \\N.

Pipeline, per degree n:
  1. Read data/degree<n>.txt, find rows whose columns are still \\N.
  2. Hand those group indices to Magma, in parallel chunks.
  3. Merge the computed values back into the data file (atomic write).

Re-running is safe and resumable: only \\N rows are ever recomputed, so an
interrupted run just picks up where it left off.

All of the mathematics lives in magma/ -- see magma/README.md. This script
knows only two things about it: how to invoke an entry point, and how to turn
(b_M, b_T, BW_lower, BW_upper) into four column values.
"""

import os
import sys
import argparse
import subprocess
import tempfile
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed

# --------------------------------------------------------------------------
# File schema  (must match the generator that created the data files)
# --------------------------------------------------------------------------
COLUMNS = [
    "label",
    "malle_b", "malle_turkelli_b", "malle_wang_b", "malle_b_status",
    "malle_b_prp", "malle_turkelli_b_prp", "malle_wang_b_prp", "malle_b_status_prp",
]
NULL = r"\N"

# Repo layout: this script lives at the repository root; magma/ and data/ are
# subdirectories of it.
REPO_ROOT = os.path.dirname(os.path.abspath(__file__))
MAGMA_DIR = os.path.join(REPO_ROOT, "magma")

# --------------------------------------------------------------------------
# Two orderings, each filling a disjoint block of four columns of the SAME
# data file.  The math (FullCheck) and the b_M/b_W/b_T -> status mapping are
# identical; only the Magma entry point, the target columns, and the
# "already computed" sentinel differ.
#
# The entry points are committed files (magma/compute_disc.m and
# magma/compute_prp.m).  They load the same lib/ modules in the same order and
# differ on exactly one line: which index file they pull in.
#
# Sentinel rule: a row is "done" iff its sentinel column is non-null.  The
# sentinel MUST be a column that is always written once a group is processed.
# That is the b_M column (always an integer); the wang and status columns can
# legitimately be \N, so they would cause endless recompute if used.
#
# Running the two orderings is fully independent: each writes only its own four
# columns and round-trips the rest, so `disc` then `prp` (or vice versa) on the
# same files is safe, in any order, and each resumes on its own sentinel.
# --------------------------------------------------------------------------
ORDERINGS = {
    "disc": {
        "cols":     ("malle_b", "malle_turkelli_b",
                     "malle_wang_b", "malle_b_status"),
        "sentinel": "malle_b",
        "entry":    "compute_disc.m",
    },
    "prp": {
        "cols":     ("malle_b_prp", "malle_turkelli_b_prp",
                     "malle_wang_b_prp", "malle_b_status_prp"),
        "sentinel": "malle_b_prp",
        "entry":    "compute_prp.m",
    },
}


# --------------------------------------------------------------------------
#  >>> THE ONE PLACE THAT ENCODES DATA SEMANTICS <<<
# --------------------------------------------------------------------------
def b_values(b_M, b_T, bw_lower, bw_upper):
    """Map a Magma FullCheck result to the four (b, turkelli_b, wang_b, status)
    column strings.  Identical for both orderings -- only which physical columns
    these land in differs (see ORDERINGS).

    FullCheck gives exact b_M, b_T, and Wang's b as a bracket [L, U] =
    [BW_lower_split, BW_upper_local], with b_M <= L <= U <= b_T.

      * b        = b_M
      * turkelli = b_T
      * wang     = b_W when the bracket collapses (L == U), else \\N
      * status   = relationship code among b_M, b_W, b_T:
              0 : b_M = b_W = b_T
              1 : b_M < b_W = b_T
              2 : b_M = b_W < b_T
              3 : b_M < b_W < b_T
             \\N : the comparison cannot be determined from [L, U]

    Each comparison is resolved independently; the status is set only when BOTH
    resolve.  This can succeed even when b_W itself is not pinned down -- e.g.
    b_M=1, b_T=5, [L,U]=[2,4] proves b_M < b_W < b_T (status 3) without knowing
    the exact value of b_W.

    Note: status code 4 (turkelli known, wang unknown) is applied downstream by
    scripts/set_status_4.py, not here.
    """
    L, U = bw_lower, bw_upper

    wang = str(L) if L == U else NULL          # exact Wang's b, or \N

    # b_M vs b_W  (b_M <= L, so L > b_M forces strict; U == b_M forces equal)
    if L > b_M:
        mw = "lt"
    elif U == b_M:
        mw = "eq"
    else:                                       # L == b_M < U : ambiguous
        mw = None

    # b_W vs b_T  (U <= b_T, so U < b_T forces strict; L == b_T forces equal)
    if U < b_T:
        wt = "lt"
    elif L == b_T:
        wt = "eq"
    else:                                       # L < U == b_T : ambiguous
        wt = None

    status = {("eq", "eq"): "0", ("lt", "eq"): "1",
              ("eq", "lt"): "2", ("lt", "lt"): "3"}.get((mw, wt), NULL)

    return [str(b_M), str(b_T), wang, status]


# --------------------------------------------------------------------------
#  Data-file I/O
# --------------------------------------------------------------------------
def read_data(path):
    """Return (header, types, rows) where rows is a list of column-lists."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().replace("\r\n", "\n").split("\n")
    if len(lines) < 2:
        raise ValueError(f"{path}: too short to be a valid data file.")
    header, types = lines[0], lines[1]
    rows = []
    for ln in lines[2:]:
        if ln.strip() == "":
            continue
        cells = ln.split("|")
        if len(cells) != len(COLUMNS):
            raise ValueError(f"{path}: row has {len(cells)} cols, expected "
                             f"{len(COLUMNS)}: {ln!r}")
        rows.append(cells)
    return header, types, rows


def write_data(path, header, types, rows):
    """Atomic rewrite: write to a temp file in the same dir, then os.replace."""
    body = [header, types, ""]
    body += ["|".join(r) for r in rows]
    text = "\n".join(body) + "\n"
    d = os.path.dirname(os.path.abspath(path))
    fd, tmp = tempfile.mkstemp(dir=d, prefix=".tmp_", suffix=".txt")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def label_index(label):
    """'12T7' -> 7."""
    return int(label.split("T", 1)[1])


def needs_compute(row, sentinel_off):
    return row[sentinel_off] == NULL


# --------------------------------------------------------------------------
#  Worker: one Magma invocation over a chunk of indices for a single degree
# --------------------------------------------------------------------------
def run_chunk(args):
    n, indices, workdir, magma, entry, magma_dir = args
    tag = f"{n}_{indices[0]}_{indices[-1]}"
    idxfile = os.path.join(workdir, f"idx_{tag}.txt")
    outfile = os.path.join(workdir, f"out_{tag}.txt")
    with open(idxfile, "w") as f:
        f.write(" ".join(map(str, indices)))

    # cwd = magma/ so that the `load "lib/..."` lines in the entry point
    # resolve.  idxfile/outfile are absolute, so they are unaffected.
    cmd = [magma, "-b", f"n:={n}",
           f"idxfile:={idxfile}", f"outfile:={outfile}", entry]
    subprocess.run(cmd, cwd=magma_dir, stdout=subprocess.DEVNULL,
                   stderr=subprocess.STDOUT, check=True)

    results = {}
    with open(outfile) as f:
        for ln in f:
            ln = ln.strip()
            if not ln or ln.startswith("index|"):
                continue
            i, bM, bT, lo, up = (int(x) for x in ln.split("|"))
            results[i] = (bM, bT, lo, up)
    return n, results


# --------------------------------------------------------------------------
#  Main
# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--data-dir", default=os.path.join(REPO_ROOT, "data"),
                    help="directory holding degree<n>.txt (default: <repo>/data)")
    ap.add_argument("--name", default="degree{n}.txt",
                    help="data filename pattern, must contain {n}")
    ap.add_argument("--degrees", default="1-47",
                    help="degrees to process, e.g. '1-47:32' = 1..47 except 32, "
                         "or '12,16,18'")
    ap.add_argument("--chunk-size", type=int, default=20,
                    help="group indices per Magma invocation (default 20)")
    ap.add_argument("--workers", type=int, default=30)
    ap.add_argument("--flush-every", type=int, default=1,
                    help="rewrite a degree's file after this many completed chunks")
    ap.add_argument("--ordering", choices=sorted(ORDERINGS), default="disc",
                    help="which block of four columns to fill: 'disc' "
                         "(discriminant ordering, first four columns) or 'prp' "
                         "(product of ramified primes, last four). Default: disc")
    ap.add_argument("--magma", default="magma")
    ap.add_argument("--magma-dir", default=MAGMA_DIR,
                    help="directory containing the Magma entry points and lib/ "
                         "(default: <repo>/magma)")
    ap.add_argument("--entry", default=None,
                    help="Magma entry point filename, relative to --magma-dir "
                         "(default depends on --ordering)")
    ap.add_argument("--workdir", default=None,
                    help="scratch dir for idx/out files (default: a temp dir)")
    ap.add_argument("--dry-run", action="store_true",
                    help="just report what's missing; don't call Magma")
    args = ap.parse_args()

    cfg = ORDERINGS[args.ordering]
    target_offsets = [COLUMNS.index(c) for c in cfg["cols"]]
    sentinel_off = COLUMNS.index(cfg["sentinel"])
    entry = args.entry or cfg["entry"]

    entry_path = os.path.join(args.magma_dir, entry)
    if not args.dry_run and not os.path.exists(entry_path):
        sys.exit(f"error: Magma entry point not found: {entry_path}")

    degrees = parse_degrees(args.degrees)
    workdir = os.path.abspath(
        args.workdir or tempfile.mkdtemp(prefix=f"{args.ordering}_work_"))
    os.makedirs(workdir, exist_ok=True)

    print(f"[cfg ] ordering={args.ordering}  columns={cfg['cols']}  "
          f"entry={entry_path}")

    # --- Load every degree, build the task list -----------------------------
    state = {}      # n -> dict(path, header, types, rows, idx_to_row)
    tasks = []      # (n, chunk_indices)
    for n in degrees:
        path = os.path.join(args.data_dir, args.name.format(n=n))
        if not os.path.exists(path):
            print(f"[warn] degree {n}: {path} not found, skipping")
            continue
        header, types, rows = read_data(path)
        idx_to_row = {label_index(r[0]): r for r in rows}
        missing = sorted(label_index(r[0]) for r in rows
                         if needs_compute(r, sentinel_off))
        state[n] = dict(path=path, header=header, types=types,
                        rows=rows, idx_to_row=idx_to_row)
        if not missing:
            print(f"[skip] degree {n}: complete ({len(rows)} groups)")
            continue
        print(f"[plan] degree {n}: {len(missing)}/{len(rows)} groups to compute")
        for c in chunked(missing, args.chunk_size):
            tasks.append((n, c))

    if args.dry_run:
        total = sum(len(c) for _, c in tasks)
        print(f"\n[dry-run] {len(tasks)} chunks, {total} groups would be computed.")
        return

    if not tasks:
        print("\nNothing to do -- all requested degrees are complete.")
        return

    # --- Run in parallel; merge + flush as chunks finish --------------------
    print(f"\nLaunching {len(tasks)} chunks on {args.workers} workers "
          f"(scratch: {workdir})\n" + "=" * 60)
    payloads = [(n, c, workdir, args.magma, entry, args.magma_dir)
                for (n, c) in tasks]
    done_chunks = defaultdict(int)
    expected = defaultdict(int)
    for n, _ in tasks:
        expected[n] += 1

    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(run_chunk, p): (p[0], p[1]) for p in payloads}
        for fut in as_completed(futs):
            n, chunk = futs[fut]
            try:
                _, results = fut.result()
            except Exception as e:
                print(f"[ERR ] degree {n} chunk {chunk[0]}..{chunk[-1]}: {e} "
                      f"(left as \\N, will retry on next run)")
                continue

            st = state[n]
            for i, (bM, bT, lo, up) in results.items():
                vals = b_values(bM, bT, lo, up)
                row = st["idx_to_row"][i]
                for off, v in zip(target_offsets, vals):
                    row[off] = v

            done_chunks[n] += 1
            if done_chunks[n] % args.flush_every == 0 or done_chunks[n] == expected[n]:
                write_data(st["path"], st["header"], st["types"], st["rows"])
            print(f"[ok  ] degree {n}: chunk {chunk[0]}..{chunk[-1]} "
                  f"({done_chunks[n]}/{expected[n]} chunks)")

    # Final safety flush
    for n, st in state.items():
        if n in done_chunks:
            write_data(st["path"], st["header"], st["types"], st["rows"])
    print("=" * 60 + "\nAll done.")


# --------------------------------------------------------------------------
#  small helpers
# --------------------------------------------------------------------------
def chunked(seq, size):
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


def parse_degrees(spec):
    """'1-47:32' -> [1..47] minus {32}; '12,16,18' -> [12,16,18]."""
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
