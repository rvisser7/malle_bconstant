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

With --verify it instead recomputes rows that are ALREADY filled in, as if the
data files were empty, and reports every cell where the fresh value disagrees
with what is on disk. Nothing is written in this mode. Use --verify-sample to
spot-check a random subset rather than all 512,614 rows.

All of the mathematics lives in magma/ -- see magma/README.md. This script
knows only two things about it: how to invoke an entry point, and how to turn
(b_M, b_T, BW_lower, BW_upper) into four column values.
"""

import os
import sys
import argparse
import subprocess
import random
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


def compare_row(label, old, new, colnames):
    """Compare four stored strings against four freshly computed ones.

    Returns (verdict, detail) where verdict is one of:
      "match"    -- every cell agrees
      "new"      -- every stored cell was \\N, so there was nothing to check
      "mismatch" -- at least one stored non-null cell disagrees

    A stored \\N against a computed value is NOT a mismatch: it just means that
    cell had never been computed. A stored value against a computed \\N IS a
    mismatch -- we used to be able to determine it and now cannot.
    """
    if all(o == NULL for o in old):
        return "new", ""
    bad = [(c, o, n) for c, o, n in zip(colnames, old, new)
           if o != NULL and o != n]
    if not bad:
        return "match", ""
    detail = "; ".join(f"{c}: file={o} computed={n}" for c, o, n in bad)
    return "mismatch", f"{label}  {detail}"


# --------------------------------------------------------------------------
#  Worker: one Magma invocation over a chunk of indices for a single degree
# --------------------------------------------------------------------------
def run_chunk(args):
    n, indices, workdir, magma, entry, magma_dir, timeout = args
    tag = f"{n}_{indices[0]}_{indices[-1]}"
    idxfile = os.path.join(workdir, f"idx_{tag}.txt")
    outfile = os.path.join(workdir, f"out_{tag}.txt")
    with open(idxfile, "w") as f:
        f.write(" ".join(map(str, indices)))

    # cwd = magma/ so that the `load "lib/..."` lines in the entry point
    # resolve.  idxfile/outfile are absolute, so they are unaffected.
    cmd = [magma, "-b", f"n:={n}",
           f"idxfile:={idxfile}", f"outfile:={outfile}", entry]
    proc = subprocess.run(cmd, cwd=magma_dir, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                          text=True, timeout=timeout)

    # Magma exits 0 even when a script raises, so a nonzero code is not the
    # only failure mode -- a missing output file is the real signal.  Either
    # way, surface what Magma actually said instead of swallowing it.
    if proc.returncode != 0 or not os.path.exists(outfile):
        why = (f"exit code {proc.returncode}" if proc.returncode != 0
               else "produced no output file")
        out = (proc.stdout or "").strip()
        tail = "\n".join(out.splitlines()[-15:]) if out else "(no output)"

        # A specific failure worth naming: if the entry point's `assigned
        # outfile` test does not see the command-line variable, Magma silently
        # falls back to its default filename in the cwd and computes every
        # group of the degree rather than our chunk.  Everything looks healthy
        # in Magma's own output; only the missing file gives it away.
        hint = ""
        stray = os.path.join(magma_dir, f"bconst_results_{n}.txt")
        if os.path.exists(stray):
            hint = (f"\n    NOTE: {stray} exists. Magma ignored outfile:= and "
                    f"wrote its\n          default filename instead, which "
                    f"means the `assigned` tests in\n          the entry point "
                    f"are not seeing the command-line variables.\n"
                    f"          The CLI block must be at TOP LEVEL, not inside "
                    f"a procedure.")

        raise RuntimeError(
            f"Magma {why}.\n"
            f"    command: {' '.join(cmd)}\n"
            f"    cwd:     {magma_dir}\n"
            f"    --- last lines of Magma output ---\n{tail}{hint}")

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
    ap.add_argument("--timeout", type=float, default=None, metavar="SEC",
                    help="kill a Magma chunk after this many seconds; the rows "
                         "stay \\N and are retried next run (default: no limit)")
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

    grp = ap.add_argument_group("verification")
    grp.add_argument("--verify", action="store_true",
                     help="recompute rows that are ALREADY filled in, as if the "
                          "data files were empty, and report disagreements. "
                          "Writes nothing; exits 1 if any mismatch is found.")
    grp.add_argument("--verify-sample", type=int, default=None, metavar="K",
                     help="with --verify, check a random sample of K groups per "
                          "degree instead of all of them")
    grp.add_argument("--seed", type=int, default=0,
                     help="random seed for --verify-sample (default 0, so the "
                          "same sample is reproducible)")
    grp.add_argument("--mismatch-log", default="bconstant_mismatches.log",
                     help="where to write mismatches found by --verify")
    args = ap.parse_args()

    if args.verify_sample is not None and not args.verify:
        ap.error("--verify-sample only makes sense with --verify")

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
        state[n] = dict(path=path, header=header, types=types,
                        rows=rows, idx_to_row=idx_to_row)

        if args.verify:
            # Ignore the sentinel entirely: recompute as if nothing were filled
            # in. Rows that really are all \N still get computed; they simply
            # report as "new" rather than as agreeing or disagreeing.
            targets = sorted(idx_to_row)
            if args.verify_sample is not None and args.verify_sample < len(targets):
                targets = sorted(random.Random(args.seed + n)
                                 .sample(targets, args.verify_sample))
                print(f"[plan] degree {n}: verifying a sample of "
                      f"{len(targets)}/{len(rows)} groups")
            else:
                print(f"[plan] degree {n}: verifying all {len(targets)} groups")
        else:
            targets = sorted(label_index(r[0]) for r in rows
                             if needs_compute(r, sentinel_off))
            if not targets:
                print(f"[skip] degree {n}: complete ({len(rows)} groups)")
                continue
            print(f"[plan] degree {n}: {len(targets)}/{len(rows)} groups to compute")

        for c in chunked(targets, args.chunk_size):
            tasks.append((n, c))

    if args.dry_run:
        total = sum(len(c) for _, c in tasks)
        verb = "verified" if args.verify else "computed"
        print(f"\n[dry-run] {len(tasks)} chunks, {total} groups would be {verb}.")
        return

    if not tasks:
        print("\nNothing to do -- all requested degrees are complete.")
        return

    # --- Run in parallel; merge + flush as chunks finish --------------------
    mode = "VERIFY (nothing will be written)" if args.verify else "fill"
    print(f"\nLaunching {len(tasks)} chunks on {args.workers} workers "
          f"[{mode}]\n(scratch: {workdir})\n" + "=" * 60)
    payloads = [(n, c, workdir, args.magma, entry, args.magma_dir, args.timeout)
                for (n, c) in tasks]
    done_chunks = defaultdict(int)
    n_failed = [0]                # so the first failure can be shown in full
    tally = defaultdict(int)      # verify mode: match / new / mismatch counts
    mismatches = []               # verify mode: human-readable lines
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
                n_failed[0] += 1
                if n_failed[0] == 1:
                    print("\n" + "!" * 60)
                    print(f"FIRST FAILURE -- degree {n} chunk "
                          f"{chunk[0]}..{chunk[-1]}:\n{e}")
                    print("!" * 60 + "\n")
                else:
                    print(f"[ERR ] degree {n} chunk {chunk[0]}..{chunk[-1]}: "
                          f"{type(e).__name__} (left as \\N, will retry)")
                continue

            st = state[n]
            for i, (bM, bT, lo, up) in results.items():
                vals = b_values(bM, bT, lo, up)
                row = st["idx_to_row"][i]

                if args.verify:
                    old = [row[off] for off in target_offsets]
                    verdict, detail = compare_row(row[0], old, vals, cfg["cols"])
                    tally[verdict] += 1
                    if verdict == "mismatch":
                        mismatches.append(detail)
                        print(f"[MISMATCH] {detail}")
                else:
                    for off, v in zip(target_offsets, vals):
                        row[off] = v

            done_chunks[n] += 1
            if not args.verify:
                if (done_chunks[n] % args.flush_every == 0
                        or done_chunks[n] == expected[n]):
                    write_data(st["path"], st["header"], st["types"], st["rows"])
            print(f"[ok  ] degree {n}: chunk {chunk[0]}..{chunk[-1]} "
                  f"({done_chunks[n]}/{expected[n]} chunks)")

    if args.verify:
        print("=" * 60)
        print(f"Verified {sum(tally.values())} groups in the {args.ordering} "
              f"ordering:")
        print(f"  agree with the data files : {tally['match']}")
        print(f"  not previously computed   : {tally['new']}")
        print(f"  DISAGREE                  : {tally['mismatch']}")
        if mismatches:
            with open(args.mismatch_log, "w", encoding="utf-8") as f:
                f.write(f"# {args.ordering} ordering, {len(mismatches)} mismatches\n")
                f.write("\n".join(mismatches) + "\n")
            print(f"\nMismatches written to {args.mismatch_log}")
            sys.exit(1)
        if n_failed[0]:
            # Chunks that never ran are not evidence of agreement.  Without
            # this, a run where Magma failed on everything would report a
            # clean bill of health.
            print(f"\nINCOMPLETE: {n_failed[0]} of {len(tasks)} chunks failed, "
                  f"so those groups were never checked.")
            sys.exit(2)
        print("\nNo disagreements. Nothing was written.")
        return

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
