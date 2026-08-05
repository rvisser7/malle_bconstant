#!/usr/bin/env python3
"""Combine the per-degree b-constant files into a single psycodict-style upload file.

Reads data/degree<n>.txt for n = 1..47, keeps only the columns

    label | malle_turkelli_b | malle_wang_b | malle_b_status

and drops any row whose three data entries are all \\N.

Place this script alongside the degree<n>.txt files and run it there.

Usage:
    python3 combine_malle_b.py                          # read the script's own folder
    python3 combine_malle_b.py -d /path/to/data -o out.txt
    python3 combine_malle_b.py --download                # fetch from GitHub
"""

import argparse
import os
import sys
import urllib.request

COLUMNS = ["label", "malle_turkelli_b", "malle_wang_b", "malle_b_status"]
TYPES = {"label": "text", "malle_turkelli_b": "smallint",
         "malle_wang_b": "smallint", "malle_b_status": "smallint"}
NULL = r"\N"
RAW_URL = ("https://raw.githubusercontent.com/rvisser7/malle_bconstant"
           "/main/data/degree{n}.txt")


def read_lines(degree, data_dir=None, download=False):
    """Return the lines of degree<n>.txt, from disk or from GitHub."""
    if download:
        url = RAW_URL.format(n=degree)
        with urllib.request.urlopen(url) as resp:
            text = resp.read().decode("utf-8")
    else:
        path = os.path.join(data_dir, "degree{}.txt".format(degree))
        with open(path, encoding="utf-8") as f:
            text = f.read()
    # splitlines() copes with both LF and CRLF; lstrip removes any BOM
    return text.lstrip("\ufeff").splitlines()


def parse_file(lines, degree):
    """Yield (label, turkelli, wang, status) tuples from one degree file.

    The first line is the header, the second the postgres types, the third
    blank; data rows follow.  Column positions are looked up by name rather
    than hardcoded, so the files can gain or reorder columns later.
    """
    if len(lines) < 3:
        raise ValueError("degree{}.txt is too short to contain a header".format(degree))

    header = lines[0].strip().split("|")
    try:
        idx = [header.index(col) for col in COLUMNS]
    except ValueError as exc:
        raise ValueError("degree{}.txt is missing a required column: {}".format(degree, exc))

    for lineno, line in enumerate(lines[2:], start=3):
        line = line.strip()
        if not line:
            continue
        parts = line.split("|")
        if len(parts) != len(header):
            raise ValueError(
                "degree{}.txt line {}: expected {} fields, got {}".format(
                    degree, lineno, len(header), len(parts)))
        row = [parts[i] for i in idx]
        # skip rows where every data entry (i.e. everything but the label) is null
        if all(entry == NULL for entry in row[1:]):
            continue
        yield row


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-d", "--data-dir", default=os.path.dirname(os.path.abspath(__file__)),
                        help="folder containing degree<n>.txt (default: the script's own folder)")
    parser.add_argument("-o", "--output", default="malle_b_constants.txt",
                        help="output file (default: malle_b_constants.txt)")
    parser.add_argument("--min-degree", type=int, default=1)
    parser.add_argument("--max-degree", type=int, default=47)
    parser.add_argument("--download", action="store_true",
                        help="fetch the files from GitHub instead of reading locally")
    args = parser.parse_args()

    total = kept = 0
    with open(args.output, "w", encoding="utf-8", newline="\n") as out:
        out.write("|".join(COLUMNS) + "\n")
        out.write("|".join(TYPES[col] for col in COLUMNS) + "\n")
        out.write("\n")

        for degree in range(args.min_degree, args.max_degree + 1):
            lines = read_lines(degree, args.data_dir, args.download)
            n_before = kept
            for row in parse_file(lines, degree):
                out.write("|".join(row) + "\n")
                kept += 1
            total += max(0, len(lines) - 3)
            print("degree {:>2}: {:>6} rows kept".format(degree, kept - n_before),
                  file=sys.stderr)

    print("\nWrote {} rows to {} (dropped {} all-null rows)".format(
        kept, args.output, total - kept), file=sys.stderr)


if __name__ == "__main__":
    main()
