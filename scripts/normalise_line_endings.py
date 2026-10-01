#!/usr/bin/env python3
"""
normalise_line_endings.py  --  make every data file LF, once.

Nineteen of the degree files (21, 22, 25-29, 31, 33-35, 37-39, 41, 43, 44, 46,
47) are entirely CRLF while the rest are LF, presumably from a Windows machine
during the workshop. Python's universal newlines hides this from every script
in this repository, so nothing here is broken by it, but anything outside
Python -- awk, the LMFDB upload path, git diffs -- sees a trailing carriage
return glued to the last column, e.g. the string "\\N\\r" instead of "\\N".

Run this once, commit, and let .gitattributes keep it that way.

Usage:
    python3 scripts/normalise_line_endings.py --dry-run
    python3 scripts/normalise_line_endings.py
"""

import argparse
import glob
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--glob", default=os.path.join(REPO_ROOT, "data", "*.txt"))
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    touched = 0
    for path in sorted(glob.glob(args.glob)):
        with open(path, "rb") as f:
            raw = f.read()
        if b"\r" not in raw:
            continue
        touched += 1
        print("%s: %d CR bytes%s"
              % (os.path.relpath(path, REPO_ROOT), raw.count(b"\r"),
                 " (dry run)" if args.dry_run else ""))
        if not args.dry_run:
            with open(path, "wb") as f:
                f.write(raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n"))

    print("%d file(s)%s" % (touched, " would change" if args.dry_run else " normalised"))


if __name__ == "__main__":
    main()
