# Python tests

Run from the repository root:

```bash
python3 -m unittest discover -s tests_py -p 'test_*.py' -v
```

These cover the `b_M/b_W/b_T -> status` semantics, atomic data-file I/O,
comparison/merge semantics, witness parsing and stale-certificate rejection,
`scripts/witnesses.py` classification, command-line smoke tests, witness-file
integrity, and a whole-repository integrity scan of all `data/degree*.txt`
rows.

The same suite runs automatically on GitHub Actions for Python 3.11 and 3.13.
The CI job also compiles all Python sources and smoke-tests both command-line
entry points.  Magma tests are intentionally not run on GitHub-hosted runners,
since Magma and its licence are not available there.
