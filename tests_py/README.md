# Python tests

Run from the repository root:

```bash
python3 -m unittest discover -s tests_py -p 'test_*.py'
```

These cover the `b_M/b_W/b_T -> status` semantics, atomic data-file I/O,
comparison/merge semantics, witness parsing and stale-certificate rejection,
`scripts/witnesses.py` classification, and a whole-repository integrity scan
of all `data/degree*.txt` rows.
