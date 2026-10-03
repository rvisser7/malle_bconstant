# Scripts

These are just some small Python utility files for working with the data in `../data/`.

* `witnesses.py` compares the verified witness fields in
  `../data/witnesses/verified_<ordering>.txt` with the data files: it reports
  conflicts, writes `b_W = b_T` for rows a witness settles (`--apply`), and
  lists rows whose lower bound a witness raises (`--write-labels`) for
  `run_parallel.py --retry-unresolved --labels-file`. See
  `../data/witnesses/README.md`.
