# Scripts

These are just some small Python utility files for working with the data in `../data/`.

* `witnesses.py` compares the verified witness fields in
  `../data/witnesses/verified_<ordering>.txt` with the data files: it reports
  conflicts, writes `b_W = b_T` for rows a witness settles (`--apply`), and
  lists rows whose lower bound a witness raises (`--write-labels`) for
  `run_parallel.py --retry-unresolved --labels-file`. See
  `../data/witnesses/README.md`.

* `list_unresolved.py` lists the groups whose b_M and b_T are computed but
  whose b_W is still `\N`, per ordering (`--ordering disc|prp|both`), with
  `--summary` for counts per degree and `--labels-only` for a file that
  `run_parallel.py --labels-file` accepts.
