# Witness fields

A *witness* for a pair (pi, phi) is a number field K whose Galois closure
K~ has Galois group G and satisfies

    K~ cap Q(mu_d) = F    exactly,   with Gal(K~/F) = Ker(pi),

where F is the field cut out by phi and d is the d of the ordering in
question. It proves that the pair is properly solvable *with exact
intersection*, so

    b_W  >=  b(pi, phi)

with no appeal to the split tower, the certificates, or README assumption 3
(magma/README.md). Witnesses only ever raise the lower bound `BW_lower_split`;
they never touch the upper bound.

## Files

| file | written by | contents |
|---|---|---|
| `witnesses.txt` | people | candidate fields, one per line (format in the file header) |
| `verified_disc.txt` | `magma/verify_witnesses_disc.m` | what each candidate actually proves, disc ordering |
| `verified_prp.txt` | `magma/verify_witnesses_prp.m` | the same, prp ordering |

Only the `verified_*.txt` files are read by `run_parallel.py` and
`scripts/witnesses.py`. Regenerate them after editing `witnesses.txt`:

    cd magma
    magma -b verify_witnesses_disc.m
    magma -b verify_witnesses_prp.m

(`infile:=` and `outfile:=` override the default paths.)

## What verification does

For each candidate the Magma script

1. recomputes `GaloisGroup(f)` and checks `TransitiveGroupIdentification`
   against the stated label;
2. runs Phase 1 (`EvaluatePairs`) on that Galois group, so every b(pi, phi) is
   computed exactly as in production;
3. determines F = K~ cap Q(mu_d): for every normal N containing [G,G] whose
   quotient could be cyclotomic of level d, it computes the fixed field with
   `GaloisSubgroup` and tests `IsSubfield(K~^N, Q(mu_d))`; N0 is the
   intersection of those that pass, and the residues u mod d fixing F are
   read off from an explicit embedding of F into Q(mu_d);
4. keeps the pairs from step 2 with `Ker(pi) = N0` and the right kernel
   residues, which pins down the field F but not the identification
   Gal(F/Q) = G/N0;
5. narrows the identification with Frobenius data: for unramified primes
   l (not dividing d), phi(l mod d) must lie in pi of some conjugacy class of
   G with the cycle type of f mod l. The true pair always survives, so this
   is sound.

The reported `b_witness` is the MINIMUM of b over the survivors, which is a
valid lower bound whichever survivor is the true pair. `exact` is 1 when all
survivors have the same b.

**Limitation.** Cycle types cannot tell an element from its inverse, so
phi and phi composed with inversion on B always survive together. For B of
exponent > 2 the result can therefore be conservative (`exact = 0`). Pinning
down the true identification would need actual Frobenius elements, not
cycle types.

## Output format (`verified_*.txt`)

    label|b_witness|exact|b_M|b_T|survivors|source
    label|ERROR|message

`b_M` and `b_T` are recomputed from the witness's own Galois group and must
agree with the data files; `scripts/witnesses.py check` and `run_parallel.py`
both refuse a witness that disagrees.

## Using the results

* `python3 scripts/witnesses.py check --ordering prp` compares the verified
  witnesses with the data files and reports, per label: no gain (b_witness <=
  b_M), consistent, CONFLICT (b_witness above a stored exact b_W, or above
  b_T), settles (b_witness = b_T, so b_W = b_T), or raises the lower bound
  (needs a recompute to know whether the bracket now closes).
* `--apply` writes the "settles" rows directly (b_W = b_T).
* `--write-labels PATH` writes the "raises" labels, for
  `run_parallel.py --retry-unresolved --labels-file PATH`.
* `run_parallel.py` itself applies `verified_<ordering>.txt` to every row it
  computes: `L := max(L, b_witness)`, and a witness with `b_witness > U` (or
  disagreeing b_M/b_T) is reported as a conflict and the row is not written.
  `--no-witnesses` turns this off.

## Where witnesses come from

* The LMFDB, searched by degree and Galois group. For prp, b depends only on
  the abstract group, but this pipeline still requires the stated nTk to
  match, so a field of a different degree with the same abstract group is not
  accepted yet.
* Targeted constructions for solvable groups (class field theory over the
  relevant subfields). The file does not care how a field was found.

Example: for 24T8727 (prp) the open pair is phi <-> Q(i), with b = 72. Since
24T8727 is not inside A24 and its index-2 subgroup is G cap A24, and Q(mu_24)
has no cubic subfield, any field with Galois group 24T8727 and -disc(K) a
perfect square is a witness for b_W = b_T = 72.
