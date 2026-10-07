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

Verification is incremental: a row already in `verified_*.txt` is reused when
the same `(label, poly)` is still offered in `witnesses.txt`, so only new or
edited witnesses are verified.  `ERROR` rows are always retried.  After a
change to the verifier itself (`magma/lib/witness_body.m`) cached rows may be
stale, so re-verify with `force:=1` (everything) or `recheck:=L1,L2,...`
(just those labels), e.g.

    magma -b recheck:=26T34,34T34 verify_witnesses_disc.m

## What verification does

For each candidate the Magma script

1. recomputes `GaloisGroup(f)`, requires `GaloisProof(f, S)` to certify any
   conditional steps, and checks `TransitiveGroupIdentification` against the
   stated label;
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
exponent > 2 the result can therefore be conservative
(`identification_exact = 0`). Pinning down the true identification would need
more Frobenius information than the cycle type in the defining permutation
representation (for example auxiliary resolvents).

For quotient witnesses this is partly repaired by **twisting**
(`WitnessTwistPair` in `magma/lib/witness_body.m`).  If beta in Aut(Gam) maps
Gal(K~/F) to itself, the witness used through alpha o beta realises the same
kernel and the pair iota_beta o phi_alpha, with iota_beta = alpha beta
alpha^-1 on G/N.  So whichever survivor s is the true phi_alpha, the value
max_beta b(iota_beta o s) is attained by a genuine G-solution, and the bound
for alpha is min over survivors of that maximum.  When the inversion twin is
realised by such a beta, the twins collapse and the bound is exact: e.g.
26T34 (Gam = C3 x Q8, inversion on the C3 factor; 3 -> 7) and 34T34
(Gam = SmallGroup(32,17), every unit mod 8 on Gam/N0 = C8; 3 -> 9).

## Quotient and alternate-representation witnesses

`VerifyAnyWitness` first uses the fast direct path when the polynomial realises
exactly the target `nTk` permutation representation.  Otherwise it treats the
field as a witness for a quotient `G/M`, **including `M = 1`**.  Consequently a
field with the same abstract Galois group but a different degree/transitive
representation can now witness `nTk` as well.

The quotient path (implemented by `VerifyQuotientWitnessCore` in
`magma/lib/witness_body.m`)

1. computes Gam = Gal(f) and F = K~ cap Q(mu_d) for the d of G;
2. runs over the normal subgroups M of G with G/M isomorphic to Gam such that
   * M is reached by a chain 1 = M_0 < ... < M_r = M of normal subgroups
     of G, each M_i/M_(i-1) an admissible split-tower layer of G/M_(i-1): a
     GAR layer, or complemented and nilpotent ([NSW 9.6.10]), or
     complemented of odd order with the mu(K) condition ([NSW 9.5.8]); and
   * M is inside [G,G], so that the lifted G-field has no abelian
     subextension beyond those of the G/M-field, and the intersection with
     Q(mu_d) is still exactly F;
3. for every isomorphism alpha : Gam -> G/M (a fixed one composed with all of
   Aut(Gam)), takes the realised kernel q^-1(alpha(Gal(K~/F))), narrows phi
   with Frobenius cycle types transported by alpha, and records the minimum b
   over the survivors;
4. reports the maximum over M and alpha. Each (M, alpha) is a genuine proper
   solution after lifting through M, so the maximum is a valid lower bound.

Automorphisms of G/M need not lift to G, which is why step 3 runs over all of
Aut(Gam) rather than one isomorphism: for G/M = C4:C4, for example, the
characteristic C4 x C2 subgroup gives a smaller b than the other two.

The six degree-20 entries (20T105, 20T111, 20T386, 20T390, 20T396, 20T397,
disc ordering) are residual witnesses of this kind, with G = O_5(G) : H and
H of order 16. Each should verify to b_witness = b_T.

The ten further degree-20 entries added in October 2026 (20T498, 20T550,
20T583, 20T598, 20T612, 20T782, 20T785, 20T789, 20T879, 20T884, disc
ordering) are residual witnesses of the same kind, with H = G/O_5(G) of order
32 to 384 and F = Q(sqrt 5).  For these the split-tower leaf G/O_5(G) is
non-split and non-central, so no certificate applies and the witness is the
only route to b_W.  20T583 and 20T598 share a polynomial (they have the same
H).  The order-192 and order-384 ones were identified only statistically when
they were found, so their verification is the first rigorous check.  Each
should verify to b_witness = b_T.  They were found with
`scripts/witness_search/` (see its README for the method and the local
conditions that made the searches succeed).

## Output format (`verified_*.txt`)

    label|b_witness|identification_exact|b_M|b_T|survivors|source|poly
    label|ERROR|message

Here `poly` is the canonical coefficient vector that was actually verified.
When `witnesses.txt` is present beside the verified file, the Python loader
checks that the same `(label, poly)` is still offered for the relevant ordering.
Thus editing or removing a witness invalidates the old certificate instead of
silently reusing it.  Legacy `verified_*.txt` rows without `poly` are rejected;
regenerate them with the Magma verifier after applying this change.

`b_M` and `b_T` are recomputed from the witness's own proven Galois group and
must agree with the data files; `scripts/witnesses.py` and `run_parallel.py`
both refuse a witness that disagrees.

## Using the results

* `python3 scripts/witnesses.py --ordering prp` compares the verified
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

* The LMFDB, searched by degree and Galois group.  A field need not have the
  same degree as the target `nTk`: the verifier may use it through the `M = 1`
  abstract-group path (or through a genuine quotient `M > 1`).
* Targeted constructions for solvable groups (class field theory over the
  relevant subfields). The file does not care how a field was found.

Example: for 24T8727 (prp) the open pair is phi <-> Q(i), with b = 72. Since
24T8727 is not inside A24 and its index-2 subgroup is G cap A24, and Q(mu_24)
has no cubic subfield, any field with Galois group 24T8727 and -disc(K) a
perfect square is a witness for b_W = b_T = 72.
