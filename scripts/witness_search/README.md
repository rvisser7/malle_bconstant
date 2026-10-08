# Witness search (PARI/GP + GAP)

Tools for *finding* residual witness fields when the split tower stops at a
non-split, non-central leaf and no certificate applies.  They produced the
degree-20 disc witnesses added to `data/witnesses/witnesses.txt` in
October 2026 (20T498, 550, 554, 583, 598, 612, 662, 782, 783, 785, 789, 877,
879, 880, 884).

Nothing these scripts print is trusted.  Add a candidate to
`data/witnesses/witnesses.txt`, then run `magma -b verify_witnesses_disc.m`
(or `_prp`), which proves the Galois group, the intersection with Q(mu_d) and
b(pi, phi); `scripts/witnesses.py --ordering <ordering>` then compares with the data.

## Requirements

* Python 3 with `numpy` and `cypari2` (`pip install cypari2`); PARI >= 2.15.
* GAP 4 with TransGrp, SmallGrp (only for `gap/` and to regenerate `tables/`).
  Run it as `gap -A` so it does not autoload AtlasRep, which may try to download.

## The situation these tools address

For all ten groups above, `G = V : H` with `V = O_5(G) = C5^4` complemented
inside `[G,G]` and the only pairs with `b > b_M` have `F = Q(sqrt 5)`.  The
split tower peels `V` and stops at the leaf `1 -> H0 -> H -> C2 -> 1`, which
is locally solvable everywhere (so `U = b_T`) but non-split and non-central.
Then `b_W = b_T` iff the leaf is properly solvable, and a field with Galois
group `H` and `Q(sqrt 5)` fixed by the right `H0` is a residual witness that
the existing quotient path of the verifier accepts.

## Workflow

1. **Analyse H in GAP.** IdGroup of `H = G/O_5(G)` and of the admissible
   `H0`, `H^ab`, `[H,H]` and whether it is elementary abelian, and the
   block structure of the faithful degree-16 representation.
2. **Run the local pre-checks first** (`gap/local_lift.g`): which complex
   conjugations and which tame (inertia, Frobenius) data of the base field
   can lift to `H`.  Every successful search was unblocked by such a local
   condition, never by enlarging S:
   * 20T498, 20T583/598, 20T612: `H^ab = C4 x C2` and only the identity
     (resp. the identity and one involution) lifts at infinity, so the base
     `E = L(sqrt 5)` must be totally real; a real cyclic quartic `L` of
     conductor 145 (ramified at 5) works.
   * 20T612: additionally the intermediate `H/Z(H)` field must be totally
     real, or every central lift lands in [64,23] / [64,90].
   * 20T550 (`H = 2O`): the only involution is central, so `L` must be a
     totally real S4 quartic.
   * 20T879/884: the Frobenius of the S4 quartic `L` at 5 must have cycle
     type (1,1,1,1), (1,1,2) or (1,3); `x^4-x-1` fails, `x^4-x+1` works.
3. **Search** with the script matching the shape of `H`:

| script | shape of H | used for |
|---|---|---|
| `search_abelian_base.py` | `[H,H]` elementary, `H/[H,H] = Gal(E/Q)` | 20T498 ([32,8]), 20T583/598 ([64,33]) |
| `search_central_lift.py` | as above after removing a central C2 | 20T612 ([64,35]) |
| `search_octic_kummer.py` | S4/A4 block quotient, elementary block kernel | 20T554 (48), 20T662 (96), 20T782/783/785/789 (192), 20T877/879/880/884 (384) |
| `search_binary_octahedral.py` | `H = 2O` | 20T550 |
| `search_kummer_fixed_field.py` | 2-block quotient a fixed field of (A4 closure)(sqrt 5, ...), any degree; `--exact-kummer` | 30T2400, 2418, 2467, 2778, 2843, 2848 (degree 24, orders 192/384) |

Each script's docstring has the exact command line that found the committed
witness.  Typical run times on one core: seconds (abelian base), 1-5 minutes
(the others).

## How the searches work

All four reduce Kummer theory to F2 linear algebra.  An S-unit of the base
field is represented by its quadratic residue symbols at many degree-1 primes
of a Galois field containing all its conjugates ("Legendre coordinates"); on
S-units modulo squares this is injective.  Galois automorphisms act by
permuting those primes, so fixed spaces, conjugate spans and invariant
classes are kernels of explicit F2 matrices (`wslib.GaloisBase`,
`wslib.ConjugateData`).  Only candidates passing the linear conditions are
turned into fields.

Candidate closures are identified exactly by PARI `galoisinit` when it can
(2-groups, 2O, and the orders 48 and 96 groups above); otherwise by Frobenius
cycle-type statistics against `tables/` (regenerate with
`gap -A -q gap/cycle_types.g`), which is a filter only.  Statistics can tie
(16T60/57, 16T423/418, 16T763/725 have identical distributions); the script
then prints a warning, and the twins have to be separated by other means
(see the docstring of `search_octic_kummer.py`).

## Exact identification by Kummer theory

When the closure is too large for PARI `galoisinit` (it fails on the order
192/384 closures of degree 24) and the cycle-type statistics tie
(24T298/301/308, 24T299/305/309/310/312 for order 192),
`wslib.kummer_galois_group(K, P, delta)` computes Gal(L/Q) exactly for
L = closure of K(sqrt delta), K a subfield of the Galois field P: L is
P(sqrt delta_1, ..., sqrt delta_n), every sigma in Gal(P/Q) lifts as
sqrt(delta_i) -> s_i sqrt(delta_pi(i)), and the admissible sign vectors s are
cut out by the multiplicative relations among the delta_i, each certified to
be an exact square in P (nfroots).  The resulting permutation group on the 2n
roots is identified with GAP (`wslib.gap_identify`: IdGroup of H and of the
subgroup fixing sqrt q).  `search_kummer_fixed_field.py --exact-kummer` uses
it on every statistical hit in the twin class of a target.

For the degree-30 searches the decisive conditions were again local: the A4
quartic must be totally real (complex conjugation lies in H0 and must act
trivially on the A4 part), P should be unramified at 2 (with sqrt(-1) the
order-384 target 24T894/908 never appeared; with sqrt(-3) it did at once),
and for [192,199] the Frobenius of the A4 quartic at 5 must not be a double
transposition (then only [192,190] occurs).

## Files

* `wslib.py`: shared code (S-units, Legendre coordinates, F2 algebra,
  identification).
* `search_*.py`: the four searches above.
* `gap/local_lift.g`: local liftability tables (with the two examples above).
* `gap/cycle_types.g`, `gap/cycle_types_deg24.g`: regenerate `tables/*.txt`.
* `tables/cycle_types_deg16.txt`, `tables/index2_subgroups_deg16.txt`:
  cycle-type distributions of degree-16 transitive groups of orders 32, 48,
  64, 96, 192, 384 (and `*_deg24.txt`: degree 24, orders 192 and 384), and of the index-2 subgroups of the relevant ones.
