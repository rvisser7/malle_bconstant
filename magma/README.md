# Magma code

This folder holds all the mathematics.

```
magma/
├── compute_disc.m           entry point, discriminant ordering
├── compute_prp.m            entry point, product-of-ramified-primes ordering
├── bench_disc.m             Phase 1 / Phase 2 timing, disc ordering
├── bench_prp.m              Phase 1 / Phase 2 timing, prp ordering
├── diagnose_disc.m          policy diagnostic, disc ordering
├── diagnose_prp.m           policy diagnostic, prp ordering
├── verdicts_disc.m          per-pair verdict report, disc ordering
├── verdicts_prp.m           per-pair verdict report, prp ordering
├── inspect_stalled.m        diagnostic: why did a b_W bracket not collapse?
├── why_no_candidates.m      diagnostic: dump the tower's candidate table
├── verify_witnesses_disc.m  verify data/witnesses/witnesses.txt, disc ordering
├── verify_witnesses_prp.m   verify data/witnesses/witnesses.txt, prp ordering
├── tests/                   see tests/README.md
└── lib/
    ├── records.m                record formats (EmbeddingProb, ...)
    ├── splitting.m              IsSplitKernel, SplitReduction (legacy)
    ├── split_tower.m            split-tower reduction (nilpotent / odd layers)
    ├── local_tame.m             tame finite + real local liftability
    ├── wild_prop.m              wild pro-p local liftability (by Jiuya Wang)
    ├── local_verdict.m          three-valued local verdicts + policy
    ├── certificates/
    │   ├── shared.m                 phi -> field, Hilbert symbols, local squares
    │   ├── structural.m             field-independent residual shapes
    │   ├── central.m                central kernels over Q, decided locally
    │   └── q8.m                     Witt's criterion for residual Q8 problems
    ├── certify.m                CertifyAdmissible: the certificate chain
    ├── embedding_problems.m     Gpiphi (pruned), GpiphiReference
    ├── class_orbits.m           b(pi,phi) on classes of Ker(pi), both orderings
    ├── bw_phase2.m              the b_W bracket, shared by both orderings
    ├── disc/
    │   ├── orbits.m             ind(g), MinIndexClasses; keep ind = a
    │   └── fullcheck.m          FullCheck Phase 1 for disc
    ├── prp/
    │   ├── orbits.m             keep every non-identity class
    │   └── fullcheck.m          FullCheck Phase 1 for prp
    ├── driver.m                 machine-readable CLI driver
    └── witness_body.m           witness fields: K~ cap Q(mu_d), the pair, b
```

## How it works

`FullCheck` returns Malle's `b_M` and Turkelli's `b_T` exactly, and Wang's `b_W`
as a bracket `[BW_lower_split, BW_upper_local]` with `b_M <= L <= U <= b_T`.
`b_W` is known exactly when the bracket collapses.

Phase 1 (which pairs `(pi, phi)` exist and what `b(pi, phi)` is) differs between
the orderings and lives as `EvaluatePairs` in the two `fullcheck.m` files, where
the verdict report also picks it up, so both enumerate the same pairs.

`Gpiphi` returns the pairs grouped by `pi`, and Phase 1 walks the groups. Every
expensive thing in Phase 1 depends on `pi` alone -- `Kernel(pi)`, then
`Classes(N)` and `ClassMap(N)` for prp or `Smin meet N` for disc -- so it is built
once per `pi` in a `KernelCtx` and shared by every `phi` over it.

Both orderings now count orbits on conjugacy classes of `N = Ker(pi)`, with
the machinery in `class_orbits.m`; they differ only in which classes are kept
(`ind = a` for disc, every non-identity class for prp). The twisted action is
cached as permutations of the kept class indices: powering by `a = f(c)`
depends only on the generator of `C`, conjugation depends only on `phi(c)` in
`B` and composes over generators of `B`, so a pi group costs
`(Ngens(B) + Ngens(C)) * #kept classes` ClassMap evaluations in total and each
pair after that is array lookups. `MinIndexClasses` gets `a`, `d` and `#Smin`
from the classes of `G`, so nothing element-sized is ever built.

`Gpiphi` enumerates subgroups of `AbG / e*AbG` (with `e = Exp(C)`) of index
dividing `#C`, since only those quotients admit a surjection from `C`, and in
the disc ordering skips every `pi` whose kernel misses the minimal classes
before forming `Kernel(pi)`. `GpiphiReference` is the old enumeration.

The element-based `bpiphi`/`MinIndex` and `GpiphiReference` are kept as
reference implementations; `tests/test_orbits_agree_*.m` and
`tests/test_gpiphi_pruning.m` assert agreement pair by pair or value by value.
Use `bench_disc.m` / `bench_prp.m` to see which phase a slow group is actually
slow in before optimising further. Phase 2 (the bracket) is
identical and lives once, in `bw_phase2.m`.

## The two bounds

**Order of work.** Phase 2 sorts the pairs by decreasing `b`. The first pair
not proven locally obstructed fixes the upper bound; a pair proven obstructed is
never sent to the certificates (sound policy); the first certified pair fixes
the lower bound and stops the loop. The split tower depends on `pi` only, so it
is built once per `pi` (`SplitTowerRaw`) and passed to the certificates and the
local-quotient scan through their `Raw` parameter. Inside the tower, states are
cumulative kernels in the original group and each is expanded once.

**Lower.** `BWlowerSplit` is the largest `b(pi, phi)` over pairs *proven properly
solvable*. `split_tower.m` returns every dead end of the split tower,
and `certify.m` offers the chain all of them, stopping at the first that
certifies. Picking one leaf in advance can only lose certificates, since which
residual a certificate can handle does not follow from its size; offering all of
them chooses nothing and so loses nothing. No case in the current data is known
to require it, and the cost is bounded by `Cap` in `SplitReductionLeaves`.

**Witness fields.** Independently of the certificates, a number field whose
Galois closure K~ has group G and meets Q(mu_d) in exactly F proves
b_W >= b(pi, phi) for the pair it realises, with exact intersection, so
without README assumption 3. Candidates live in `data/witnesses/witnesses.txt`;
`verify_witnesses_*.m` recomputes everything about them and `run_parallel.py`
raises L to the best verified witness. A field for a quotient G/M also
counts (a *residual* witness) when M is reached by admissible tower layers inside
[G,G]. See `data/witnesses/README.md`.

**Upper.** `BWupperLocal` is the largest `b(pi, phi)` over pairs *not proven
locally obstructed*.

The rule that keeps these honest: a local test may not raise the lower bound on
its own, and a certificate may not lower the upper bound. `certificates/central.m`
looks like an exception and is not, because over Q a central kernel has
`Sha^2 = 0`, so an *exhibited* lift at every place is equivalent to solvability,
and a central kernel upgrades solvable to properly solvable by twisting.

## Local verdicts are three-valued

`local_verdict.m` returns Yes / No / Unknown per place, because two of the tests
prove only one direction:

* the tame test at a prime `p` where `F/Q` is tame is exact when `p` does not
  divide `#Ker(pi)`, and otherwise a failure proves nothing, since the lift may
  be wildly ramified;
* the pro-`p` test exhibits a lift of `phi_p` itself only when `phi_p` factors
  through `G_{Q_p}(p)`, which is checked; and whether a full local lift forces
  the pro-`p` problem to be solvable is not established.

The upper bound excludes a pair only on a No, and a No is inherited from any
quotient: if `M` is normal in `G` with `M` inside `Ker(pi)`, a solution of the pair
pushes forward to a solution of the quotient problem, so an obstruction on the
quotient obstructs the pair. Since passing to a quotient shrinks the kernel, it can
move the tame test at `p` into its exact case, which is how 20T297 is decided.
`LocalVerdictWithQuotients` tries the split residual first, then normal subgroups
chosen to kill a prime that is currently undetermined. `central.m` fires only on an
all-Yes. `LegacyLocalPolicy` reproduces the old both-ways-veto behaviour and
exists only so that the diagnostics can measure how many published cells the
correction moves. **Run `diagnose_disc.m` / `diagnose_prp.m` before recomputing any column.** When a
group does move, `magma -b n:=<deg> i:=<idx> verdicts_disc.m` prints the verdict at
every place for every pair that could raise the upper bound, which says which test
and which prime caused it.

## Standing assumptions, in one place

1. **`b_W >= b_M`.** Both bounds start at `b_M`; the trivial pair is never sent
   to a certificate, since for `B = 1` proper solvability is the inverse Galois
   problem for `G` over Q. Every number here is conditional on `G` being
   realisable, which Malle's conjecture assumes anyway. Strictly, the trivial
   pair needs a `G`-extension with `K cap Q(mu_d) = Q` (exact intersection
   again, see 3). For solvable `G` this follows from Shafarevich with
   ramification kept away from the primes dividing `d`; for non-solvable `G`
   it is part of the assumption.
2. **Split tower properness.** `split_tower.m` lifts a *proper* solution
   psi : G_Q ->> G/M, with unknown field K, through a *split* layer
   1 -> M -> G -> G/M -> 1. A layer is allowed (`LayerAllowed`) if either
   M is nilpotent -- NSW08 Thm (9.6.10), no further hypothesis -- or #M is odd
   and exp(M) is prime to #mu(K) -- NSW08 Cor (9.5.8)(ii)(c). Since K is
   unknown, the second is enforced by requiring that p - 1 not divide
   exp((G/M)^ab) for each prime p | #M, which rules out Q(mu_p) in K.
   Note (9.5.8) asks for coprimality with mu(K), the TOP field, not mu(Q).
   Third, a layer M all of whose composition factors are non-abelian with a
   GAR-realisation over Q is peeled off WITHOUT a complement: by [MM99,
   Thm IV.3.6] every embedding problem with such a kernel is properly
   solvable (Thm IV.3.5 for M = H^r, with G permuting the factors). The table
   is `IsGARSimpleOrder` in `split_tower.m`.
3. **Exact intersection.** Conjecture 6 counts liftings with
   `K(phi~) cap Q(mu_d) = F` exactly. The certificates produce *some* proper
   lift; none of them checks the intersection. This follows Conjecture 7 as
   literally stated, and is a gap in the conjecture rather than in the code.
   `diagnose_intersection_disc.m` / `_prp.m` measure it: a witness K for
   (pi, phi) witnesses, WITH exact intersection, some refinement
   (pi', phi'), so `min b(pi', phi')` over the refinements that are not
   proven locally obstructed is a lower bound immune to this gap. Groups
   where it is below `L` are flagged.
4. **GAR table.** Checked against [MM99] Ch. IV: Thm 4.3 (one variable over
   Q) and Ex. 4.1, 4.2 (L3(3), L3(4), two variables). There is no
   centraliser condition (Prop. IV.3.1 and Thm IV.3.2/3.5/3.6). A6 is NOT
   on the list (Thm 4.3(a) excludes n = 6) and has been removed; it had
   been accepted before. Simple factors are identified by order, which is
   exact by the classification except for {A8, L3(4)} (both GAR) and
   {B_n(q), C_n(q)}, n >= 3, q odd (kept out of the table).
5. **Wreath shape.** `structural.m` shape (3) accepts `T` abelian (class field
   theory) or `T` regular over Q(t); it no longer accepts arbitrary solvable `T`,
   which had no citation.
6. **Supplements (experimental, off).** `certify.m` can, with
   `SupplementDepth > 0`, certify a leaf through a maximal subgroup X with
   X Fit(Ker) = G (lemma and proof in `certify.m`). Production runs use
   depth 0; `diagnose_supplements_*.m` reports what depth 1 would change.
