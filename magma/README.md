# Magma code

This folder holds all the mathematics.

```
magma/
├── compute_disc.m           entry point, discriminant ordering
├── compute_prp.m            entry point, product-of-ramified-primes ordering
├── diagnose_disc.m          policy diagnostic, disc ordering
├── diagnose_prp.m           policy diagnostic, prp ordering
├── verdicts_disc.m          per-pair verdict report, disc ordering
├── verdicts_prp.m           per-pair verdict report, prp ordering
├── inspect_stalled.m        diagnostic: why did a b_W bracket not collapse?
├── why_no_candidates.m      diagnostic: dump the tower's candidate table
├── tests/                   see tests/README.md
└── lib/
    ├── records.m                record formats (EmbeddingProb, ...)
    ├── splitting.m              IsSplitKernel, SplitReduction (legacy)
    ├── split_tower.m            nilpotent split-tower reduction
    ├── local_tame.m             tame finite + real local liftability
    ├── wild_prop.m              wild pro-p local liftability (by Jiuya Wang)
    ├── local_verdict.m          three-valued local verdicts + policy
    ├── certificates/
    │   ├── shared.m                 phi -> field, Hilbert symbols, local squares
    │   ├── structural.m             field-independent residual shapes
    │   ├── central.m                central kernels over Q, decided locally
    │   └── q8.m                     Witt's criterion for residual Q8 problems
    ├── certify.m                CertifyAdmissible: the certificate chain
    ├── embedding_problems.m     Gpiphi
    ├── bw_phase2.m              the b_W bracket, shared by both orderings
    ├── disc/
    │   ├── orbits.m             ind(g), MinIndex, bpiphi for disc
    │   └── fullcheck.m          FullCheck Phase 1 for disc
    ├── prp/
    │   ├── orbits.m             bpiphi over conjugacy classes, for prp
    │   └── fullcheck.m          FullCheck Phase 1 for prp
    └── driver.m                 machine-readable CLI driver
```

`lib/known_residuals.m` and `lib/q8_certificate.m` are the pre-refactor versions
of `certificates/structural.m` and `certificates/q8.m`. Nothing loads them any
more; `git rm` them once you are happy, the history keeps them either way.

## How it works

`FullCheck` returns Malle's `b_M` and Turkelli's `b_T` exactly, and Wang's `b_W`
as a bracket `[BW_lower_split, BW_upper_local]` with `b_M <= L <= U <= b_T`.
`b_W` is known exactly when the bracket collapses.

Phase 1 (which pairs `(pi, phi)` exist and what `b(pi, phi)` is) differs between
the orderings and lives as `EvaluatePairs` in the two `fullcheck.m` files, where
the verdict report also picks it up, so both enumerate the same pairs. Phase 2 (the bracket) is
identical and lives once, in `bw_phase2.m`.

## The two bounds

**Lower.** `BWlowerSplit` is the largest `b(pi, phi)` over pairs *proven properly
solvable*. `split_tower.m` returns every dead end of the nilpotent split tower,
and `certify.m` offers the chain all of them, stopping at the first that
certifies. Picking one leaf in advance can only lose certificates, since which
residual a certificate can handle does not follow from its size; offering all of
them chooses nothing and so loses nothing. No case in the current data is known
to require it, and the cost is bounded by `Cap` in `SplitReductionLeaves`.

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
   realisable, which Malle's conjecture assumes anyway.
2. **Split tower properness.** `split_tower.m` needs "solvable, with nilpotent
   kernel, implies properly solvable over a global field". The exact citation is
   still open: see the marked block in that file. If the version that holds
   carries Wang's coprimality hypothesis `(|mu(k)|, |Ker pi|) = 1`, every
   even-order layer is uncertified.
3. **Exact intersection.** Conjecture 6 counts liftings with
   `K(phi~) cap Q(mu_d) = F` exactly. The certificates produce *some* proper
   lift; none of them checks the intersection. This follows Conjecture 7 as
   literally stated, and is a gap in the conjecture rather than in the code.
4. **GAR table.** `structural.m` shape (2) is cited, not verified, and imposes
   no centraliser condition on `G_r`.
