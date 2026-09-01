# Magma code
 
This folder includes all the relevant Magma code; all of the actual mathematics and computations lives here.

The layout of this folder is as follows:
 
```
magma/
├── compute_disc.m           entry point, discriminant ordering
├── compute_prp.m            entry point, product-of-ramified-primes ordering
├── inspect_stalled.m        diagnostic: why did a b_W bracket not collapse?
├── why_no_candidates.m      diagnostic: dump the tower's candidate table
└── lib/
    ├── records.m                record formats (EmbeddingProb, ...)
    ├── splitting.m              IsSplitKernel, SplitReduction (legacy)
    ├── split_tower.m            nilpotent split-tower reduction
    ├── q8_certificate.m         Witt's criterion for residual Q8 problems
    ├── known_residuals.m        table of residual shapes with known citations
    ├── local_tame.m             tame finite + real local liftability
    ├── wild_prop.m              wild pro-p local liftability (by Jiuya Wang)
    ├── embedding_problems.m     Gpiphi
    ├── disc/
    │   ├── orbits.m             ind(g), MinIndex, bpiphi for disc
    │   └── fullcheck.m          FullCheck for disc
    ├── prp/
    │   ├── orbits.m             bpiphi over conjugacy classes, for prp
    │   └── fullcheck.m          FullCheck for prp
    └── driver.m                 machine-readable CLI driver
```

## How it works

The `FullCheck` function returns Malle's original b-constant `b_M` and Turkelli's b-constant `b_T`.
To compute Wang's b-constant `b_W`, we compute a lower bound and upper bound `[BWlowerSplit, BWupperLocal]`for `b_W`, with `b_M <= L <= U <= b_T`.
