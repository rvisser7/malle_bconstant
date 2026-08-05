# Magma code
 
This folder includes all the relevant Magma code; all of the actual mathematics and computations lives here.

The layout of this folder is as follows:
 
```
magma/
├── compute_disc.m       entry point, discriminant ordering
├── compute_prp.m        entry point, product-of-ramified-primes ordering
└── lib/
    ├── records.m               record formats (EmbeddingProb, ...)
    ├── index_disc.m            ind(g) for the discriminant ordering
    ├── index_prp.m             ind(g) for the prp ordering
    ├── splitting.m             IsSplitKernel, SplitReduction, ...
    ├── local_tame.m            tame finite + real local liftability
    ├── embedding_problems.m    Gpiphi
    ├── orbits.m                MinIndex, bpiphi, ...
    ├── fullcheck.m             FullCheck
    └── driver.m                machine-readable CLI driver
```

