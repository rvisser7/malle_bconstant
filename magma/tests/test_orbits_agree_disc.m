// =====================================================================
// tests/test_orbits_agree_disc.m
// =====================================================================
//
//     magma -b tests/test_orbits_agree_disc.m      (run from magma/)
//
// The per-pi caching in Phase 1 is a pure speed change and must not move a
// single number.  This asserts that, pair by pair, on every group in the
// list: the class-based path bpiphiCtx (lib/class_orbits.m) agrees with the
// reference bpiphi, which BFSes over ELEMENTS of Smin meet Ker(pi) exactly as
// the pre-optimisation code did.  These are now genuinely different
// algorithms, so this test carries real weight.
//
// Comparing b_M and b_T alone would not be enough -- they are maxima, and a
// caching bug that corrupted one pair could easily leave the maximum intact.

load "lib/records.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/disc/orbits.m";

CASES := [ <6,5>, <8,10>, <8,23>, <10,20>, <12,131>, <12,19>, <15,95>, <16,1192>, <20,27> ];

failures := 0;
checked := 0;

for c in CASES do
    n := c[1]; i := c[2];
    G := TransitiveGroup(n, i);
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);

    // The class-based Phase 1 data must agree with the element-based one.
    a2, reps2, nSmin2, d2 := MinIndexClasses(G);
    if a2 ne a or nSmin2 ne #Smin or d2 ne d then
        printf "  FAIL %oT%o: MinIndexClasses (%o,%o,%o) vs MinIndex (%o,%o,%o)\n",
               n, i, a2, nSmin2, d2, a, #Smin, d;
        failures +:= 1;
    end if;

    // No MinReps here on purpose: keep the pairs whose kernel misses Smin,
    // so that the (0, 0) path is compared too.
    T, groups := Gpiphi(G, d);

    // Every pair must appear in exactly one group.
    seen := {};
    for grp in groups do
        for j in grp do
            if j in seen then
                printf "  FAIL %oT%o: pair %o in two groups\n", n, i, j;
                failures +:= 1;
            end if;
            Include(~seen, j);
        end for;
    end for;
    if #seen ne #T then
        printf "  FAIL %oT%o: grouping covers %o of %o pairs\n", n, i, #seen, #T;
        failures +:= 1;
    end if;

    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]], a);
        for j in grp do
            ebp := T[j];
            n1, b1 := bpiphiCtx(ebp, ctx);
            n2, b2 := bpiphi(ebp, Smin);
            checked +:= 1;
            if n1 ne n2 or b1 ne b2 then
                printf "  FAIL %oT%o pair %o: cached (%o,%o) vs reference (%o,%o)\n",
                       n, i, j, n1, b1, n2, b2;
                failures +:= 1;
            end if;
        end for;
    end for;
    printf "  %oT%o: %o pairs agree\n", n, i, #T;
end for;

printf "test_orbits_agree_disc: %o pairs checked, %o failures\n", checked, failures;
assert failures eq 0;
print "test_orbits_agree_disc: PASS";
quit;
