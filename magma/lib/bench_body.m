// =====================================================================
// bench_body.m  --  where does the time actually go?
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering.
//
// Splits each group's wall time into
//
//   phase1   EvaluatePairs: b_M and b_T.  Pure orbit counting.
//   phase2   the b_W bracket: split towers, certificates, local tests.
//
// so that "this group is slow" turns into "this group is slow HERE".  Do not
// optimise on a guess: the two phases have completely different cost
// profiles, and for a group with a huge kernel phase 1 can dominate even
// though phase 2 is where all the machinery lives.

BenchIndices := procedure(n, indices)
    print "label|order|pairs|b_M|b_T|phase1_s|phase2_s|total_s";
    for i in indices do
        G := TransitiveGroup(n, i);

        t0 := Cputime();
        d, a, nSmin, nPairs, bM, bT, pairs := EvaluatePairs(G);
        t1 := Cputime();
        _ := BWBoundsFromPairs(d, pairs, bM, bT, DefaultLocalPolicy);
        t2 := Cputime();

        printf "%oT%o|%o|%o|%o|%o|%o|%o|%o\n",
               n, i, #G, nPairs, bM, bT,
               t1 - t0, t2 - t1, t2 - t0;
    end for;
end procedure;
