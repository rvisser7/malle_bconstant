// =====================================================================
// tests/test_small_groups_disc.m
// =====================================================================
//
//     magma -b tests/test_small_groups_disc.m      (run from magma/)
//     magma -b slow:=1 tests/test_small_groups_disc.m
//
// Sweep every transitive group through degree 6 (degree 7 with slow:=1).
// Compare production b_M with a tiny independent implementation of Malle's
// original orbit definition on the minimal-index conjugacy classes, and check
// b_M <= b_T.  This is broad coverage for group shapes not hand-picked by the
// regression fixtures.

load "lib/records.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/disc/orbits.m";

DirectBM := function(G)
    cls := [ c : c in Classes(G) | c[1] gt 1 ];
    if #cls eq 0 then return 0; end if;

    inds := [ Degree(G) - &+[ z[2] : z in CycleStructure(c[3]) ] : c in cls ];
    a := Minimum(inds);
    keep := [ k : k in [1..#cls] | inds[k] eq a ];
    d := LCM([ cls[k][1] : k in keep ]);
    C, f := MultiplicativeGroup(Integers(d));
    cm := ClassMap(G);

    allowed := { cm(cls[k][3]) : k in keep };
    visited := {};
    orbits := 0;
    for i in allowed do
        if i in visited then continue; end if;
        orbits +:= 1;
        Include(~visited, i);
        queue := [i]; q := 1;
        while q le #queue do
            j := queue[q]; q +:= 1;
            rep := Classes(G)[j][3];
            for c in Generators(C) do
                nxt := cm(rep^(IntegerRing()!f(c)));
                assert nxt in allowed;
                if not nxt in visited then
                    Include(~visited, nxt); Append(~queue, nxt);
                end if;
            end for;
        end while;
    end for;
    return orbits;
end function;

ProductionPhase1 := function(G)
    a, reps, _, d := MinIndexClasses(G);
    T, groups := Gpiphi(G, d : MinReps := reps);
    bM := 0; bT := 0;
    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]], a);
        if ctx`nkept eq 0 then continue; end if;
        for j in grp do
            ebp := T[j]; _, b := bpiphiCtx(ebp, ctx); b := Integers()!b;
            bT := Max(bT, b);
            if IsTrivialQuotientEbp(ebp) then bM := Max(bM, b); end if;
        end for;
    end for;
    return bM, bT;
end function;

maxDegree := assigned slow select 7 else 6;
failures := 0; checked := 0;
for n := 2 to maxDegree do
    for k := 1 to NumberOfTransitiveGroups(n) do
        G := TransitiveGroup(n, k);
        got, bT := ProductionPhase1(G);
        want := DirectBM(G);
        checked +:= 1;
        if got ne want or got gt bT then
            printf "  FAIL %oT%o: production b_M=%o direct=%o b_T=%o\n",
                   n, k, got, want, bT;
            failures +:= 1;
        end if;
    end for;
end for;
printf "test_small_groups_disc: %o groups checked, %o failures\n", checked, failures;
assert failures eq 0;
print "test_small_groups_disc: PASS";
quit;
