// =====================================================================
// tests/test_small_groups_prp.m
// =====================================================================
//
//     magma -b tests/test_small_groups_prp.m      (run from magma/)
//     magma -b slow:=1 tests/test_small_groups_prp.m
//
// Same broad small-group sweep as the discriminant test, but for the product
// of ramified primes.  Here every non-identity class is minimal and
// d = exponent(G).

load "lib/records.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/prp/orbits.m";

DirectBM := function(G)
    cls := Classes(G);
    cm := ClassMap(G);
    ididx := cm(Id(G));
    allowed := { i : i in [1..#cls] | i ne ididx };
    if IsEmpty(allowed) then return 0; end if;
    d := Exponent(G);
    C, f := MultiplicativeGroup(Integers(d));
    visited := {}; orbits := 0;
    for i in allowed do
        if i in visited then continue; end if;
        orbits +:= 1; Include(~visited, i); queue := [i]; q := 1;
        while q le #queue do
            j := queue[q]; q +:= 1;
            rep := cls[j][3];
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
    d := Exponent(G);
    T, groups := Gpiphi(G, d);
    bM := 0; bT := 0;
    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]]);
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
printf "test_small_groups_prp: %o groups checked, %o failures\n", checked, failures;
assert failures eq 0;
print "test_small_groups_prp: PASS";
quit;
