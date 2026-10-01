// =====================================================================
// tests/test_gpiphi_pruning.m
// =====================================================================
//
//     magma -b tests/test_gpiphi_pruning.m      (run from magma/)
//
// Gpiphi now enumerates subgroups of AbG / e*AbG of index dividing #C, and
// (disc) skips kernels missing Smin.  Neither may change the set of
// b(pi, phi) values that matter.  For each group this compares, in both
// orderings, the multiset of NONZERO b-values over Gpiphi's pairs with the
// multiset over GpiphiReference's pairs (the old enumeration of every
// subgroup of AbG), using the reference orbit counters on both sides so
// that only the enumeration differs.  Zero b-values are exactly the pairs
// the MinReps filter is allowed to drop.

load "lib/records.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/disc/orbits.m";

// The prp reference counter, inlined so that both orbits.m files need not
// be loaded together (they define the same production names).
PrpReference := function(ebp)
    G := ebp`G; C := ebp`C; pi := ebp`pi; phi := ebp`phi; f := ebp`f;
    N := Kernel(pi);
    if #N eq 1 then return 0; end if;
    cls := Classes(N); cm := ClassMap(N);
    acts := [ < G!(phi(c) @@ pi), IntegerRing()!(f(c)) > : c in Generators(C) ];
    visited := { cm(Id(N)) };
    orbits := 0;
    for i in [1..#cls] do
        if i in visited then continue; end if;
        orbits +:= 1; Include(~visited, i); queue := [i]; k := 1;
        while k le #queue do
            rep := cls[queue[k]][3]; k +:= 1;
            for a in acts do
                j := cm(a[1]^(-1) * rep^a[2] * a[1]);
                if not j in visited then Include(~visited, j); Append(~queue, j); end if;
            end for;
        end while;
    end for;
    return orbits;
end function;

CASES := [ <6,5>, <8,10>, <8,23>, <10,20>, <12,131>, <12,19>, <15,95>, <16,1192>, <20,27> ];
failures := 0;

for c in CASES do
    n := c[1]; i := c[2];
    G := TransitiveGroup(n, i);

    // disc
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    _, reps, _, _ := MinIndexClasses(G);
    Tn := Gpiphi(G, d : MinReps := reps);
    To := GpiphiReference(G, d);
    bn := [];
    for ebp in Tn do _, b := bpiphi(ebp, Smin); if b ne 0 then Append(~bn, b); end if; end for;
    bo := [];
    for ebp in To do _, b := bpiphi(ebp, Smin); if b ne 0 then Append(~bo, b); end if; end for;
    Sort(~bn); Sort(~bo);
    if bn ne bo then
        printf "  FAIL %oT%o disc: pruned %o vs reference %o\n", n, i, bn, bo;
        failures +:= 1;
    end if;

    // prp
    e := Exponent(G);
    Tn := Gpiphi(G, e);
    To := GpiphiReference(G, e);
    bn := [];
    for ebp in Tn do b := PrpReference(ebp); if b ne 0 then Append(~bn, b); end if; end for;
    bo := [];
    for ebp in To do b := PrpReference(ebp); if b ne 0 then Append(~bo, b); end if; end for;
    Sort(~bn); Sort(~bo);
    if bn ne bo then
        printf "  FAIL %oT%o prp: pruned %o vs reference %o\n", n, i, bn, bo;
        failures +:= 1;
    end if;

    printf "  %oT%o: prp %o pairs (reference %o)\n", n, i, #Tn, #To;
end for;

printf "test_gpiphi_pruning: %o failures\n", failures;
assert failures eq 0;
print "test_gpiphi_pruning: PASS";
quit;
