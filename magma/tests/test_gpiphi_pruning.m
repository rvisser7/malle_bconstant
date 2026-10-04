// =====================================================================
// tests/test_gpiphi_pruning.m
// =====================================================================
//
//     magma -b tests/test_gpiphi_pruning.m      (run from magma/)
//
// Gpiphi now enumerates subgroups of AbG / e*AbG of index dividing #C, and
// (disc) skips kernels missing Smin.  Neither may change the actual
// (pi,phi)-pairs that matter.  Comparing only the multiset of b-values is NOT
// enough for Wang's constant: two different phi can have the same b(pi,phi)
// but different liftability.  So this test compares the pairs themselves,
// up to the canonical quotient isomorphism determined by their common kernel,
// and also checks the associated NONZERO b-values.  Zero b-values are exactly
// the pairs the MinReps filter is allowed to drop.

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

// Find in ebp`C the cyclotomic element with a prescribed residue modulo d.
// This avoids assuming that two independent calls to MultiplicativeGroup have
// literally the same parent group.
CyclotomicElementWithResidue := function(ebp, a)
    d := ebp`d;
    aa := a mod d;
    for c in ebp`C do
        if (IntegerRing()!ebp`f(c)) mod d eq aa then return c; end if;
    end for;
    error Sprintf("no cyclotomic element with residue %o mod %o", aa, d);
end function;

// SamePair(P,Q) means that P and Q have the same kernel N in G and that,
// under the canonical isomorphism G/N -> G/N induced by the identity on G,
// their cyclotomic quotient maps agree.  Concretely, for c in C_P choose any
// x with pi_P(x)=phi_P(c), then require pi_Q(x)=phi_Q(c') where c' has the
// same residue modulo d.  Equality on generators is enough.
SamePair := function(P, Q)
    if Kernel(P`pi) ne Kernel(Q`pi) then return false; end if;
    for c in Generators(P`C) do
        cQ := CyclotomicElementWithResidue(Q, IntegerRing()!P`f(c));
        x := P`phi(c) @@ P`pi;
        if Q`pi(x) ne Q`phi(cQ) then return false; end if;
    end for;
    return true;
end function;

// Compare two generic sequences of <ebp,b> as multisets of actual pairs.
SamePairMultiset := function(A, B)
    if #A ne #B then return false; end if;
    used := {};
    for x in A do
        found := 0;
        for j := 1 to #B do
            if j in used then continue; end if;
            if x[2] eq B[j][2] and SamePair(x[1], B[j][1]) then
                found := j;
                break;
            end if;
        end for;
        if found eq 0 then return false; end if;
        Include(~used, found);
    end for;
    return true;
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
    An := [* *];
    for ebp in Tn do
        _, b := bpiphi(ebp, Smin);
        if b ne 0 then Append(~An, < ebp, b >); end if;
    end for;
    Ao := [* *];
    for ebp in To do
        _, b := bpiphi(ebp, Smin);
        if b ne 0 then Append(~Ao, < ebp, b >); end if;
    end for;
    if not SamePairMultiset(An, Ao) then
        printf "  FAIL %oT%o disc: pruned/reference pair sets differ (%o vs %o)\n",
               n, i, #An, #Ao;
        failures +:= 1;
    end if;

    // prp
    e := Exponent(G);
    Tn := Gpiphi(G, e);
    To := GpiphiReference(G, e);
    An := [* *];
    for ebp in Tn do
        b := PrpReference(ebp);
        if b ne 0 then Append(~An, < ebp, b >); end if;
    end for;
    Ao := [* *];
    for ebp in To do
        b := PrpReference(ebp);
        if b ne 0 then Append(~Ao, < ebp, b >); end if;
    end for;
    if not SamePairMultiset(An, Ao) then
        printf "  FAIL %oT%o prp: pruned/reference pair sets differ (%o vs %o)\n",
               n, i, #An, #Ao;
        failures +:= 1;
    end if;

    printf "  %oT%o: prp %o pairs (reference %o)\n", n, i, #Tn, #To;
end for;

printf "test_gpiphi_pruning: %o failures\n", failures;
assert failures eq 0;
print "test_gpiphi_pruning: PASS";
quit;
