// =====================================================================
// tests/test_wreath.m
// =====================================================================
//
//     magma -b tests/test_wreath.m         (run from magma/)
//
// Shape (3) of certificates/structural.m had two bugs and, as far as the
// data shows, had never actually run: the element outside K was picked by
// Rep from a set with Id unioned in as an emptiness guard, so Rep could
// return the guard; and "#T^2" was unparenthesised.  Exercise the branch.

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/certificates/structural.m";

// The base group of a wreath product T wr C2, as a normal subgroup of order
// #T^2.
BaseGroupOfWreath := function(G, ordT)
    for R in NormalSubgroups(G) do
        if #R`subgroup eq ordT^2 then return R`subgroup; end if;
    end for;
    error "no normal subgroup of the expected order";
end function;

CheckWreath := procedure(T, name)
    G := WreathProduct(T, CyclicGroup(2));
    K := BaseGroupOfWreath(G, #T);
    Q, pi := quo< G | K >;

    assert #Q eq 2;

    ok, T0 := IsWreathResidual(G, K, pi);
    printf "  %o: detected=%o, #T0=%o (expected %o)\n", name, ok, #T0, #T;
    assert ok;
    assert #T0 eq #T;
end procedure;

print "test_wreath: shape (3) detection";
CheckWreath(CyclicGroup(3), "C3 wr C2");
CheckWreath(Sym(5),         "S5 wr C2");

// S5 wr C2: split, non-direct, kernel S5 x S5, T = S5 is in the regular
// table, so the certificate should fire.  This is the path that the Rep bug
// silently disabled.
G := WreathProduct(Sym(5), CyclicGroup(2));
K := BaseGroupOfWreath(G, 120);
Q, pi := quo< G | K >;
ebp := rec< EmbeddingProb | G := G, B := Q, pi := pi >;
ok, why := StructuralResidualIsProperlySolvable(ebp);
printf "  S5 wr C2 certificate: %o (%o)\n", ok, why;
assert ok;

print "test_wreath: PASS";
quit;
