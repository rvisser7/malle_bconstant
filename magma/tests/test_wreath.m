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

// The base group of T wr C2, as a normal subgroup of G of order (#T)^2.
//
// Order alone does NOT pin it down.  (S5 wr C2)^ab = C2 x C2, so there are
// three normal subgroups of index 2 in S5 wr C2, all of order 120^2: the
// base group, and the kernels of the two sign-type characters.  Only the
// base group fixes the blocks, so it is the intransitive one -- the other
// two contain block-swapping elements.  An earlier version of this file
// took the first subgroup of the right order and fed IsWreathResidual a K
// that is not T x T^g, which it then correctly rejected.
BaseGroupOfWreath := function(G, degT)
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M ne #G div 2 then continue; end if;
        if IsTransitive(M) then continue; end if;
        orbs := Orbits(M);
        if #orbs eq 2 and forall{ o : o in orbs | #o eq degT } then
            return M;
        end if;
    end for;
    error "no intransitive normal subgroup with two blocks of size", degT;
end function;

CheckWreath := procedure(T, name)
    G := WreathProduct(T, CyclicGroup(2));
    K := BaseGroupOfWreath(G, Degree(T));

    // The fixture itself is asserted, so a bad K reports as a bad fixture
    // rather than as a failure of the code under test.
    assert #K eq (#T)^2;

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
K := BaseGroupOfWreath(G, 5);
Q, pi := quo< G | K >;
ebp := rec< EmbeddingProb | G := G, B := Q, pi := pi >;
ok, why := StructuralResidualIsProperlySolvable(ebp);
printf "  S5 wr C2 certificate: %o (%o)\n", ok, why;
assert ok;

// Negative control: one of the OTHER index-2 normal subgroups is not
// T x T^g, and shape (3) must decline it rather than find a spurious T.
for R in NormalSubgroups(G) do
    M := R`subgroup;
    if #M eq #G div 2 and IsTransitive(M) then
        QM, piM := quo< G | M >;
        okM := IsWreathResidual(G, M, piM);
        printf "  transitive index-2 normal subgroup: detected=%o (expected false)\n", okM;
        assert not okM;
        break;
    end if;
end for;

print "test_wreath: PASS";
quit;
