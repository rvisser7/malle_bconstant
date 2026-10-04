// =====================================================================
// tests/test_local_tame_reference.m
// =====================================================================
//
//     magma -b tests/test_local_tame_reference.m      (run from magma/)
//
// The production tame solver works with conjugacy classes and centralisers.
// Compare it against the literal definition on small groups: enumerate every
// X,Y in G with prescribed quotient images and test X Y X^-1 = Y^p.
// This is intentionally independent of the optimisation in local_tame.m.

load "lib/records.m";
load "lib/local_tame.m";

BruteTame := function(ebp, p, bX, bY)
    G := ebp`G; pi := ebp`pi;
    for X in G do
        if pi(X) ne bX then continue; end if;
        for Y in G do
            if pi(Y) ne bY then continue; end if;
            if X*Y*X^(-1) eq Y^p then
                return true;
            end if;
        end for;
    end for;
    return false;
end function;

CheckGroup := procedure(G, name, ~failures, ~checked)
    N := DerivedGroup(G);
    B, pi := quo< G | N >;
    assert IsAbelian(B);

    // Only G, B and pi are used by IsLocalLiftableTameByBImages.  Filling the
    // remaining fields keeps this a bona-fide EmbeddingProb for diagnostics.
    idB := IdentityHomomorphism(B);
    ebp := rec< EmbeddingProb |
        G := G, B := B, pi := pi, C := B, f := idB, phi := idB, d := 1
    >;

    for p in [2,3,5,7] do
        for bX in B do
            for bY in B do
                got := IsLocalLiftableTameByBImages(ebp, p, bX, bY);
                want := BruteTame(ebp, p, bX, bY);
                checked +:= 1;
                if got ne want then
                    printf "  FAIL %o p=%o bX=%o bY=%o: optimised=%o brute=%o\n",
                           name, p, bX, bY, got, want;
                    failures +:= 1;
                end if;
            end for;
        end for;
    end for;
end procedure;

failures := 0;
checked := 0;

CheckGroup(Sym(3),                 "S3",       ~failures, ~checked);
CheckGroup(TransitiveGroup(4, 3), "D8",       ~failures, ~checked);
CheckGroup(Alt(4),                 "A4",       ~failures, ~checked);
CheckGroup(Sym(4),                 "S4",       ~failures, ~checked);
CheckGroup(DirectProduct(CyclicGroup(4), CyclicGroup(2)),
           "C4 x C2", ~failures, ~checked);

printf "test_local_tame_reference: %o image-pairs checked, %o failures\n",
       checked, failures;
assert failures eq 0;
print "test_local_tame_reference: PASS";
quit;
