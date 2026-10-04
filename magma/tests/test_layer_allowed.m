// =====================================================================
// tests/test_layer_allowed.m
// =====================================================================
//
//     magma -b tests/test_layer_allowed.m      (run from magma/)
//
// LayerAllowed(G, M) decides whether a complemented layer may be peeled off
// in the split tower:
//   (1) M nilpotent                                    [NSW08 (9.6.10)]
//   (2) #M odd and, for every prime p | #M, p - 1 does not divide
//       Exponent((G/M)^ab), so mu_p cannot lie in the field K of the
//       reduced solution                                [NSW08 (9.5.8)]
// F21 = C7 : C3 is the smallest odd, non-nilpotent kernel.

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";

failures := 0;
Check := procedure(name, got, want, ~failures)
    printf "  %-40o %o (expected %o)\n", name, got, want;
    if got ne want then failures +:= 1; end if;
end procedure;

// F21 on 7 points: x -> x+1 and x -> 2x on Z/7 (points = residues + 1).
F := sub< Sym(7) | (1,2,3,4,5,6,7), (2,3,5)(4,7,6) >;
assert #F eq 21 and not IsNilpotent(F);

NonAbelian21 := function(G)
    return [ R`subgroup : R in NormalSubgroups(G)
             | #R`subgroup eq 21 and not IsAbelian(R`subgroup) ];
end function;

// (2) fires: G/M = C3, exponent 3; p = 3, 7 give p - 1 = 2, 6, neither | 3.
G := DirectProduct(F, CyclicGroup(3));
Ms := NonAbelian21(G);
assert #Ms gt 0;
for M in Ms do
    Check("F21 x C3, M = F21-type: allowed", LayerAllowed(G, M), true, ~failures);
    Check("   ... and complemented", IsSplitKernel(G, M), true, ~failures);
end for;

// (2) refused: G/M = C2, and 3 - 1 = 2 divides 2, so Q(sqrt -3) could be
// the quadratic subfield of K and mu_3 would lie in K.
G := DirectProduct(F, CyclicGroup(2));
Ms := NonAbelian21(G);
assert #Ms eq 1;
Check("F21 x C2, M = F21: allowed", LayerAllowed(G, Ms[1]), false, ~failures);

// (1): nilpotent layers are always allowed, whatever G/M is.
C7 := sub< F | F.1 >;
Check("F21, M = C7 (nilpotent): allowed", LayerAllowed(F, C7), true, ~failures);
G := DirectProduct(F, CyclicGroup(2));
Check("F21 x C2, M = C7 (nilpotent): allowed",
      LayerAllowed(G, sub< G | G!(1,2,3,4,5,6,7) >), true, ~failures);

// Even, non-nilpotent: never allowed.
G := DirectProduct(Sym(3), CyclicGroup(3));
M := sub< G | G!(1,2,3), G!(1,2) >;
assert #M eq 6 and IsNormal(G, M);
Check("S3 x C3, M = S3: allowed", LayerAllowed(G, M), false, ~failures);

// The tower uses it: F21 x C3 -> C3 (kernel F21) now reduces to the trivial
// kernel, where before (nilpotent layers only) it could at best peel C7.
G := DirectProduct(F, CyclicGroup(3));
M := NonAbelian21(G)[1];
Q, q := quo< G | M >;
pi := q;
cands := AdmissibleComplementedCandidates(G, Kernel(pi));
Check("F21 x C3: largest candidate has order", #cands[1], 21, ~failures);

// Search bookkeeping: hitting the depth limit is now recorded explicitly,
// while the ordinary search proves this tower fully split.  The dummy C/f/phi
// fields are unused by SplitTowerRaw; they only complete the EmbeddingProb
// record.
idQ := IdentityHomomorphism(Q);
ebp := rec< EmbeddingProb |
    B := Q, G := G, C := Q, f := idQ, pi := pi, phi := idQ, d := 1
>;
R0 := SplitTowerRaw(ebp : Depth := 0);
Check("split tower: depth-0 search is incomplete",
      SplitTowerSearchComplete(R0), false, ~failures);
R := SplitTowerRaw(ebp);
Check("split tower: F21 x C3 reaches trivial kernel", R[1], true, ~failures);
Check("split tower: successful search is complete",
      SplitTowerSearchComplete(R), true, ~failures);

printf "test_layer_allowed: %o failures\n", failures;
assert failures eq 0;
print "test_layer_allowed: PASS";
quit;
