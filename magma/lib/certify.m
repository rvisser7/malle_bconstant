// =====================================================================
// certify.m  --  the certificate chain
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m,
//   local_verdict.m, and every certificate module it dispatches to:
//   certificates/shared.m, certificates/structural.m,
//   certificates/central.m, certificates/q8.m.  Load this LAST of them.
//
// CertifyAdmissible answers one question: is this (pi, phi) pair PROPERLY
// solvable?  A true return may raise BWlowerSplit.
//
// THE ONE ASYMMETRY THAT MATTERS.  A local test may never RAISE
// BWlowerSplit on its own, and a certificate may never LOWER BWupperLocal.
// certificates/central.m looks like a violation of the first rule and is
// not: it uses local data only in the direction where a lift is exhibited
// at every place, which over Q with a central kernel is equivalent to
// proper solvability.  Every other certificate is field-theoretic or
// group-theoretic.  See "The two bounds" in magma/README.md.
//
// Adding a certificate is now a new file under certificates/ plus one line
// in CertificateChain, rather than another hand-written if-block.  Each
// entry has the uniform signature
//
//     f(ebp1, d, policy) -> ok, reason
//
// with ebp1 the maximally split-reduced residual.

CertEntryStructural := function(ebp1, d, policy)
    ok, why := StructuralResidualIsProperlySolvable(ebp1);
    return ok, why;
end function;

CertEntryCentral := function(ebp1, d, policy)
    ok, why := CertifyCentralResidual(ebp1, policy);
    return ok, why;
end function;

CertEntryQ8 := function(ebp1, d, policy)
    ok, why := CertifyResidualQ8(ebp1, d);
    return ok, why;
end function;

// Order: cheapest and most general first.  central before q8 because it
// subsumes the Q8 (a) shape and a good deal besides.
CertificateChain := [*
    < "structural", CertEntryStructural >,
    < "central",    CertEntryCentral    >,
    < "q8",         CertEntryQ8         >
*];

// Returns: ok, reason, ebp1.
//
// The chain is offered EVERY dead end of the split tower, not one chosen
// representative.  A proper solution of any leaf climbs back up its own
// branch to a proper solution of the original, so stopping at the first leaf
// that certifies is correct and choosing a leaf in advance is not: which
// residual a certificate can handle does not follow from its size.  See the
// note above TowerLeaves in split_tower.m.
//
// ebp1 is handed back so callers do not repeat the reduction for their
// diagnostics: the certifying leaf on success, the smallest-kernel leaf on
// failure.
//
// Raw: optional precomputed SplitTowerRaw for this pi (see split_tower.m).
//
// SUPPLEMENTS (new, OFF by default: SupplementDepth := 0).  When no leaf
// certifies, each leaf 1 -> N1 -> G1 -> B is offered once more through a
// SUBGROUP: for a maximal subgroup X of G1 not containing F := Fit(N1),
// the problem (X, pi1|X, phi) is certified recursively, depth-limited.
//
//   Lemma.  Let M <= N1 be nilpotent and normal in G1, and X <= G1 with
//   X M = G1.  If (X, pi1|X, phi) is properly solvable, so is
//   (G1, pi1, phi).
//
//   Proof.  Let M~ be the relatively free group of class c(M) and exponent
//   exp(M) on generators indexed by X x Y, Y a generating set of M; it is
//   finite and nilpotent, X permutes its generators, and (x, y) -> x y x^-1
//   extends to an X-equivariant surjection f : M~ ->> M.  Then
//   (m, x) -> f(m) x is a surjection Theta : M~ : X ->> G1, since X M = G1,
//   and pi1 . Theta kills M~.  A proper solution psi : G_Q ->> X lifts
//   through the SPLIT layer with NILPOTENT kernel M~ to a proper
//   psi~ : G_Q ->> M~ : X [NSW08 (9.6.10)], and Theta . psi~ is a proper
//   solution for G1.  []
//
// M ranges over nilpotent normal subgroups inside N1, all of which lie in
// F = Fit(N1) (characteristic in N1, so normal in G1); "X F = G1" is the
// weakest form of the hypothesis, and for maximal X it says F is not in X.
// A supplement S lies in some maximal X with X F = G1, and the lemma
// applies inside X again (Dedekind), so maximal subgroups up to
// conjugacy suffice.  Conjugate X give isomorphic problems (B abelian).
//
// A complement is the case X meet M = 1, so this strictly extends the split
// tower.  The X-problems are SUBproblems, not quotients: insolvability does
// NOT pass from them to G1, which is why they are only ever used here, to
// raise the lower bound, and never in LocalVerdictWithQuotients.
CertifyAdmissible := function(ebp, d : Policy := DefaultLocalPolicy, Raw := false,
                                       SupplementDepth := 0)
    towerRaw := Raw;
    if Type(towerRaw) eq BoolElt then towerRaw := SplitTowerRaw(ebp); end if;
    leaves, fullySplit := SplitReductionLeaves(ebp : Raw := towerRaw);
    if fullySplit then
        return true, "split tower (nilpotent / odd / GAR layers) to trivial kernel", leaves[1];
    end if;

    best := leaves[1];
    for e in leaves do
        if #Kernel(e`pi) lt #Kernel(best`pi) then best := e; end if;
    end for;

    reasons := "";
    for k := 1 to #leaves do
        ebp1 := leaves[k];
        for entry in CertificateChain do
            ok, why := entry[2](ebp1, d, Policy);
            if ok then
                return true,
                       Sprintf("leaf %o of %o (#G = %o, #Ker = %o), %o: %o",
                               k, #leaves, #ebp1`G, #Kernel(ebp1`pi),
                               entry[1], why),
                       ebp1;
            end if;
            if k eq 1 then
                reasons := reasons cat entry[1] cat ": " cat why cat "; ";
            end if;
        end for;
    end for;

    if #leaves gt 1 then
        reasons := reasons cat Sprintf("(and no certificate on any of the "
                                       cat "other %o leaves)", #leaves - 1);
    end if;
    if not SplitTowerSearchComplete(towerRaw) then
        reasons := reasons cat "; split-tower search truncated by Depth/Cap";
    end if;

    if SupplementDepth gt 0 then
        for k := 1 to #leaves do
            ebp1 := leaves[k];
            G1 := ebp1`G;
            N1 := Kernel(ebp1`pi);
            F := FittingSubgroup(N1);
            if #F eq 1 then continue; end if;
            for R in MaximalSubgroups(G1) do
                X := R`subgroup;
                if F subset X then continue; end if;
                piX := hom< X -> ebp1`B | [ ebp1`pi(X.i) : i in [1..Ngens(X)] ] >;
                subprob := rec< EmbeddingProb |
                    B := ebp1`B, G := X, C := ebp1`C, f := ebp1`f,
                    pi := piX, phi := ebp1`phi, d := ebp1`d >;
                ok, why, _ := $$(subprob, d : Policy := Policy,
                                 SupplementDepth := SupplementDepth - 1);
                if ok then
                    return true,
                           Sprintf("leaf %o of %o (#G = %o, #Ker = %o), supplement "
                                   cat "of Fit(Ker) (#X = %o, #Fit = %o): %o",
                                   k, #leaves, #G1, #N1, #X, #F, why),
                           ebp1;
                end if;
            end for;
        end for;
        reasons := reasons cat "; no supplement certified";
    end if;
    return false, reasons, best;
end function;
