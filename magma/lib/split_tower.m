// =====================================================================
// Iterated split reduction
// =====================================================================
//
// Requires (load first): records.m, splitting.m
//
// Given the embedding problem
//
//     1 -> N -> G -pi-> B -> 1,     N = Ker(pi),
//
// repeatedly look for a nontrivial M <= N, normal in G, admitting a
// complement in G, and replace the problem by
//
//     1 -> N/M -> G/M -> B -> 1.
//
// SOUNDNESS OF THE REDUCTION.  If G = M : H and psi : G_Q -> G/M solves the
// reduced problem, then s . psi solves the original, where s : G/M -> G is
// the splitting: pi factors through G/M as pibar, and pi . s = pibar, so
// pi . (s . psi) = pibar . psi = phi.  So reduced-solvable => solvable.
//
// PROPERNESS.  s . psi is not surjective onto G (its image is the
// complement), so the above certifies solvable, not properly solvable, and
// Conjecture 6 counts surjective liftings.  The repair is to climb back up
// the tower: we hold a PROPER solution psi : G_Q ->> G/M of the reduced
// problem, cutting out some field K with Gal(K/Q) = G/M, and ask for a
// proper solution of the layer
//
//     1 -> M -> G -> G/M -> 1,    lifting psi.
//
// The layer is SPLIT, hence solvable (by s . psi), for every psi.  What we
// do NOT control is K: it is whatever field the rest of the tower produced.
// So a layer may be peeled off only under hypotheses that hold for every
// such K.  Two are used (see LayerAllowed below):
//
//   (1) M NILPOTENT.  [NSW08, Thm (9.6.10)]: for K|k finite Galois and
//       phi : G_k ->> G(K|k) the natural projection, every embedding problem
//       with finite nilpotent kernel that has a solution can be solved
//       properly.  No further hypothesis -- in particular none on K.
//
//   (2) #M ODD, and exp(M) prime to #mu(K).  [NSW08, Cor (9.5.8)(ii)(c)]:
//       with Gamma = G(K|k) finite and H separable, prosolvable, of finite
//       exponent prime to #mu(K), a SPLIT extension has a proper solution.
//       M of odd order is solvable (Feit-Thompson).  The condition is on the
//       roots of unity of the TOP field K, not of Q, and K is unknown, so we
//       require for every prime p | #M that mu_p cannot lie in K: if it did,
//       Q(mu_p) would lie in K and C_{p-1} would be a quotient of G/M, and a
//       finite abelian group has a C_n quotient iff n divides its exponent.
//       So: p - 1 must not divide Exponent((G/M)^ab).  (p = 2 is excluded by
//       oddness, since mu_2 = {+-1} lies in every K.)  This is restrictive --
//       p = 3 already forces (G/M)^ab to have odd exponent -- but sound.
//
// Note that Wang's Theorem 4.2 states the coprimality with mu(k).  That is
// harmless in her setting (K inside the cyclotomic Z^-extension; over Q
// totally real, so mu(K) = mu(Q) = {+-1}) but it is NOT the hypothesis of
// (9.5.8) in general, and it would be wrong to use "#M odd" alone here.
//
// Some hypothesis on M cannot simply be dropped.  With B trivial, the split
// problem 1 -> G -> G -> 1 -> 1 is properly solvable exactly when G is a
// Galois group over Q, so an unrestricted "split => properly solvable" would
// be assuming the inverse Galois problem.
//
// Nor may we simply take the LARGEST complemented M at each step: a bigger M
// is worthless if a finer tower exists below it.  12T130 = C_3 wr C_2^2 is
// the example.  For N = C_3^4 : C_2 of index 2 in G, N is itself
// complemented (by any involution of V outside N) but a greedy step ends the
// tower there; whereas C_3^4 first, then C_2, reduces to the trivial kernel.
// So: largest first, and backtrack.

// May the complemented normal subgroup M of G be peeled off?  (1) or (2)
// above.  Cheap tests first; the quotient is only formed for odd,
// non-nilpotent M.
LayerAllowed := function(G, M)
    if IsNilpotent(M) then return true; end if;                // (9.6.10)
    if IsEven(#M) then return false; end if;
    e := Exponent(AbelianQuotient(quo< G | M >));              // (9.5.8)
    return forall{ p : p in PrimeDivisors(#M) | e mod (p - 1) ne 0 };
end function;

// Normal M <= N, M != 1, allowed by LayerAllowed and admitting a complement
// in G, largest first.
AdmissibleComplementedCandidates := function(G, N)
    cands := [];
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M eq 1 or #M eq #G then continue; end if;
        if not (M subset N) then continue; end if;
        if not LayerAllowed(G, M) then continue; end if;
        ok := IsSplitKernel(G, M);
        if ok then Append(~cands, M); end if;
    end for;
    Sort(~cands, func< X, Y | #Y - #X >);
    return cands;
end function;

// Old name, kept for the diagnostics (inspect_stalled.m, why_no_candidates.m).
NilpotentComplementedCandidates := AdmissibleComplementedCandidates;

// Depth-first search for towers of complemented admissible layers.
//
// STATE.  A node of the search is a normal subgroup K of the ORIGINAL group
// G0 (the cumulative kernel quotiented out so far), and the problem at that
// node is 1 -> Ker(pi0)/K -> G0/K -> B -> 1.  Different orders of peeling
// off layers (M1 then M2, or M2 then M1) reach the same K, and the search
// used to explore each of them again, which is exponential in the number of
// layers.  `seen` records every K already expanded, and a K is expanded at
// most once.
//
// Memoisation caveat: a K first reached near the depth limit is not
// re-expanded if later reached with more depth to spare.  That can only lose
// leaves, i.e. certificates; it can never produce a false one.  Depth 16 is
// far above the number of layers in any group in the data.
//
// Returns:
//   done    true iff some branch reduced the kernel to 1
//   leaves  if done, the single fully reduced problem; otherwise the DEAD
//           ENDS of every branch, up to cap, as a list of <G, pi>
//   seen    the updated memo
//
// WHY ALL THE LEAVES.  Different branches leave different residuals, and
// which of them a certificate can handle does not follow from the
// residual's size.  A proper solution of ANY leaf climbs back up its own
// branch to a proper solution of the original, so the certificate chain is
// simply offered every leaf and stops at the first that works.
// Insolvability travels the other way and is likewise inherited from any
// leaf, so the local machinery uses them all too.

InSubgroupList := function(L, K)
    for x in L do
        if x eq K then return true; end if;
    end for;
    return false;
end function;

TowerLeavesFrom := function(G0, pi0, B, K, depth, cap, seen)
    if #K eq 1 then
        GK := G0; piK := pi0; qK := IdentityHomomorphism(G0);
    else
        GK, qK := quo< G0 | K >;
        piK := hom< GK -> B | [ pi0(GK.i @@ qK) : i in [1..Ngens(GK)] ] >;
    end if;

    N := Kernel(piK);
    if #N eq 1 then return true, [* <GK, piK> *], seen; end if;
    if depth le 0 then return false, [* <GK, piK> *], seen; end if;

    cands := AdmissibleComplementedCandidates(GK, N);
    if #cands eq 0 then return false, [* <GK, piK> *], seen; end if;

    leaves := [* *];
    for M in cands do
        K1 := M @@ qK;                       // cumulative kernel, inside G0
        if InSubgroupList(seen, K1) then continue; end if;
        Append(~seen, K1);
        done, L, seen := $$(G0, pi0, B, K1, depth - 1, cap, seen);
        if done then return true, L, seen; end if;
        for x in L do
            if #leaves lt cap then Append(~leaves, x); end if;
        end for;
        if #leaves ge cap then break; end if;
    end for;
    // May be empty if every child had already been expanded elsewhere: its
    // dead ends were collected on that earlier visit.
    return false, leaves, seen;
end function;

// The raw tower for a pair: <fullySplit, list of <G, pi>>.  It depends on
// (G, pi) only, NOT on phi, so callers that handle several phi over one pi
// should compute it once and pass it back in via the Raw parameter below.
SplitTowerRaw := function(ebp : Cap := 24)
    G := ebp`G;
    triv := sub< G | Id(G) >;
    done, L, seen := TowerLeavesFrom(G, ebp`pi, ebp`B, triv, 16, Cap, [* triv *]);
    if #L eq 0 then L := [* <G, ebp`pi> *]; end if;
    return < done, L >;
end function;

// Every dead end of the tower, as embedding problems sharing the original's
// B, C, f, phi and d.  Second return value says whether the kernel reduced
// to 1, in which case there is exactly one leaf and it is trivial.
//
// Raw: optional precomputed SplitTowerRaw(ebp) for the same pi (any phi).
SplitReductionLeaves := function(ebp : Cap := 24, Raw := false)
    R := Raw;
    if Type(R) eq BoolElt then
        R := SplitTowerRaw(ebp : Cap := Cap);
    end if;
    fullySplit := R[1];
    leaves := [* *];
    for x in R[2] do
        Append(~leaves, rec< EmbeddingProb |
            B := ebp`B, G := x[1], C := ebp`C, f := ebp`f,
            pi := x[2], phi := ebp`phi, d := ebp`d >);
    end for;
    return leaves, fullySplit;
end function;

// Single-residual view, kept for callers that want one problem to report on:
// the leaf with the smallest kernel.  Nothing decides anything on the basis
// of this choice -- CertifyAdmissible and LocalVerdictWithQuotients both
// work through SplitReductionLeaves.
MaximalSplitReduction := function(ebp : Raw := false)
    leaves, fullySplit := SplitReductionLeaves(ebp : Raw := Raw);
    best := leaves[1];
    for e in leaves do
        if #Kernel(e`pi) lt #Kernel(best`pi) then best := e; end if;
    end for;
    return best, fullySplit;
end function;
