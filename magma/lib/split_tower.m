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
// PROPERNESS, AND THE ONE CITATION EVERYTHING RESTS ON.  s . psi is not
// surjective onto G (its image is the complement), so the above certifies
// solvable, not properly solvable, and Conjecture 6 counts surjective
// liftings.  The repair is to climb back up the tower: each layer is a
// SPLIT embedding problem, hence solvable, and we then invoke
//
//     (*)  over a global field, a solvable embedding problem with finite
//          NILPOTENT kernel is properly solvable.
//
// which is why every layer is required to have nilpotent kernel.
//
//   >>> BEFORE PUBLISHING, PIN DOWN (*).  This file used to cite
//   >>> [NSW08, (9.6.10)] for it.  Wang cites [NSW08, Cor. (9.5.8)] in the
//   >>> proofs of her Theorems 4.1 and 4.2, and in both places she carries
//   >>> extra hypotheses: kernel SOLVABLE and (|mu(k)|, |Ker pi|) = 1, which
//   >>> over Q means ODD ORDER.  If the coprimality hypothesis is genuinely
//   >>> needed then every layer of even order is uncertified, which is most
//   >>> of them, and BWlowerSplit is not a lower bound.  Quote the exact
//   >>> statement here once it is settled.
//
// The nilpotent hypothesis cannot simply be dropped.  With B trivial, the
// split problem 1 -> G -> G -> 1 -> 1 is properly solvable exactly when G is
// a Galois group over Q, so an unrestricted "split => properly solvable"
// would be assuming the inverse Galois problem.  Nilpotent layers are safe
// on that count: nilpotent groups are realisable over Q.
//
// Nor may we simply take the LARGEST complemented M at each step: a bigger M
// is worthless if a finer tower exists below it.  12T130 = C_3 wr C_2^2 is
// the example.  For N = C_3^4 : C_2 of index 2 in G, N is itself
// complemented (by any involution of V outside N) but a greedy step ends the
// tower there; whereas C_3^4 first, then C_2, reduces to the trivial kernel.
// So: largest first, and backtrack.

// Nilpotent normal M <= N, M != 1, admitting a complement in G, largest first.
NilpotentComplementedCandidates := function(G, N)
    cands := [];
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M eq 1 or #M eq #G then continue; end if;
        if not (M subset N) then continue; end if;
        if not IsNilpotent(M) then continue; end if;
        ok := IsSplitKernel(G, M);
        if ok then Append(~cands, M); end if;
    end for;
    Sort(~cands, func< X, Y | #Y - #X >);
    return cands;
end function;

// Depth-first search for a tower of complemented nilpotent layers reducing
// the kernel to the trivial group.  Returns:
//   done  true iff the kernel was reduced to 1
//   G, pi the reduced problem: fully reduced if done, else the DEEPEST
//         reduction found over all branches, i.e. the one with the smallest
//         residual kernel.
//
// FIXED: the failure handoff used to be whatever the FIRST candidate
// produced, although the doc comment promised the deepest.  Since the
// residual is what certificates/ then gets to work on, and a different
// branch can leave a certifiable residual where another leaves an opaque
// one, this was silently costing lower bounds.
ReduceTower := function(G, pi, B, depth)
    N := Kernel(pi);
    if #N eq 1 then return true, G, pi; end if;
    if depth le 0 then return false, G, pi; end if;

    cands := NilpotentComplementedCandidates(G, N);
    if #cands eq 0 then return false, G, pi; end if;

    bestG := G; bestpi := pi; bestKer := #N; haveBest := false;
    for M in cands do
        G1, q := quo< G | M >;
        // pi kills M, so it descends to G1.
        pi1 := hom< G1 -> B | [ pi(G1.i @@ q) : i in [1..Ngens(G1)] ] >;
        done, G2, pi2 := $$(G1, pi1, B, depth - 1);
        if done then return true, G2, pi2; end if;
        k2 := #Kernel(pi2);
        if (not haveBest) or (k2 lt bestKer) then
            bestG := G2; bestpi := pi2; bestKer := k2; haveBest := true;
        end if;
    end for;
    return false, bestG, bestpi;
end function;

// Returns:
//   ebp1       the reduced embedding problem (same B, C, f, phi)
//   fullySplit true iff the kernel reduced to 1 through nilpotent layers
MaximalSplitReduction := function(ebp)
    fullySplit, G1, pi1 := ReduceTower(ebp`G, ebp`pi, ebp`B, 16);
    ebp1 := rec< EmbeddingProb |
        B := ebp`B, G := G1, C := ebp`C, f := ebp`f, pi := pi1, phi := ebp`phi, d := ebp`d
    >;
    return ebp1, fullySplit;
end function;
