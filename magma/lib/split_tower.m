// =====================================================================
// Iterated split reduction
// =====================================================================
//
// Requires (load first): records.m, splitting.m
//
// Generalises IsTwoStepSplitReduction.  Given the embedding problem
//
//     1 -> N -> G -pi-> B -> 1,     N = Ker(pi),
//
// we repeatedly look for a nontrivial M <= N, normal in G, admitting a
// complement in G, and replace the problem by
//
//     1 -> N/M -> G/M -> B -> 1.
//
// SOUNDNESS OF THE REDUCTION.  If G = M : H and psi : G_Q -> G/M solves the
// reduced problem, then s . psi solves the original, where s : G/M -> G is
// the splitting: pi factors through G/M as pibar, and pi . s = pibar, so
// pi . (s . psi) = pibar . psi = phi.  So reduced-solvable => solvable.
//
// PROPERNESS.  s . psi is NOT surjective onto G (its image is the complement),
// so this direction alone certifies solvable, not properly solvable, and
// Conjecture 6 counts surjective liftings.  The repair is to climb back up
// the tower: each step is a SPLIT embedding problem G_k -> G_{k+1}, and by
// Ikeda's theorem a finite split embedding problem with ABELIAN kernel over a
// Hilbertian field is properly solvable.  So every layer of the tower must
// have abelian kernel.
//
// The abelian hypothesis cannot be dropped.  With B trivial, the split problem
// 1 -> G -> G -> 1 -> 1 is properly solvable exactly when G is a Galois group
// over Q, so an unrestricted "split => properly solvable" would be assuming
// the inverse Galois problem.
//
// Nor may we simply take the LARGEST complemented M at each step: a bigger M
// is worthless if it is non-abelian and a finer all-abelian tower exists.
// 12T130 = C_3 wr C_2^2 is the example.  For N = C_3^4 : C_2 of index 2 in G,
// N is itself complemented (by any involution of V outside N) but non-abelian,
// so the greedy step ends the tower with a non-abelian layer; whereas
// C_3^4 first, then C_2, reduces to the trivial kernel through abelian layers.
// So: abelian candidates only, largest first, and backtrack.

// Abelian normal M <= N, M != 1, admitting a complement in G, largest first.
AbelianComplementedCandidates := function(G, N)
    cands := [];
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M eq 1 or #M eq #G then continue; end if;
        if not (M subset N) then continue; end if;
        if not IsAbelian(M) then continue; end if;
        ok := IsSplitKernel(G, M);
        if ok then Append(~cands, M); end if;
    end for;
    Sort(~cands, func< X, Y | #Y - #X >);
    return cands;
end function;

// Depth-first search for a tower of abelian complemented layers reducing the
// kernel to the trivial group.  Returns:
//   done  true iff the kernel was reduced to 1
//   G, pi the reduced problem (fully reduced if done, else the deepest
//         all-abelian reduction found, which is still a sound handoff)
ReduceTower := function(G, pi, B, depth)
    N := Kernel(pi);
    if #N eq 1 then return true, G, pi; end if;
    if depth le 0 then return false, G, pi; end if;

    cands := AbelianComplementedCandidates(G, N);
    if #cands eq 0 then return false, G, pi; end if;

    bestG := G; bestpi := pi; haveBest := false;
    for M in cands do
        G1, q := quo< G | M >;
        // pi kills M, so it descends to G1.
        pi1 := hom< G1 -> B | [ pi(G1.i @@ q) : i in [1..Ngens(G1)] ] >;
        done, G2, pi2 := $$(G1, pi1, B, depth - 1);
        if done then return true, G2, pi2; end if;
        if not haveBest then
            bestG := G2; bestpi := pi2; haveBest := true;
        end if;
    end for;
    return false, bestG, bestpi;
end function;

// Returns:
//   ebp1       the reduced embedding problem (same B, C, f, phi)
//   fullySplit true iff the kernel reduced to 1 through abelian layers
MaximalSplitReduction := function(ebp)
    fullySplit, G1, pi1 := ReduceTower(ebp`G, ebp`pi, ebp`B, 16);
    ebp1 := rec< EmbeddingProb |
        B := ebp`B, G := G1, C := ebp`C, f := ebp`f, pi := pi1, phi := ebp`phi, d := ebp`d
    >;
    return ebp1, fullySplit;
end function;
