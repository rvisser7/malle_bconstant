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
// the tower: each step is a SPLIT embedding problem G_k -> G_{k+1}, and a
// finite split embedding problem with ABELIAN kernel over a Hilbertian field
// is properly solvable.  So if every M split off is abelian, a proper
// solution of the reduced problem lifts to a proper solution of the original.
// That is what allAbelian tracks; do not use the certificate without it.

// Largest nontrivial M <= N, normal in G, with a complement in G.
SplitOffOnce := function(G, N)
    bestM  := sub< G | Id(G) >;
    found  := false;
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M eq 1 then continue; end if;
        if #M le #bestM then continue; end if;
        if not (M subset N) then continue; end if;
        ok := IsSplitKernel(G, M);
        if ok then bestM := M; found := true; end if;
    end for;
    return found, bestM;
end function;

// Reduce as far as possible.  Returns:
//   ebp1       the reduced embedding problem (same B, C, f, phi)
//   allAbelian true iff every M split off along the way was abelian
//   steps      how many reductions were performed
MaximalSplitReduction := function(ebp)
    G  := ebp`G;
    B  := ebp`B;
    pi := ebp`pi;
    allAbelian := true;
    steps      := 0;

    while true do
        N := Kernel(pi);
        if #N eq 1 then break; end if;

        ok, M := SplitOffOnce(G, N);
        if not ok then break; end if;

        if not IsAbelian(M) then allAbelian := false; end if;

        G1, q := quo< G | M >;
        // pi kills M, so it descends to G1.
        pi := hom< G1 -> B | [ pi(G1.i @@ q) : i in [1..Ngens(G1)] ] >;
        G  := G1;
        steps +:= 1;
    end while;

    ebp1 := rec< EmbeddingProb |
        B := B, G := G, C := ebp`C, f := ebp`f, pi := pi, phi := ebp`phi
    >;
    return ebp1, allAbelian, steps;
end function;
