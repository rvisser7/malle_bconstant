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

// Depth-first search for towers of complemented nilpotent layers.
// Returns:
//   done    true iff some branch reduced the kernel to 1
//   leaves  if done, the single fully reduced problem; otherwise the DEAD
//           ENDS of every branch, up to cap, as a list of <G, pi>
//
// WHY ALL THE LEAVES.  Different branches leave different residuals, and
// which of them a certificate can handle is not predictable from the
// residual's size.  An earlier version returned the first branch's dead end;
// then, to make the handoff match its own doc comment, it returned the one
// with the smallest kernel.  Both are guesses, and both lose certificates
// that the other would have found -- 15T95 in the prp ordering is a case
// where the smallest-kernel leaf is opaque while another leaf certifies.
//
// There is no need to guess.  A proper solution of ANY leaf climbs back up
// its own branch to a proper solution of the original, so the certificate
// chain should simply be offered every leaf and stop at the first that
// works.  Insolvability travels the other way and is likewise inherited from
// any leaf, so the local machinery can use them all too.
TowerLeaves := function(G, pi, B, depth, cap)
    N := Kernel(pi);
    if #N eq 1 then return true, [* <G, pi> *]; end if;
    if depth le 0 then return false, [* <G, pi> *]; end if;

    cands := NilpotentComplementedCandidates(G, N);
    if #cands eq 0 then return false, [* <G, pi> *]; end if;

    leaves := [* *];
    for M in cands do
        G1, q := quo< G | M >;
        // pi kills M, so it descends to G1.
        pi1 := hom< G1 -> B | [ pi(G1.i @@ q) : i in [1..Ngens(G1)] ] >;
        done, L := $$(G1, pi1, B, depth - 1, cap);
        if done then return true, L; end if;
        for x in L do
            if #leaves lt cap then Append(~leaves, x); end if;
        end for;
        if #leaves ge cap then break; end if;
    end for;
    if #leaves eq 0 then return false, [* <G, pi> *]; end if;
    return false, leaves;
end function;

// Every dead end of the tower, as embedding problems sharing the original's
// B, C, f, phi and d.  Second return value says whether the kernel reduced
// to 1, in which case there is exactly one leaf and it is trivial.
SplitReductionLeaves := function(ebp : Cap := 24)
    fullySplit, L := TowerLeaves(ebp`G, ebp`pi, ebp`B, 16, Cap);
    leaves := [* *];
    for x in L do
        Append(~leaves, rec< EmbeddingProb |
            B := ebp`B, G := x[1], C := ebp`C, f := ebp`f,
            pi := x[2], phi := ebp`phi, d := ebp`d >);
    end for;
    return leaves, fullySplit;
end function;

// Single-residual view, kept for callers that want one problem to report on:
// the leaf with the smallest kernel.  Nothing decides anything on the basis
// of this choice any more -- CertifyAdmissible and LocalVerdictWithQuotients
// both work through SplitReductionLeaves.
//
// Returns:
//   ebp1       a reduced embedding problem (same B, C, f, phi)
//   fullySplit true iff the kernel reduced to 1 through nilpotent layers
MaximalSplitReduction := function(ebp)
    leaves, fullySplit := SplitReductionLeaves(ebp);
    best := leaves[1];
    for e in leaves do
        if #Kernel(e`pi) lt #Kernel(best`pi) then best := e; end if;
    end for;
    return best, fullySplit;
end function;
