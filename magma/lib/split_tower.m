// =====================================================================
// Iterated split reduction
// =====================================================================
//
// Requires (load first): records.m, splitting.m
//
// Also defines the GAR table (IsGARSimpleOrder, HasGAROverQ, IsGARLayer),
// which certificates/structural.m uses: this file is loaded before it.
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
//
//   (3) GAR LAYERS (new).  [MM99, Thm IV.3.6]: over a Hilbertian field,
//       every finite embedding problem whose kernel has all composition
//       factors non-abelian with a GAR-realisation has a proper solution.
//       (Thm IV.3.5 is the characteristically simple case H^r; its proof
//       reduces to a minimal normal kernel on whose simple factors G acts
//       TRANSITIVELY, so factors permuted by G are covered.)  That is a
//       statement about EVERY embedding problem with that kernel -- split or
//       not, for every top field K -- so such a layer is peeled off WITHOUT
//       asking for a complement.  Which simple groups qualify is the table
//       in IsGARSimpleOrder below.
//
// The climb is unchanged: a proper solution of G/M lifts properly through
// each layer, whichever of (1)-(3) admitted it, and the leaves are still
// quotient problems, so local obstructions are still inherited from them.

// May the complemented normal subgroup M of G be peeled off?  (1) or (2)
// above.  Cheap tests first; the quotient is only formed for odd,
// non-nilpotent M.
LayerAllowed := function(G, M)
    if IsNilpotent(M) then return true; end if;                // (9.6.10)
    if IsEven(#M) then return false; end if;
    e := Exponent(AbelianQuotient(quo< G | M >));              // (9.5.8)
    return forall{ p : p in PrimeDivisors(#M) | e mod (p - 1) ne 0 };
end function;

// ---------------------------------------------------------------------
// GAR table: [MM99] = Malle-Matzat, Inverse Galois Theory, Ch. IV.
// ---------------------------------------------------------------------
//
// Simple groups with a GAR-realisation over Q:
//   Thm IV.4.3 (one variable)
//     (a) A_n, n >= 5, n != 6
//     (b) L_2(p), p prime, with (a/p) = -1 for some a in {2,3,5,7}
//     (c) L_{2n+1}(p), gcd(2n+1, p-1) = 1, p > 3, p != -1 mod 12
//     (d) U_{2n+1}(p), gcd(2n+1, p+1) = 1, p > 2, p != 1 mod 12
//     (e) S_{2n}(p), p odd, p != +-1 mod 24, p not dividing n; or p = 2
//     (f) O_{2n+1}(p), n >= 1, p odd, p != +-1 mod 24
//     (h) O^-_{2n}(2), n >= 3
//     (i) G_2(p)
//     (n) the sporadic groups, except possibly M23
//   Ex. IV.4.1, IV.4.2 (two variables): L_3(3), L_3(4)
//   ((g), (j)-(m) are omitted: none of them is anywhere near our degrees.)
//
// NOT on the list, and so NOT accepted: A_6 (excluded in (a)), L_2(8),
// L_2(16), L_2(25), L_2(27), M23, and anything else not named.  Thm IV.4.6
// is over Q^ab and is no use here.  A_6 used to be accepted; it was wrong.
//
// IDENTIFICATION BY ORDER.  Composition factors are identified by their
// order alone.  By the classification, two non-isomorphic finite simple
// groups have the same order only for {A_8, L_3(4)} (order 20160 -- both
// GAR, so harmless) and {B_n(q), C_n(q)} with n >= 3, q odd.  The table
// therefore must not contain an order of the latter kind: in particular
// 4585351680 = |O_7(3)| = |S_6(3)| is left out, because O_7(3) is GAR by
// (f) while S_6(3) is not by (e) (3 divides n = 3).
//
// Every entry of GARExtraOrders was computed in GAP (Size of PSL, PSU,
// PSp, SimpleGroup(...), and CharacterTable(...) for the sporadics).

GARExtraOrders := [
    < 5616,        "L3(3) [MM99 IV Ex. 4.1]" >,
    < 20160,       "L3(4) = A8 order [MM99 IV Ex. 4.2, Thm 4.3(a)]" >,
    < 372000,      "L3(5) [MM99 IV Thm 4.3(c)]" >,
    < 6950204928,  "L3(17) [MM99 IV Thm 4.3(c)]" >,
    < 6048,        "U3(3) [MM99 IV Thm 4.3(d)]" >,
    < 5663616,     "U3(7) [MM99 IV Thm 4.3(d)]" >,
    < 16938986400, "U3(19) [MM99 IV Thm 4.3(d)]" >,
    < 25920,       "S4(3) = U4(2) = O6-(2) [MM99 IV Thm 4.3(e)]" >,
    < 4680000,     "S4(5) [MM99 IV Thm 4.3(e)]" >,
    < 138297600,   "S4(7) [MM99 IV Thm 4.3(e)]" >,
    < 1451520,     "S6(2) [MM99 IV Thm 4.3(e)]" >,
    < 47377612800, "S8(2) [MM99 IV Thm 4.3(e)]" >,
    < 197406720,   "O8-(2) [MM99 IV Thm 4.3(h)]" >,
    < 4245696,     "G2(3) [MM99 IV Thm 4.3(i)]" >,
    < 5859000000,  "G2(5) [MM99 IV Thm 4.3(i)]" >,
    // sporadics, Thm 4.3(n); M23 (10200960) deliberately absent
    < 7920, "M11 [MM99 IV Thm 4.3(n)]" >,
    < 95040, "M12 [MM99 IV Thm 4.3(n)]" >,
    < 175560, "J1 [MM99 IV Thm 4.3(n)]" >,
    < 443520, "M22 [MM99 IV Thm 4.3(n)]" >,
    < 604800, "J2 [MM99 IV Thm 4.3(n)]" >,
    < 44352000, "HS [MM99 IV Thm 4.3(n)]" >,
    < 50232960, "J3 [MM99 IV Thm 4.3(n)]" >,
    < 244823040, "M24 [MM99 IV Thm 4.3(n)]" >,
    < 898128000, "McL [MM99 IV Thm 4.3(n)]" >,
    < 4030387200, "He [MM99 IV Thm 4.3(n)]" >,
    < 145926144000, "Ru [MM99 IV Thm 4.3(n)]" >,
    < 448345497600, "Suz [MM99 IV Thm 4.3(n)]" >,
    < 460815505920, "ON [MM99 IV Thm 4.3(n)]" >,
    < 495766656000, "Co3 [MM99 IV Thm 4.3(n)]" >,
    < 42305421312000, "Co2 [MM99 IV Thm 4.3(n)]" >,
    < 64561751654400, "Fi22 [MM99 IV Thm 4.3(n)]" >,
    < 273030912000000, "HN [MM99 IV Thm 4.3(n)]" >,
    < 51765179004000000, "Ly [MM99 IV Thm 4.3(n)]" >,
    < 90745943887872000, "Th [MM99 IV Thm 4.3(n)]" >,
    < 4089470473293004800, "Fi23 [MM99 IV Thm 4.3(n)]" >,
    < 4157776806543360000, "Co1 [MM99 IV Thm 4.3(n)]" >,
    < 86775571046077562880, "J4 [MM99 IV Thm 4.3(n)]" >,
    < 1255205709190661721292800, "Fi24' [MM99 IV Thm 4.3(n)]" >,
    < 4154781481226426191177580544000000, "B [MM99 IV Thm 4.3(n)]" >,
    < 808017424794512875886459904961710757005754368000000000, "M [MM99 IV Thm 4.3(n)]" >
];

// Is o the order of a non-abelian simple group with GAR over Q?  Only
// meaningful when o IS the order of a simple group (see above).
IsGARSimpleOrder := function(o)
    // (a) alternating, n != 6
    n := 5; a := 60;
    while a le o do
        if a eq o and n ne 6 then
            return true, Sprintf("A%o [MM99 IV Thm 4.3(a)]", n);
        end if;
        n +:= 1; a := Factorial(n) div 2;
    end while;
    // (b) L2(p): o = p(p^2-1)/2
    r := Iroot(2*o, 3);
    for p in [Max(5, r - 2) .. r + 2] do
        if IsPrime(p) and p*(p^2 - 1) div 2 eq o then
            if exists{ q : q in [2, 3, 5, 7] | q ne p and LegendreSymbol(q, p) eq -1 } then
                return true, Sprintf("L2(%o) [MM99 IV Thm 4.3(b)]", p);
            end if;
        end if;
    end for;
    for t in GARExtraOrders do
        if t[1] eq o then
            return true, t[2];
        end if;
    end for;
    return false, "";
end function;

// Simple non-abelian K with GAR over Q.  Kept under its old name; it used
// to live in certificates/structural.m with a hard-coded A5..A9, PSL(2,7)
// list that wrongly included A6.
HasGAROverQ := function(K)
    if IsAbelian(K) or not IsSimple(K) then return false, ""; end if;
    ok, why := IsGARSimpleOrder(#K);
    return ok, why;
end function;

// Every composition factor of M non-abelian and GAR over Q, i.e. M is a
// legitimate kernel for [MM99, Thm IV.3.6].
IsGARLayer := function(M)
    if #M eq 1 or IsSolvable(M) then return false, ""; end if;
    // Orders along a composition series; Sort+Set so as not to depend on
    // which end CompositionSeries starts from.
    ords := Sort(SetToSequence({ #X : X in CompositionSeries(M) } join { 1, #M }));
    whys := [];
    for i in [1 .. #ords - 1] do
        o := ords[i+1] div ords[i];
        if IsPrime(o) then return false, ""; end if;     // abelian factor
        ok, why := IsGARSimpleOrder(o);
        if not ok then return false, ""; end if;
        Append(~whys, why);
    end for;
    return true, "GAR layer: " cat &cat[ w cat "; " : w in whys ];
end function;

// Normal M <= N, M != 1, that the tower may peel off, largest first:
//   * a GAR layer (3), complemented or not; or
//   * a complemented layer allowed by LayerAllowed, (1) or (2).
AdmissibleCandidates := function(G, N)
    cands := [];
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M eq 1 or #M eq #G then continue; end if;
        if not (M subset N) then continue; end if;
        if IsGARLayer(M) then Append(~cands, M); continue; end if;
        if not LayerAllowed(G, M) then continue; end if;
        ok := IsSplitKernel(G, M);
        if ok then Append(~cands, M); end if;
    end for;
    Sort(~cands, func< X, Y | #Y - #X >);
    return cands;
end function;

// The pre-GAR candidate list (complemented, LayerAllowed), unchanged.  Kept
// for the diagnostics (inspect_stalled.m, why_no_candidates.m) and for
// tests/test_layer_allowed.m.  The tower itself uses AdmissibleCandidates.
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

// Depth-first search for towers of admissible layers (complemented
// nilpotent / odd layers, and GAR layers).
//
// STATE.  A node of the search is a normal subgroup K of the ORIGINAL group
// G0 (the cumulative kernel quotiented out so far), and the problem at that
// node is 1 -> Ker(pi0)/K -> G0/K -> B -> 1.  Different orders of peeling
// off layers (M1 then M2, or M2 then M1) reach the same K, and the search
// used to explore each of them again, which is exponential in the number of
// layers.  `seen` records, for each K, the LARGEST remaining search depth with
// which K has already been expanded.  Thus a state first reached near the
// depth limit is re-expanded if it is later reached by a shorter path with
// more depth to spare.  This avoids silently losing certificates through the
// memoisation itself.
//
// Returns:
//   done    true iff some branch reduced the kernel to 1
//   leaves  if done, the single fully reduced problem; otherwise the DEAD
//           ENDS of every branch, up to cap, as a list of <G, pi>
//   seen    the updated memo, as <K, largest remaining depth expanded>
//   complete true iff no branch was cut off by the depth or leaf cap.  If a
//            fully split branch is found then complete is true, since the
//            existential certificate has already been established.
//
// WHY ALL THE LEAVES.  Different branches leave different residuals, and
// which of them a certificate can handle does not follow from the
// residual's size.  A proper solution of ANY leaf climbs back up its own
// branch to a proper solution of the original, so the certificate chain is
// simply offered every leaf and stops at the first that works.
// Insolvability travels the other way and is likewise inherited from any
// leaf, so the local machinery uses them all too.

TowerSeenDepth := function(L, K)
    for x in L do
        if x[1] eq K then return x[2]; end if;
    end for;
    return -1;
end function;

TowerRecordDepth := function(L, K, depth)
    for i := 1 to #L do
        if L[i][1] eq K then
            if depth gt L[i][2] then L[i] := < K, depth >; end if;
            return L;
        end if;
    end for;
    Append(~L, < K, depth >);
    return L;
end function;

TowerLeavesFrom := function(G0, pi0, B, K, depth, cap, seen)
    if #K eq 1 then
        GK := G0; piK := pi0; qK := IdentityHomomorphism(G0);
    else
        GK, qK := quo< G0 | K >;
        piK := hom< GK -> B | [ pi0(GK.i @@ qK) : i in [1..Ngens(GK)] ] >;
    end if;

    N := Kernel(piK);
    if #N eq 1 then return true, [* <GK, piK> *], seen, true; end if;
    if depth le 0 then return false, [* <GK, piK> *], seen, false; end if;

    cands := AdmissibleCandidates(GK, N);
    if #cands eq 0 then return false, [* <GK, piK> *], seen, true; end if;

    leaves := [* *];
    complete := true;
    for idx := 1 to #cands do
        M := cands[idx];
        K1 := M @@ qK;                       // cumulative kernel, inside G0
        nextDepth := depth - 1;
        if TowerSeenDepth(seen, K1) ge nextDepth then continue; end if;
        seen := TowerRecordDepth(seen, K1, nextDepth);
        done, L, seen, childComplete := $$(
            G0, pi0, B, K1, nextDepth, cap, seen
        );
        if done then return true, L, seen, true; end if;
        if not childComplete then complete := false; end if;
        for x in L do
            if #leaves lt cap then
                Append(~leaves, x);
            else
                complete := false;
                break;
            end if;
        end for;
        if #leaves ge cap and idx lt #cands then
            complete := false;
            break;
        end if;
    end for;
    // May be empty if every child had already been expanded elsewhere: its
    // dead ends were collected on that earlier visit.
    return false, leaves, seen, complete;
end function;

// The raw tower for a pair:
//
//     <fullySplit, list of <G, pi>, searchComplete>.
//
// searchComplete means the result is conclusive for the tower question: either
// a fully split branch was found, or (when fullySplit is false) every branch
// was exhausted without hitting Depth/Cap.  It is false when a negative search
// was truncated.  The first two components retain their old positions, so all
// existing callers remain compatible.  The tower depends on
// (G, pi) only, NOT on phi, so callers that handle several phi over one pi
// should compute it once and pass it back in via the Raw parameter below.
SplitTowerRaw := function(ebp : Cap := 24, Depth := 16)
    G := ebp`G;
    triv := sub< G | Id(G) >;
    done, L, seen, complete := TowerLeavesFrom(
        G, ebp`pi, ebp`B, triv, Depth, Cap, [* <triv, Depth> *]
    );
    if #L eq 0 then L := [* <G, ebp`pi> *]; end if;
    return < done, L, complete >;
end function;

SplitTowerSearchComplete := function(R)
    if #R lt 3 then return false; end if;
    return R[3];
end function;

// Every dead end of the tower, as embedding problems sharing the original's
// B, C, f, phi and d.  Second return value says whether the kernel reduced
// to 1, in which case there is exactly one leaf and it is trivial.
//
// Raw: optional precomputed SplitTowerRaw(ebp) for the same pi (any phi).
SplitReductionLeaves := function(ebp : Cap := 24, Depth := 16, Raw := false)
    R := Raw;
    if Type(R) eq BoolElt then
        R := SplitTowerRaw(ebp : Cap := Cap, Depth := Depth);
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
