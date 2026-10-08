// =====================================================================
// Record formats
// =====================================================================
//
// Requires (load first): nothing

EmbeddingProb := recformat<
    B, G, C, f, pi, phi, d
>;

FullCheckCandidateFormat := recformat<
    pair_index, b_value, B_order, Ker_order,
    passes_split, passes_local, reduced_G_order, reduced_Ker_order,
    certificate, certificate_kind, proof_scope, local_verdict
>;

// Diagnostic fields added alongside the four published quantities:
//
//   undetermined_local        1 if the pair that fixed the upper bound was
//                             admitted on an UNDETERMINED local verdict
//                             rather than an exhibited lift, else 0.  If 0,
//                             the policy correction cannot have moved the
//                             upper bound for this group.
//   BW_lower_lift             largest lower bound backed by an actual
//                             proper-lift certificate (including a verified
//                             witness supplied as KnownLower), excluding the
//                             standing b_W >= b_M assumption.
//   BW_lower_exact            largest lower bound known with Wang's exact
//                             cyclotomic-intersection condition.  In the
//                             production driver this is the verified witness
//                             input; split/certificate proofs only establish
//                             proper liftability.
//   known_lower_input         verified witness lower bound supplied to Phase 2
//                             (0 if none).
//   lower_uses_bM_assumption  true iff BW_lower_split is strictly larger than
//                             BW_lower_lift and therefore still relies on the
//                             standing b_W >= b_M assumption.
//   central_residual_stalled  pairs whose residual is central -- so
//                             certificates/central.m is in principle a
//                             decision procedure -- but whose local verdict
//                             was not an all-Yes.  This is the queue of
//                             brackets that better local tests would close.
FullCheckResultFormat := recformat<
    group_order, minimal_index, number_of_Smin, number_of_pairs,
    b_M, b_T, BW_lower_split, BW_upper_local,
    BW_lower_lift, BW_lower_exact, known_lower_input,
    lower_uses_bM_assumption,
    split_candidates, local_candidates,
    undetermined_local, central_residual_stalled
>;

// ---------------------------------------------------------------------
// TryQuo(G, K): quo< G | K > for a normal subgroup K, without crashing.
// Returns ok, Q, q with q : G -> Q a homomorphism (supporting @ and @@)
// whose kernel is exactly K; ok = false if no quotient could be formed.
//
// For a large permutation group Magma's quo< G | K > can fail with
// "Index of subgroup is too large", when it cannot find a permutation
// representation of G/K (36T120951, 36T120953 = 2^18:((3^8:A9):S3), order
// ~1.9 * 10^15).  Fallback: the action of G on one of its block systems;
// when that kernel lies inside K, G/K is a quotient of the (much smaller)
// block image H, so take H / image(K) instead, recursively.
//
// Callers treat ok = false as "this quotient is unavailable" and skip it.
// That is sound in every place it is used: the split tower loses a branch
// (fewer certificates, search marked incomplete), the local-quotient scan
// loses one candidate obstruction, the witness search one route.  It can
// only leave a bracket wider, never make it wrong.
// ---------------------------------------------------------------------
TryQuo := function(G, K)
    ok := true;
    try
        Q, q := quo< G | K >;
    catch err
        ok := false;
    end try;
    if ok then return true, Q, q; end if;

    if Type(G) ne GrpPerm or not IsTransitive(G) then
        return false, G, IdentityHomomorphism(G);
    end if;
    best := false;
    bestOrd := 1;
    for P in AllPartitions(G) do                // one block per block system
        f, H, Kf := BlocksAction(G, P);
        if #Kf gt bestOrd and Kf subset K then
            best := < f, H >; bestOrd := #Kf;
        end if;
    end for;
    if Type(best) eq BoolElt then
        return false, G, IdentityHomomorphism(G);
    end if;
    f := best[1]; H := best[2];
    ok2, Q, q2 := $$(H, f(K));
    if not ok2 then return false, G, IdentityHomomorphism(G); end if;
    q := hom< G -> Q | [ q2(f(G.i)) : i in [1..Ngens(G)] ] >;
    return true, Q, q;
end function;
