// =====================================================================
// FullCheck -- DISCRIMINANT ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, class_orbits.m,
//                        disc/orbits.m, bw_phase2.m
//
// Phase 1 only: which pairs exist, and b(pi,phi) for each.  The bracket is
// Phase 2, shared with the prp ordering in lib/bw_phase2.m.

// Phase 1, exposed so that the verdict reporter enumerates exactly the same
// pairs as FullCheck rather than a second copy of this loop.
// Returns: d, a, #Smin, #pairs, b_M, b_T, evaluated_pairs.
//
// #pairs now counts only pairs with Ker(pi) meeting Smin: Gpiphi drops the
// others up front (MinReps), since Theorem 2.16 excludes them anyway.
EvaluatePairs := function(G)
    a, minreps, nSmin, d := MinIndexClasses(G);
    T, groups := Gpiphi(G, d : MinReps := minreps);

    bM := 0;
    bT := 0;
    evaluated_pairs := [];

    // One pass per pi: the class context depends on pi alone.
    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]], a);
        if ctx`nkept eq 0 then continue; end if;   // exp(Ker pi) > exp(G)

        for j in grp do
            ebp := T[j];
            _, bval := bpiphiCtx(ebp, ctx);
            bval_int := Integers()!bval;

            if bval_int gt bT then bT := bval_int; end if;
            if IsTrivialQuotientEbp(ebp) and bval_int gt bM then
                bM := bval_int;
            end if;

            Append(~evaluated_pairs, <j, ebp, bval_int>);
        end for;
    end for;

    return d, a, nSmin, #T, bM, bT, evaluated_pairs;
end function;

FullCheck := function(
    G : Policy := DefaultLocalPolicy, SupplementDepth := 0, MaxQuotients := 60,
        KnownLower := 0, KnownBM := -1, KnownBT := -1
)
    d, a, nSmin, nPairs, bM, bT, evaluated_pairs := EvaluatePairs(G);

    // A verified witness may be fed into Phase 2 before the expensive local
    // and certificate search.  When its stored Phase-1 values are supplied,
    // check them here so a stale/incompatible certificate can never alter the
    // search.
    if KnownLower gt 0 then
        if KnownBM ge 0 and KnownBM ne bM then
            error Sprintf("known witness has b_M=%o but Phase 1 computed %o", KnownBM, bM);
        end if;
        if KnownBT ge 0 and KnownBT ne bT then
            error Sprintf("known witness has b_T=%o but Phase 1 computed %o", KnownBT, bT);
        end if;
        if KnownLower gt bT then
            error Sprintf("known witness lower bound %o exceeds b_T=%o", KnownLower, bT);
        end if;
    end if;


    BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
        undetermined, centralStalled :=
            BWBoundsFromPairs(d, evaluated_pairs, bM, bT, Policy :
                              SupplementDepth := SupplementDepth,
                              MaxQuotients := MaxQuotients,
                              KnownLower := KnownLower);

    certLower := KnownLower;
    for c in splitCandidates do
        if c`b_value gt certLower then certLower := c`b_value; end if;
    end for;
    exactLower := KnownLower;   // verified field witnesses certify exact intersection

    return rec< FullCheckResultFormat |
        group_order              := #G,
        minimal_index            := a,
        number_of_Smin           := nSmin,
        number_of_pairs          := nPairs,
        b_M                      := bM,
        b_T                      := bT,
        BW_lower_split           := BWlowerSplit,
        BW_upper_local           := BWupperLocal,
        BW_lower_lift            := certLower,
        BW_lower_exact           := exactLower,
        known_lower_input        := KnownLower,
        lower_uses_bM_assumption := BWlowerSplit gt certLower,
        split_candidates         := splitCandidates,
        local_candidates         := localCandidates,
        undetermined_local       := undetermined,
        central_residual_stalled := centralStalled
    >;
end function;
