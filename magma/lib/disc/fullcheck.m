// =====================================================================
// FullCheck -- DISCRIMINANT ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, disc/orbits.m,
//                        bw_phase2.m
//
// Phase 1 only: which pairs exist, and b(pi,phi) for each.  The bracket is
// Phase 2, shared with the prp ordering in lib/bw_phase2.m.

// Phase 1, exposed so that the verdict reporter enumerates exactly the same
// pairs as FullCheck rather than a second copy of this loop.
// Returns: d, a, #Smin, #pairs, b_M, b_T, evaluated_pairs.
EvaluatePairs := function(G)
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    T, groups := Gpiphi(G, d);

    bM := 0;
    bT := 0;
    evaluated_pairs := [];

    // One pass per pi, not per pair.  Kernel(pi) and Smin meet N depend only
    // on pi, so they are built once here and shared by every phi over it --
    // and the "exp(Ker pi) > exp(G)" skip is decided once for the whole
    // group of pairs rather than re-derived for each.
    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]], Smin);
        if IsEmpty(ctx`Sminpi) then continue; end if;   // exp(Ker pi) > exp(G)

        for j in grp do
            ebp := T[j];

            numberSminInKer, bval := bpiphiCtx(ebp, ctx);
            bval_int := Integers()!bval;

            if bval_int gt bT then bT := bval_int; end if;

            if IsTrivialQuotientEbp(ebp) then
                if bval_int gt bM then bM := bval_int; end if;
            end if;

            Append(~evaluated_pairs, <j, ebp, bval_int>);
        end for;
    end for;

    return d, a, #Smin, #T, bM, bT, evaluated_pairs;
end function;

FullCheck := function(G : Policy := DefaultLocalPolicy)
    d, a, nSmin, nPairs, bM, bT, evaluated_pairs := EvaluatePairs(G);

    BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
        undetermined, centralStalled :=
            BWBoundsFromPairs(d, evaluated_pairs, bM, bT, Policy);

    return rec< FullCheckResultFormat |
        group_order              := #G,
        minimal_index            := a,
        number_of_Smin           := nSmin,
        number_of_pairs          := nPairs,
        b_M                      := bM,
        b_T                      := bT,
        BW_lower_split           := BWlowerSplit,
        BW_upper_local           := BWupperLocal,
        split_candidates         := splitCandidates,
        local_candidates         := localCandidates,
        undetermined_local       := undetermined,
        central_residual_stalled := centralStalled
    >;
end function;
