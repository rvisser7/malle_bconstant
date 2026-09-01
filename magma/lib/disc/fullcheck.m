// =====================================================================
// FullCheck -- DISCRIMINANT ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, disc/orbits.m,
//                        bw_phase2.m
//
// Phase 1 only: which pairs exist, and b(pi,phi) for each.  The bracket is
// Phase 2, shared with the prp ordering in lib/bw_phase2.m.

FullCheck := function(G : Policy := DefaultLocalPolicy)
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    T := Gpiphi(G, d);

    bM := 0;
    bT := 0;
    evaluated_pairs := [];

    for j := 1 to #T do
        ebp := T[j];

        Sminpi := SminIntersectionKerPi(ebp, Smin);
        if #Sminpi eq 0 then continue; end if;      // exp(Ker pi) > exp(G)

        numberSminInKer, bval := bpiphi(ebp, Smin);
        bval_int := Integers()!bval;

        if bval_int gt bT then bT := bval_int; end if;

        if IsTrivialQuotientEbp(ebp) then
            if bval_int gt bM then bM := bval_int; end if;
        end if;

        Append(~evaluated_pairs, <j, ebp, bval_int>);
    end for;

    BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
        undetermined, centralStalled :=
            BWBoundsFromPairs(d, evaluated_pairs, bM, bT, Policy);

    return rec< FullCheckResultFormat |
        group_order              := #G,
        minimal_index            := a,
        number_of_Smin           := #Smin,
        number_of_pairs          := #T,
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
