// =====================================================================
// FullCheck -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, prp/orbits.m,
//                        bw_phase2.m
//
// Differences from the disc version, all in Phase 1:
//   * a := 1 (every non-identity element has exponent 1 for rad)
//   * num_Smin := #G - 1, and Smin meet Ker(pi) is just N minus identity,
//     so the skip test is "#N eq 1"
//   * d := Exponent(G), which is what lcm{ord(g) : exp(g) = exp(G)} becomes
//     when every non-identity g is minimal
//   * bpiphi takes one argument and works on conjugacy classes of N
// Phase 2 is shared, in lib/bw_phase2.m.

// Phase 1, exposed so that the verdict reporter enumerates exactly the same
// pairs as FullCheck rather than a second copy of this loop.
// Returns: d, a, #Smin, #pairs, b_M, b_T, evaluated_pairs.
EvaluatePairs := function(G)
    d := Exponent(G);
    T := Gpiphi(G, d);

    bM := 0;
    bT := 0;
    evaluated_pairs := [];

    a := 1;
    num_Smin := #G - 1;

    for j := 1 to #T do
        ebp := T[j];

        N := Kernel(ebp`pi);
        if #N eq 1 then continue; end if;

        numberSminInKer, bval := bpiphi(ebp);
        bval_int := Integers()!bval;

        if bval_int gt bT then bT := bval_int; end if;

        if IsTrivialQuotientEbp(ebp) then
            if bval_int gt bM then bM := bval_int; end if;
        end if;

        Append(~evaluated_pairs, <j, ebp, bval_int>);
    end for;

    return d, a, num_Smin, #T, bM, bT, evaluated_pairs;
end function;

FullCheck := function(G : Policy := DefaultLocalPolicy)
    d, a, num_Smin, nPairs, bM, bT, evaluated_pairs := EvaluatePairs(G);

    BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
        undetermined, centralStalled :=
            BWBoundsFromPairs(d, evaluated_pairs, bM, bT, Policy);

    return rec< FullCheckResultFormat |
        group_order              := #G,
        minimal_index            := a,
        number_of_Smin           := num_Smin,
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
