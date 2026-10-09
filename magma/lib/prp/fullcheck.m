// =====================================================================
// FullCheck -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, class_orbits.m,
//                        prp/orbits.m,
//                        bw_phase2.m
//
// Differences from the disc version, all in Phase 1:
//   * a := 1 (every non-identity element has exponent 1 for rad)
//   * num_Smin := #G - 1, and Smin meet Ker(pi) is just N minus identity,
//     so the skip test is "#N eq 1"
//   * d := Exponent(G), which is what lcm{ord(g) : exp(g) = exp(G)} becomes
//     when every non-identity g is minimal
//   * the class context keeps every non-identity class of N
//     (lib/class_orbits.m, shared with disc)
// Phase 2 is shared, in lib/bw_phase2.m.

// Phase 1, exposed so that the verdict reporter enumerates exactly the same
// pairs as FullCheck rather than a second copy of this loop.
// Returns: d, a, #Smin, #pairs, b_M, b_T, evaluated_pairs.
//
// Method := "formula" (default) counts from the classes of G alone
// (class_orbits.m, CLASS FORMULA); Method := "kernel" is the previous
// per-kernel orbit count, kept as the reference.  Both return the same pairs
// with the same b-values; tests/test_class_formula_agree_prp.m checks this.
EvaluatePairs := function(G : Method := "formula")
    d := Exponent(G);
    T, groups := Gpiphi(G, d);

    bM := 0;
    bT := 0;
    evaluated_pairs := [];

    a := 1;
    num_Smin := #G - 1;

    if Method eq "formula" then
        // Group data once; per pi only images under pi.
        data := MakeClassFormulaData(G, T[1]`C, T[1]`f, func< g | Order(g) gt 1 >);
        for grp in groups do
            entries := MakeClassFormulaPiCtx(T[grp[1]], data);
            if #entries eq 0 then continue; end if;      // Ker(pi) = 1
            for j in grp do
                ebp := T[j];
                bval_int := ClassFormulaCount(ebp, entries);
                if bval_int gt bT then bT := bval_int; end if;
                if IsTrivialQuotientEbp(ebp) and bval_int gt bM then
                    bM := bval_int;
                end if;
                Append(~evaluated_pairs, <j, ebp, bval_int>);
            end for;
        end for;
        return d, a, num_Smin, #T, bM, bT, evaluated_pairs;
    end if;
    assert Method eq "kernel";

    // One pass per pi, not per pair.  Classes(N) and ClassMap(N) are the
    // expensive part here and depend only on pi, so they are computed once
    // per group of pairs instead of once per phi.
    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]]);
        if ctx`nkept eq 0 then continue; end if;

        for j in grp do
            ebp := T[j];

            _, bval := bpiphiCtx(ebp, ctx);
            bval_int := Integers()!bval;

            if bval_int gt bT then bT := bval_int; end if;

            if IsTrivialQuotientEbp(ebp) then
                if bval_int gt bM then bM := bval_int; end if;
            end if;

            Append(~evaluated_pairs, <j, ebp, bval_int>);
        end for;
    end for;

    return d, a, num_Smin, #T, bM, bT, evaluated_pairs;
end function;

FullCheck := function(
    G : Policy := DefaultLocalPolicy, SupplementDepth := 0, MaxQuotients := 60,
        KnownLower := 0, KnownBM := -1, KnownBT := -1, Phase1 := false
)
    // Phase1, if given, is the tuple of values EvaluatePairs(G) returned, so
    // a caller that has already written b_M/b_T need not recompute them.
    if Type(Phase1) eq BoolElt then
        d, a, num_Smin, nPairs, bM, bT, evaluated_pairs := EvaluatePairs(G);
    else
        d, a, num_Smin, nPairs, bM, bT, evaluated_pairs := Explode(Phase1);
    end if;

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
        number_of_Smin           := num_Smin,
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
