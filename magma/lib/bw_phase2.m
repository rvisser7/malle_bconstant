// =====================================================================
// Phase 2: the b_W bracket, shared by both orderings
// =====================================================================
//
// Requires (load first): records.m, split_tower.m, local_verdict.m,
//                        certify.m
//
// Phase 1 (which pairs exist, and what b(pi,phi) is) genuinely differs
// between disc and prp and stays in the two fullcheck.m files.  Phase 2 was
// byte-for-byte identical in both, so it lives here once; two copies of this
// logic drifting apart is exactly the failure this refactor is meant to
// prevent.
//
// THE TWO BOUNDS.
//   BWlowerSplit  = max b(pi,phi) over pairs PROVEN properly solvable.
//                   Starts at b_M: see the assumption note below.
//   BWupperLocal  = max b(pi,phi) over pairs not PROVEN locally obstructed.
// Wang's b_W lies in [BWlowerSplit, BWupperLocal], and is known exactly when
// they meet.
//
// STANDING ASSUMPTION, b_W >= b_M.  Both bounds start at b_M rather than at
// the certified value for the trivial pair, and the threshold tests below
// mean the trivial pair is never sent to CertifyAdmissible.  For the trivial
// pair (B = 1) proper solvability is literally the inverse Galois problem
// for G over Q, which we do not attempt.  So every number here is
// conditional on G being realisable over Q -- which Malle's conjecture
// assumes anyway, since otherwise N_k(G, X) = 0 and there is no b to
// predict.
//
// GREEDY SKIPPING.  A pair is examined only when its b-value exceeds the
// current bound, which cannot lose the maximum: a pair with a smaller value
// could not raise it.  The loop stops as soon as both bounds reach b_T.

BWBoundsFromPairs := function(d, evaluated_pairs, bM, bT, policy)
    BWlowerSplit := bM;
    BWupperLocal := bM;
    splitCandidates := [];
    localCandidates := [];
    undetermined := 0;
    centralStalled := 0;

    if bM ge bT then
        return bM, bM, splitCandidates, localCandidates, undetermined, centralStalled;
    end if;

    for item in evaluated_pairs do
        j        := item[1];
        ebp      := item[2];
        bval_int := item[3];

        autoSolved := false;
        haveEbp1   := false;
        ebp1       := ebp;
        why        := "";

        if bval_int gt BWlowerSplit then
            autoSolved, why, ebp1 := CertifyAdmissible(ebp, d : Policy := policy);
            haveEbp1 := true;

            if autoSolved then
                BWlowerSplit := bval_int;
                Append(~splitCandidates, rec< FullCheckCandidateFormat |
                    pair_index        := j,
                    b_value           := bval_int,
                    B_order           := #ebp`B,
                    Ker_order         := #Kernel(ebp`pi),
                    passes_split      := true,
                    passes_local      := false,
                    reduced_G_order   := #ebp1`G,
                    reduced_Ker_order := #Kernel(ebp1`pi),
                    certificate       := why,
                    local_verdict     := LocalVerdictUnknown
                >);
            end if;
        end if;

        if bval_int gt BWupperLocal then
            allow, v := LocalTestsAllowPair(ebp, policy);
            if allow then
                BWupperLocal := bval_int;
                if v eq LocalVerdictUnknown then
                    undetermined +:= 1;
                end if;
                if not haveEbp1 then
                    ebp1 := MaximalSplitReduction(ebp);
                    haveEbp1 := true;
                end if;
                Append(~localCandidates, rec< FullCheckCandidateFormat |
                    pair_index        := j,
                    b_value           := bval_int,
                    B_order           := #ebp`B,
                    Ker_order         := #Kernel(ebp`pi),
                    passes_split      := autoSolved,
                    passes_local      := true,
                    reduced_G_order   := #ebp1`G,
                    reduced_Ker_order := #Kernel(ebp1`pi),
                    certificate       := why,
                    local_verdict     := v
                >);
            end if;
        end if;

        // Diagnostic only: a pair that could have raised the lower bound,
        // whose residual is central, and which did not certify.  With a
        // complete local decision at every place this one would close.
        if (not autoSolved) and (bval_int gt BWlowerSplit) then
            if not haveEbp1 then
                ebp1 := MaximalSplitReduction(ebp);
                haveEbp1 := true;
            end if;
            if IsCentralResidual(ebp1) then
                centralStalled +:= 1;
            end if;
        end if;

        if BWlowerSplit eq bT and BWupperLocal eq bT then
            break;
        end if;
    end for;

    // A certificate says "properly solvable", a No verdict says "not even
    // locally solvable".  Both cannot hold, so this assert is a real
    // contradiction detector -- for the sound policy.  Under
    // LegacyLocalPolicy a No is not a proof, so it can fire legitimately;
    // that is a finding, not a crash to work around.
    assert BWlowerSplit le BWupperLocal;

    return BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
           undetermined, centralStalled;
end function;
