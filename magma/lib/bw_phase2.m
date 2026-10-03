// =====================================================================
// Phase 2: the b_W bracket, shared by both orderings
// =====================================================================
//
// Requires (load first): records.m, split_tower.m, local_verdict.m,
//                        certify.m, certificates/central.m
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
// ORDER OF WORK (new).  Pairs are processed in DECREASING b, and each pair
// gets the local test before the certificate chain:
//
//   * the first pair not proven locally obstructed fixes BWupperLocal --
//     every later pair has smaller or equal b and cannot raise it;
//   * a pair proven obstructed cannot be properly solvable, so under the
//     sound policy it is never sent to CertifyAdmissible (the old order ran
//     the whole split tower and certificate chain on it first);
//   * the first certified pair fixes BWlowerSplit, and the loop stops.
//
// Under LegacyLocalPolicy a No is not a proof, so obstructed pairs are still
// offered to the certificates there, exactly as before; the contradiction
// assert at the end keeps its meaning.
//
// THE TOWER CACHE.  The split tower depends on (G, pi) and not on phi, and it
// used to be rebuilt up to three times per pair (certificates, local
// quotients, diagnostics).  It is now built once per pi.  In Gpiphi's output
// distinct pi have distinct kernels, so the kernel is the cache key.
//
// SupplementDepth is passed through to CertifyAdmissible (see certify.m);
// 0, the default, reproduces the published behaviour exactly.
//
// DIAGNOSTIC FIELDS.  undetermined_local is now 0 or 1: whether the pair
// that fixed BWupperLocal was admitted on an UNDETERMINED verdict (if 0, the
// sound/legacy policy difference cannot have moved the upper bound).
// central_residual_stalled counts the pairs examined above the final lower
// bound whose residual is central and which did not certify.  Both used to
// depend on Gpiphi's enumeration order; now they do not.

BWBoundsFromPairs := function(d, evaluated_pairs, bM, bT, policy : SupplementDepth := 0)
    BWlowerSplit := bM;
    BWupperLocal := bM;
    splitCandidates := [];
    localCandidates := [];
    undetermined := 0;
    centralStalled := 0;

    if bM ge bT then
        return bM, bM, splitCandidates, localCandidates, undetermined, centralStalled;
    end if;

    sound := policy`name eq "sound";
    pairs := Sort(evaluated_pairs, func< x, y | y[3] - x[3] >);
    upperDone := false;
    towerCache := [* *];   // entries < Kernel(pi), SplitTowerRaw >

    for item in pairs do
        j        := item[1];
        ebp      := item[2];
        bval_int := item[3];

        if bval_int le BWlowerSplit then break; end if;

        // Tower for this pi, built once.
        K := Kernel(ebp`pi);
        raw := false;
        for t in towerCache do
            if t[1] eq K then raw := t[2]; break; end if;
        end for;
        if Type(raw) eq BoolElt then
            raw := SplitTowerRaw(ebp);
            Append(~towerCache, < K, raw >);
        end if;

        // Local test only while the upper bound is still open.  Once it is
        // fixed, every remaining pair has b <= BWupperLocal and only the
        // lower bound is in play, so the (possibly expensive) quotient scan
        // is skipped and the pair goes straight to the certificates.  That
        // keeps the local work no larger than in the old greedy loop.
        if not upperDone then
            allow, v := LocalTestsAllowPair(ebp, policy : Raw := raw);
            if allow then
                BWupperLocal := bval_int;
                upperDone := true;
                if v eq LocalVerdictUnknown then undetermined +:= 1; end if;
                ebp1 := MaximalSplitReduction(ebp : Raw := raw);
                Append(~localCandidates, rec< FullCheckCandidateFormat |
                    pair_index        := j,
                    b_value           := bval_int,
                    B_order           := #ebp`B,
                    Ker_order         := #K,
                    passes_split      := false,
                    passes_local      := true,
                    reduced_G_order   := #ebp1`G,
                    reduced_Ker_order := #Kernel(ebp1`pi),
                    certificate       := "",
                    local_verdict     := v
                >);
            elif sound then
                continue;   // proven obstructed: cannot be properly solvable
            end if;
        end if;

        autoSolved, why, ebp1 := CertifyAdmissible(ebp, d : Policy := policy, Raw := raw,
                                                   SupplementDepth := SupplementDepth);
        if autoSolved then
            BWlowerSplit := bval_int;
            Append(~splitCandidates, rec< FullCheckCandidateFormat |
                pair_index        := j,
                b_value           := bval_int,
                B_order           := #ebp`B,
                Ker_order         := #K,
                passes_split      := true,
                passes_local      := false,
                reduced_G_order   := #ebp1`G,
                reduced_Ker_order := #Kernel(ebp1`pi),
                certificate       := why,
                local_verdict     := LocalVerdictUnknown
            >);
            break;   // sorted: nothing later can raise either bound
        end if;

        // Diagnostic only: could have raised the lower bound, central
        // residual, did not certify.  A complete local decision at every
        // place would close it.
        if IsCentralResidual(ebp1) then
            centralStalled +:= 1;
        end if;
    end for;

    // A certificate says "properly solvable", a No verdict says "not even
    // locally solvable".  Under the sound policy both cannot hold, so this
    // assert is a real contradiction detector.  Under LegacyLocalPolicy a No
    // is not a proof, so it can fire legitimately; that is a finding, not a
    // crash to work around.
    assert BWlowerSplit le BWupperLocal;

    return BWlowerSplit, BWupperLocal, splitCandidates, localCandidates,
           undetermined, centralStalled;
end function;
