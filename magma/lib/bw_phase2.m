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
//   BWlowerSplit  = max of the standing b_M floor, any verified KnownLower,
//                   and b(pi,phi) over pairs PROVEN properly solvable.
//   BWupperLocal  = max b(pi,phi) over pairs not PROVEN locally obstructed,
//                   with the same verified KnownLower as a fallback floor.
// Wang's b_W lies in [BWlowerSplit, BWupperLocal], and is known exactly when
// they meet.
//
// STANDING ASSUMPTION, b_W >= b_M.  In the absence of a verified field
// witness both bounds start at b_M rather than at the certified value for the
// trivial pair, and the threshold tests below
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
// MaxQuotients is passed to the quotient-obstruction search; 0 means
// exhaustive, while 60 is the production default.
// KnownLower is an externally VERIFIED witness lower bound.  Supplying it
// moves both the initial lower floor and the fallback upper floor, so Phase 2
// never spends time on b-strata that cannot change the answer.
//
// DIAGNOSTIC FIELDS.  undetermined_local is now 0 or 1: whether the pair
// that fixed BWupperLocal was admitted on an UNDETERMINED verdict (if 0, the
// sound/legacy policy difference cannot have moved the upper bound).
// central_residual_stalled counts the pairs examined above the final lower
// bound whose residual is central and which did not certify.  Both used to
// depend on Gpiphi's enumeration order; now they do not.

BWBoundsFromPairs := function(
    d, evaluated_pairs, bM, bT, policy : SupplementDepth := 0, MaxQuotients := 60,
                                             KnownLower := 0
)
    if KnownLower lt 0 or KnownLower gt bT then
        error Sprintf("KnownLower = %o is outside [0,b_T=%o]", KnownLower, bT);
    end if;

    // A verified field witness is a genuine lower bound, not merely a
    // post-processing hint.  Feeding it in here lets the descending-b search
    // skip every pair at or below that value and makes b_witness = b_T an
    // immediate exact answer.  The upper bound starts at the same floor:
    // after every larger b-stratum has been proved obstructed, the witness
    // itself shows that the remaining maximum is at least KnownLower.
    lowerFloor := Max(bM, KnownLower);
    BWlowerSplit := lowerFloor;
    BWupperLocal := lowerFloor;
    splitCandidates := [];
    localCandidates := [];
    undetermined := 0;
    centralStalled := 0;

    if lowerFloor ge bT then
        return bT, bT, splitCandidates, localCandidates, undetermined, centralStalled;
    end if;

    sound := policy`name eq "sound";

    // evaluated_pairs may be a Magma List (its entries contain records), and
    // Sort with a comparison function only accepts sequences.  Sort a sequence
    // of integer indices instead, then rebuild the list in decreasing b-value.
    // This also leaves the caller's evaluated_pairs unchanged.
    pairOrder := [1..#evaluated_pairs];
    Sort(~pairOrder, func< i, j | evaluated_pairs[j][3] - evaluated_pairs[i][3] >);
    pairs := [* evaluated_pairs[i] : i in pairOrder *];

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
            allow, v := LocalTestsAllowPair(
                ebp, policy : Raw := raw, MaxQuotients := MaxQuotients
            );
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
                    certificate_kind  := "",
                    proof_scope       := "upper_only",
                    local_verdict     := v
                >);
            elif sound then
                continue;   // proven obstructed: cannot be properly solvable
            end if;
        end if;

        autoSolved, why, ebp1, certKind, proofScope := CertifyAdmissibleDetailed(
            ebp, d : Policy := policy, Raw := raw, SupplementDepth := SupplementDepth
        );
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
                certificate_kind  := certKind,
                proof_scope       := proofScope,
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
