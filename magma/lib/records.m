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
