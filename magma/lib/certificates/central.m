// =====================================================================
// certificates/central.m  --  central kernels over Q, decided locally
// =====================================================================
//
// Requires (load first): records.m, local_tame.m, wild_prop.m,
//                        local_verdict.m
//
// THE STATEMENT.  Let k = Q and consider a residual
//
//     1 -> A -> G_r -pi-> B -> 1,     A = Ker(pi) contained in Z(G_r),
//
// so A is a trivial Galois module.  Then:
//
//   * LOCAL-GLOBAL.  Sha^2(Q, A) = 0 for every trivial module A, because
//     Sha^1(Q, mu_{2^r}) = 0 for all r -- 2 has full decomposition group in
//     Q(mu_{2^r})/Q -- so by Poitou-Tate the problem is solvable iff it is
//     solvable at every place.  [Wang, Lemma 4.3 and Theorem 4.5, with the
//     remark after Theorem 4.6 for k = Q; NSW08 Prop. 3.5.9, Thm 9.1.9.]
//
//   * SOLVABLE => PROPERLY SOLVABLE.  For a central kernel one twists a
//     solution by H^1(Q, A), i.e. by abelian extensions with group a
//     subgroup of A, to make the lifting surjective.  [Wang, proof of
//     Lemma 4.3.]
//
// So for central residuals the local machinery stops being merely a source
// of upper bounds and becomes a decision procedure that may also raise
// BWlowerSplit.  This subsumes the Q8 shape (a), whose kernel is Z(Q8) = C_2
// and whose Witt condition is exactly the Hilbert-symbol form of the local
// condition; it also covers C_4, C_8, C_2^r and every other central layer
// the split tower leaves behind.
//
// POLARITY WARNING.  Everywhere else a wrong local answer only shrinks an
// upper bound.  Here a wrong "locally solvable" would certify a FALSE lower
// bound.  That is why this certificate demands LocalVerdictYes at every
// place -- an exhibited lift -- and not merely the absence of a proven
// obstruction.  See the header of lib/local_verdict.m for which tests
// exhibit and which merely fail to refute.
//
// COMPLETENESS OF THE PLACE LIST.  LocalVerdict tests the real place and
// every p | d.  Any other place is unramified in Q(mu_d), hence in F, and an
// unramified phi_v lifts trivially: send Frobenius to any preimage and
// inertia to 1.  So an all-Yes verdict really is local solvability at every
// place of Q.

IsCentralResidual := function(ebp1)
    K := Kernel(ebp1`pi);
    return K subset Centre(ebp1`G);
end function;

CertifyCentralResidual := function(ebp1, policy)
    K := Kernel(ebp1`pi);

    if #K eq 1 then
        return true, "trivial residual";
    end if;
    if not IsCentralResidual(ebp1) then
        return false, Sprintf("kernel (order %o) is not central", #K);
    end if;

    v, reports := LocalVerdict(ebp1, policy);

    if v eq LocalVerdictYes then
        return true, Sprintf(
            "central kernel of order %o over Q: locally solvable at every place, "
            cat "so solvable (Sha^2 = 0) and properly solvable (twist by H^1)", #K);
    end if;
    if v eq LocalVerdictNo then
        return false, "central kernel, but locally obstructed";
    end if;
    return false, "central kernel, but the local verdict is undetermined at some place";
end function;
