// =====================================================================
// certify.m  --  the certificate chain
// =====================================================================
//
// Requires (load first): records.m, splitting.m, and every certificate
// module it dispatches to: split_tower.m, known_residuals.m,
// q8_certificate.m.  Load this LAST of the certificate files; the modules
// it calls are peers and may be loaded in any order among themselves.
//
// CertifyAdmissible answers one question: is this (pi, phi) pair PROPERLY
// solvable?  A true return may raise BWlowerSplit.  It must never be used
// to lower BWupperLocal, and a local test must never be used to raise
// BWlowerSplit -- see "The two bounds" in magma/README.md.
//
// The chain, in order of decreasing generality:
//
//   1. split_tower.m       nilpotent split tower down to the trivial
//                          kernel; [NSW, (9.6.10)]
//   2. known_residuals.m   table of residual shapes with citations
//   3. q8_certificate.m    Witt's criterion for residual Q8 problems
//
// The second return value is a citation string, true or false.  On failure
// it is the residual table's reason, which is the more informative
// diagnosis: it names the shape that was left over rather than merely
// reporting that the shape was not Q8.

CertifyAdmissible := function(ebp, d)
    ebp1, fullySplit := MaximalSplitReduction(ebp);
    if fullySplit then
        return true, "nilpotent split tower";
    end if;

    ok, why := KnownResidualIsProperlySolvable(ebp1);
    if ok then
        return true, why;
    end if;

    okQ8, whyQ8 := CertifyResidualQ8(ebp1, d);
    if okQ8 then
        return true, whyQ8;
    end if;

    return false, why;
end function;
