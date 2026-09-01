// =====================================================================
// certify.m  --  the certificate chain
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m,
//   local_verdict.m, and every certificate module it dispatches to:
//   certificates/shared.m, certificates/structural.m,
//   certificates/central.m, certificates/q8.m.  Load this LAST of them.
//
// CertifyAdmissible answers one question: is this (pi, phi) pair PROPERLY
// solvable?  A true return may raise BWlowerSplit.
//
// THE ONE ASYMMETRY THAT MATTERS.  A local test may never RAISE
// BWlowerSplit on its own, and a certificate may never LOWER BWupperLocal.
// certificates/central.m looks like a violation of the first rule and is
// not: it uses local data only in the direction where a lift is exhibited
// at every place, which over Q with a central kernel is equivalent to
// proper solvability.  Every other certificate is field-theoretic or
// group-theoretic.  See "The two bounds" in magma/README.md.
//
// Adding a certificate is now a new file under certificates/ plus one line
// in CertificateChain, rather than another hand-written if-block.  Each
// entry has the uniform signature
//
//     f(ebp1, d, policy) -> ok, reason
//
// with ebp1 the maximally split-reduced residual.

CertEntryStructural := function(ebp1, d, policy)
    ok, why := StructuralResidualIsProperlySolvable(ebp1);
    return ok, why;
end function;

CertEntryCentral := function(ebp1, d, policy)
    ok, why := CertifyCentralResidual(ebp1, policy);
    return ok, why;
end function;

CertEntryQ8 := function(ebp1, d, policy)
    ok, why := CertifyResidualQ8(ebp1, d);
    return ok, why;
end function;

// Order: cheapest and most general first.  central before q8 because it
// subsumes the Q8 (a) shape and a good deal besides.
CertificateChain := [*
    < "structural", CertEntryStructural >,
    < "central",    CertEntryCentral    >,
    < "q8",         CertEntryQ8         >
*];

// Returns: ok, reason, ebp1.
//
// The chain is offered EVERY dead end of the split tower, not one chosen
// representative.  A proper solution of any leaf climbs back up its own
// branch to a proper solution of the original, so stopping at the first leaf
// that certifies is correct and choosing a leaf in advance is not: which
// residual a certificate can handle does not follow from its size.  See the
// note above TowerLeaves in split_tower.m.
//
// ebp1 is handed back so callers do not repeat the reduction for their
// diagnostics: the certifying leaf on success, the smallest-kernel leaf on
// failure.
CertifyAdmissible := function(ebp, d : Policy := DefaultLocalPolicy)
    leaves, fullySplit := SplitReductionLeaves(ebp);
    if fullySplit then
        return true, "nilpotent split tower to trivial kernel", leaves[1];
    end if;

    best := leaves[1];
    for e in leaves do
        if #Kernel(e`pi) lt #Kernel(best`pi) then best := e; end if;
    end for;

    reasons := "";
    for k := 1 to #leaves do
        ebp1 := leaves[k];
        for entry in CertificateChain do
            ok, why := entry[2](ebp1, d, Policy);
            if ok then
                return true,
                       Sprintf("leaf %o of %o (#G = %o, #Ker = %o), %o: %o",
                               k, #leaves, #ebp1`G, #Kernel(ebp1`pi),
                               entry[1], why),
                       ebp1;
            end if;
            if k eq 1 then
                reasons := reasons cat entry[1] cat ": " cat why cat "; ";
            end if;
        end for;
    end for;

    if #leaves gt 1 then
        reasons := reasons cat Sprintf("(and no certificate on any of the "
                                       cat "other %o leaves)", #leaves - 1);
    end if;
    return false, reasons, best;
end function;
