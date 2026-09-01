// =====================================================================
// certificates/q8.m  --  residual Q8 problems, by Witt's criterion
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m,
//                        certificates/shared.m
//   (was lib/q8_certificate.m)
//
// After MaximalSplitReduction a great many pairs bottom out at a residual
// whose group is Q8.  There are exactly two shapes:
//
//   (a)  1 -> C_2 -> Q8 -> C2 x C2 -> 1,  phi cuts out F = Q(sqrt a, sqrt b)
//   (b)  1 -> C_4 -> Q8 -> C_2      -> 1,  phi cuts out F = Q(sqrt a)
//
// WITT (1936).  Q(sqrt a, sqrt b) embeds in a Q8-extension of Q iff the
// forms <a, b, ab> and <1, 1, 1> are equivalent over Q; that is, a, b, ab
// all positive and (a,b)(a,ab)(b,ab) = 1 at every place.
//
// Case (a) is Witt read off directly.  Solvable => properly solvable here
// for free: every proper subgroup of Q8 is cyclic, so its image in C2 x C2
// has order at most 2 and cannot be onto.  Note that (a) is ALSO covered by
// certificates/central.m, since C_2 = Z(Q8); the two are independent routes
// to the same answer and disagreement between them is a bug worth catching.
//
// Case (b) is the one that does not generalise, and it is why this file
// stays separate rather than becoming a table entry.  C_4 is NOT central in
// Q8, and the question is whether Q(sqrt a) is one of the three quadratic
// subfields of SOME Q8-field -- which works only because Aut(Q8) is
// transitive on the three C_4's, and needs a search over an auxiliary b
// with no analogue for other kernels.  Expanding the Hasse invariants,
// Witt(a,b) with a,b>0 is
//
//     (a,b)(a,-1)(b,-1) = 1,  i.e.  (b, -a) = (a, -1)  in Br(Q)[2],
//
// and the algebras (b,-a) are exactly those split by Q(sqrt -a).  So:
//
//   CRITERION.  For a > 0 squarefree, Q(sqrt a) lies in a Q8-extension of Q
//   iff at every place v where (a,-1) ramifies, -a is a nonsquare in Q_v.
//
// (Positivity of b is automatic: (b,-a)_oo = 1 for b > 0, and (a,-1)_oo = 1
// because a > 0.)  Case (b) is properly solvable exactly when this holds --
// an improper solution would be a C_4-extension, which is why the search
// over b is the right question and not merely solvability.
//
// The agreement of the criterion with brute force over b is no longer a
// claim in a comment: it is tests/test_q8_witt.m.

WittEmbeds := function(a, b)
    ab := a*b;
    if a le 0 or b le 0 then return false; end if;
    for p in [-1] cat BadPlaces([a, b, ab]) do
        if Hilb(a,b,p) * Hilb(a,ab,p) * Hilb(b,ab,p) ne 1 then
            return false;
        end if;
    end for;
    return true;
end function;

// Does Q(sqrt a) sit inside some Q8-extension of Q?
QuadraticInQ8 := function(a)
    if a le 0 then return false; end if;
    a := SquarefreeFactorization(a);
    if a eq 1 then return false; end if;
    for p in [-1] cat BadPlaces([a, -1, -a]) do
        if Hilb(a, -1, p) eq -1 then
            if IsSquareInQp(-a, p) then return false; end if;
        end if;
    end for;
    return true;
end function;

// ebp1 is assumed already maximally split-reduced.  True only when the pair
// is PROPERLY solvable.
CertifyResidualQ8 := function(ebp1, d)
    G := ebp1`G; B := ebp1`B; N := Kernel(ebp1`pi);
    if #G ne 8 or IdentifyGroup(G) ne <8, 4> then return false, "not Q8"; end if;

    resid := KernelResidues(ebp1, d);

    if #N eq 2 and #B eq 4 then
        quads := QuadraticSubfieldsOfPhi(d, resid);
        if #quads lt 2 then return false, "could not identify F"; end if;
        // F has exactly three quadratic subfields a, b, ab; Witt is
        // symmetric in the three, so any two of them decide it.
        a := quads[1]; b := quads[2];
        return WittEmbeds(a, b), Sprintf("biquadratic (%o, %o)", a, b);
    end if;

    if #N eq 4 and #B eq 2 then
        ok, a := QuadraticFieldOfSubgroup(d, resid);
        if not ok then return false, "could not identify F"; end if;
        return QuadraticInQ8(a), Sprintf("quadratic Q(sqrt %o)", a);
    end if;

    return false, "unexpected Q8 shape";
end function;
