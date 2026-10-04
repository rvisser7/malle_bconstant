// =====================================================================
// marking_body.m  --  is the p = 2 Demushkin marking in wild_prop.m safe?
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering,
//                        i.e. load this LAST, exactly like driver.m.
//
// wild_prop.m tests liftability at p = 2 through the Demushkin presentation
//
//     G_{Q_2}(2) = < x1, x2, x3 | x1^2 x2^4 [x2, x3] = 1 >,  [x,y] = x^-1 y^-1 x y,
//
// with the generators MARKED by their images in G^ab = (Q_2^x)^(2):
//
//     x1 -> rec(-4),   x2 -> rec(1/2),   x3 -> rec(-3).
//
// Write x_i -> rec(eps_i * 2^(t_i) * w_i), eps_i = +-1, w_i in 1 + 4 Z_2.
// What is PROVEN (see the notes on the patch):
//
//   * chi-values.  chi(x1) = -1, chi(x2) = 1 (Labute's normal form) and
//     chi(x3) = (-3)^-1 are mutually consistent WITH THIS COMMUTATOR
//     CONVENTION: in the Kummer quotient Z_2(1) : Z_2^x of
//     Q_2(mu_2^oo, 2^(1/2^oo)), law (a,u)(b,v) = (a + u b, uv), the
//     relation reads (3 + chi(x3)^-1) a_2 = 0, so chi(x3)^-1 = -3; the
//     opposite sign, +3, would fail.  The chi-values pin eps_i and w_i, and
//     the relation in G^ab forces t1 = -2 t2.
//   * t3 is irrelevant.  If (x1, x2, x3) is a basis with the relation, so is
//     (x2^-k x1 x2^k, x2, x3 x2^k) for every k in Z_2, and it has the same
//     chi-values; t2 is a unit (else the images do not span Q_2^x / squares),
//     so k = -t3/t2 makes t3 = 0.
//   * t1 = -2 t2 then follows.
//
// What is NOT proven: t2 = -1.  Any 2-adic unit t2 might be the one a
// Labute basis actually has.  It enters only through b2 = t2 * phi(Frob_2),
// Frob_2 the 2-primary part of Frobenius on the odd part of Q(mu_d), and
// b1 = phi(rec(-1)) - 2 b2.  So it matters only when phi(Frob_2) has order
// >= 4 (if the order is <= 2, every odd t2 gives the same b2, and 2 b2 = 0).
//
// This diagnostic finds every pair, with b above b_M, where p = 2 is wild
// and phi(Frob_2) has order >= 4, reruns the p = 2 search for EVERY odd
// residue t2 mod that order, and reports the pairs whose verdict depends on
// t2.  Production sound-mode code now uses this same all-markings criterion
// before returning a positive local certificate; this file remains useful for
// locating the pairs on which the unresolved marking actually matters.

MarkingSensitivityAtTwo := function(ebp)
    labels, cImages, bImages, IwildP, Dp := WildProPCyclotomicGeneratorData(ebp, 2);
    if #IwildP le 1 then return false, 0, [* *]; end if;   // not wild at 2

    o, variants := WildProPQ2MarkingVariants(ebp, cImages, bImages);
    if o le 2 then return false, o, [* *]; end if;

    H, P, Kp := WildProPSylowTargetData(ebp, Dp, 2);

    res := [* *];
    for V in variants do
        ok := WildProPSolveQ2RelationInSylow(ebp, P, Kp, V[2], V[3], V[4]);
        Append(~res, < V[1], ok >);
    end for;
    return true, o, res;
end function;

DiagnoseMarkingIndices := procedure(n, indices, orderingName)
    printf "degree %o, ordering %o: p = 2 marking sensitivity\n", n, orderingName;
    print "label|pair|b|ord(phi(Frob_2))|t2:liftable ...|flag";
    exposed := 0; sensitive := 0;
    for i in indices do
        G := TransitiveGroup(n, i);
        d, a, nS, nP, bM, bT, ev := EvaluatePairs(G);
        if d mod 2 ne 0 then continue; end if;
        for item in ev do
            if item[3] le bM then continue; end if;
            relevant, o, res := MarkingSensitivityAtTwo(item[2]);
            if not relevant then continue; end if;
            exposed +:= 1;
            vals := { r[2] : r in res };
            flag := #vals gt 1 select "SENSITIVE" else "";
            if #vals gt 1 then sensitive +:= 1; end if;
            printf "%oT%o|%o|%o|%o|%o|%o\n", n, i, item[1], item[3], o,
                   &cat[ Sprintf("%o:%o ", r[1], r[2]) : r in res ], flag;
        end for;
    end for;
    printf "TOTAL exposed pairs: %o, sensitive: %o\n", exposed, sensitive;
end procedure;
