// =====================================================================
// typo_report_body.m  --  what if the twisted action were reversed?
// =====================================================================
//
// Requires: an orbits.m + fullcheck.m for one ordering (load LAST).
//
// The early typo used  (x, y) . g = x g^y x^-1  instead of the correct
// (x, y) . g = x^-1 g^y x  (Wang, Def. 2.8 and Remark 2.13).
//
// KEY IDENTITY.  The wrong action of (x, y) in G(pi, phi) is the correct
// action of (x^-1, y), and (x, y) -> (x^-1, y) is a bijection
// G(pi, phi) -> G(pi, -phi), where -phi = (b -> -b) o phi.  Both are genuine
// group actions, so they have the same orbits:
//
//     b_wrong(pi, phi) = b_correct(pi, -phi).
//
// Consequences:
//   * the set of pairs is closed under phi -> -phi, so b_T is UNCHANGED;
//   * the trivial pair is its own partner, so b_M is UNCHANGED;
//   * b_W can change: the wrong code paired b(pi, -phi) with the
//     liftability of (pi, phi), and liftability is not symmetric under
//     phi -> -phi unless some automorphism of G preserving Ker(pi) induces
//     -1 on B.  Only B of exponent > 2 can be affected.
//
// So the typo is simulated exactly, with no new orbit counting, by
// swapping each pair's b-value with its -phi partner's and rerunning
// Phase 2.

// part[k] = index l of the pair with the same pi and phi_l = -phi_k.
NegPartners := function(pairs)
    kers := [ Kernel(it[2]`pi) : it in pairs ];
    part := [ 0 : k in [1..#pairs] ];
    for k := 1 to #pairs do
        e := pairs[k][2];
        Cg := [ c : c in Generators(e`C) ];
        for l := 1 to #pairs do
            if kers[l] ne kers[k] then continue; end if;
            f := pairs[l][2];
            if forall{ c : c in Cg | f`phi(c) eq -e`phi(c) } then
                part[k] := l; break;
            end if;
        end for;
        assert part[k] ne 0;    // -phi is surjective too, so it is in the list
    end for;
    return part;
end function;

TypoReport := procedure(n, indices)
    print "label|b_M|b_T|L|U|L_wrong|U_wrong|asymmetric_pairs|differs";
    for i in indices do
        G := TransitiveGroup(n, i);
        d, a, nS, nP, bM, bT, pairs := EvaluatePairs(G);
        L, U := BWBoundsFromPairs(d, pairs, bM, bT, DefaultLocalPolicy);

        part := NegPartners(pairs);
        wrong := [ < pairs[k][1], pairs[k][2], pairs[part[k]][3] > : k in [1..#pairs] ];
        // the identity predicts these two are unchanged
        assert #pairs eq 0 or
               Maximum([ w[3] : w in wrong ]) eq Maximum([ p[3] : p in pairs ]);
        asym := #[ k : k in [1..#pairs] | pairs[k][3] ne pairs[part[k]][3] ];

        Lw, Uw := BWBoundsFromPairs(d, wrong, bM, bT, DefaultLocalPolicy);
        printf "%oT%o|%o|%o|%o|%o|%o|%o|%o|%o\n", n, i, bM, bT, L, U, Lw, Uw, asym,
               (L ne Lw or U ne Uw) select "YES" else "no";
    end for;
end procedure;
