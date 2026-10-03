// =====================================================================
// intersection_body.m  --  how much does the exact-intersection gap matter?
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering,
//                        i.e. load this LAST, exactly like driver.m.
//
// THE GAP (README assumption 3).  Conjecture 6 counts liftings with
// K cap Q(mu_d) = F EXACTLY.  A certificate proves that (pi, phi) is properly
// solvable, i.e. that SOME G-extension K has F inside it; it says nothing
// about K cap Q(mu_d), which may be a larger F'.
//
// WHAT CAN BE SAID ANYWAY.  Let K witness (pi, phi) and F' = K cap Q(mu_d).
// Then K witnesses, with exact intersection, the REFINEMENT (pi', phi'):
// N' = Gal of K over F' (so N' <= N = Ker(pi)), G/N' = Gal(F'/Q), and pi',
// phi' compatible with pi, phi.  So, under Conjecture 6,
//
//     b_W >= L_safe := min over refinements R of (pi, phi), including
//                      (pi, phi) itself, of b(R),
//
// where
//   * b(R) := 0 if Ker(R) contains no minimal element (Theorem 2.16 drops
//     R: such K are counted with a smaller power of X, so they contribute
//     nothing to b);
//   * refinements PROVEN locally obstructed are skipped: no K can have
//     that intersection.
// The final value is max(L_safe, b_M), b_M being the standing assumption 1.
//
// L_safe = L for a group means assumption 3 cannot have moved its lower
// bound.  This prints every group, flagging the ones where it differs.
//
// Only the pair that fixed L is examined: if it is unsafe, a lower certified
// pair might still be safe, so a flagged group's true safe bound may lie
// between the printed L_safe and L.

// Does P1 refine P?  Ker(P1) <= Ker(P), and the identification
// G/Ker(P1) = Gal(F1/Q) induces G/Ker(P) = Gal(F/Q).  Pairs from different
// Gpiphi calls live on different copies of C and B, so everything is
// compared through G and through residues mod d.
IsRefinementOfPair := function(P1, P)
    if not (Kernel(P1`pi) subset Kernel(P`pi)) then return false; end if;
    R1 := Codomain(P1`f);                  // Z/d as P1's unit map sees it
    for i in [1 .. Ngens(P`C)] do
        u := R1!(Integers()!(P`f(P`C.i)));  // same residue, P1's copy of Z/d
        c1 := u @@ P1`f;
        g := P1`phi(c1) @@ P1`pi;
        if P`pi(g) ne P`phi(P`C.i) then return false; end if;
    end for;
    return true;
end function;

// bP: b(P) itself, from evaluated_pairs.
SafeLowerBoundForPair := function(G, d, P, bP, evaluated_pairs, bM)
    allPairs := Gpiphi(G, d);                 // unpruned: every refinement
    KP := Kernel(P`pi);
    Lsafe := bP;
    nref := 0;
    worst := "";
    for P1 in allPairs do
        if #Kernel(P1`pi) eq #KP then continue; end if;     // proper only
        if not IsRefinementOfPair(P1, P) then continue; end if;
        nref +:= 1;

        b1 := 0;                                           // pruned => 0
        for item in evaluated_pairs do
            P2 := item[2];
            if #Kernel(P2`pi) eq #Kernel(P1`pi) and IsRefinementOfPair(P2, P1) then
                b1 := item[3]; break;
            end if;
        end for;
        if b1 ge Lsafe then continue; end if;

        allow := LocalTestsAllowPair(P1, DefaultLocalPolicy);
        if not allow then continue; end if;                // no K can have it

        Lsafe := b1;
        worst := Sprintf("#B'=%o b'=%o", #P1`B, b1);
    end for;
    return Max(Lsafe, bM), nref, worst;
end function;

DiagnoseIntersectionIndices := procedure(n, indices, orderingName)
    printf "degree %o, ordering %o: exact-intersection check\n", n, orderingName;
    print "label|b_M|b_T|L|U|L_safe|refinements|flag";
    unsafe := 0;
    for i in indices do
        G := TransitiveGroup(n, i);
        d, a, nS, nP, bM, bT, ev := EvaluatePairs(G);
        L, U, splitC := BWBoundsFromPairs(d, ev, bM, bT, DefaultLocalPolicy);
        if #splitC eq 0 then
            printf "%oT%o|%o|%o|%o|%o|%o|0|\n", n, i, bM, bT, L, U, L;
            continue;
        end if;
        j := splitC[1]`pair_index;
        found := false;
        for item in ev do
            if item[1] eq j then P := item[2]; bP := item[3]; found := true; break; end if;
        end for;
        assert found;
        Ls, nref, worst := SafeLowerBoundForPair(G, d, P, bP, ev, bM);
        flag := Ls lt L select "UNSAFE " cat worst else "";
        if Ls lt L then unsafe +:= 1; end if;
        printf "%oT%o|%o|%o|%o|%o|%o|%o|%o\n", n, i, bM, bT, L, U, Ls, nref, flag;
    end for;
    printf "TOTAL unsafe lower bounds: %o\n", unsafe;
end procedure;
