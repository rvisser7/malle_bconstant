// =====================================================================
// known_residuals.m  --  residual shapes whose proper solvability is known
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m
//
// Applied to a residual left over after MaximalSplitReduction, i.e. an
// embedding problem
//
//     1 -> K -> G_r -pi-> B -> 1,     phi : G_Q ->> B cyclotomic,
//
// which the nilpotent split-tower could not reduce further.  There is no
// general algorithm here: deciding proper solvability in general is the
// inverse Galois problem with a compatibility condition.  What this file is
// instead is an explicit TABLE of shapes, each with a citation, plus an
// honest "false" with a reason for everything else -- so that the table
// grows deliberately rather than by silent fallthrough.
//
// Three shapes are recognised, all requiring the residual to be split.
//
// (1) DIRECT PRODUCT  G_r = K x B.
//     A proper solution is a pair (psi, phi) with psi : G_Q ->> K and
//     Q(psi) cap Q(phi) = Q.  Enough to know K has infinitely many
//     realisations over Q, which holds when
//       - K is solvable (Shafarevich, with ramification chosen away from
//         the finitely many primes ramified in Q(phi)), or
//       - K has a regular realisation over Q(t) (table below; Hilbert
//         irreducibility then gives infinitely many specialisations, and
//         disjointness from one fixed abelian field is free).
//
// (2) GAR.  Residual split, with kernel K having the GAR property over Q.
//     If K has GAR over Q then EVERY split embedding problem with kernel K
//     is properly solvable, for any B acting through Aut(K) -- not merely
//     B = C_2.  See Malle-Matzat, "Inverse Galois Theory" [MM99], III.
//     This covers A_n < S_n over C_2, but equally A_5 : C_4 over C_4 and
//     PSL(2,7) < PGL(2,7) over C_2.
//
// (3) INDUCED / WREATH  G_r = T wr B with K = T^#B the base group.
//     G_r-extensions with wreath quotient phi correspond to T-extensions of
//     the field F = Q(phi) whose #B conjugates are linearly disjoint; this
//     is the argument of Wang's Lemma 3.8.  Needs T realisable over F with
//     infinitely many independent realisations, so the same test as (1).
//     Implemented for #B = 2 only.
//
// DELIBERATE OMISSION.  Solvable K is accepted in shape (1) but NOT in
// shapes (2) or (3) with a non-direct action, because there one needs a
// B-EQUIVARIANT realisation and Shafarevich does not supply that.  That gap
// is real; do not paper over it by testing IsSolvable at the top.

// ---------------------------------------------------------------------
// Groups with a known regular realisation over Q(t).
// Widen freely -- A_n and S_n have GAR for all n >= 5, the bound of 9 here
// is only to keep the isomorphism tests cheap.
// ---------------------------------------------------------------------
// Groups with the GAR property over Q.  GAR is the strong condition: it
// certifies ANY split embedding problem with this kernel.
//
// NEEDS CONFIRMATION before these values are published.  The entries are
// standard but are cited from the literature, not verified here.
HasGAROverQ := function(K)
    for m in [5..9] do
        if #K eq Factorial(m) div 2 and IsIsomorphic(K, Alt(m)) then
            return true, Sprintf("A%o (GAR over Q, [MM99])", m);
        end if;
    end for;
    if #K eq 168 and IsIsomorphic(K, PSL(2, 7)) then
        return true, "PSL(2,7) (GAR over Q, [MM99])";
    end if;
    return false, "";
end function;

// Weaker: groups realisable over Q with infinitely many linearly disjoint
// realisations.  Enough for the DIRECT PRODUCT branch only.
KnownRegularOverQ := function(K)
    if IsSolvable(K) then
        return true, "solvable (Shafarevich)";
    end if;
    gar, why := HasGAROverQ(K);
    if gar then return true, why; end if;
    for m in [5..9] do
        if #K eq Factorial(m) and IsIsomorphic(K, Sym(m)) then
            return true, Sprintf("S%o (regular over Q(t))", m);
        end if;
    end for;
    if #K eq 336 and IsIsomorphic(K, PGL(2, 7)) then
        return true, "PGL(2,7) (regular over Q(t))";
    end if;
    if #K eq 1512 then
        try
            if IsIsomorphic(K, PGammaL(2, 8)) then
                return true, "PGammaL(2,8) (regular over Q(t))";
            end if;
        catch e
            ;
        end try;
    end if;
    return false, "";
end function;

// A complement to K in G_r that is normal, i.e. G_r = K x H.
HasNormalComplement := function(Gr, K)
    for R in NormalSubgroups(Gr) do
        H := R`subgroup;
        if #H * #K eq #Gr and #(H meet K) eq 1 then
            return true, H;
        end if;
    end for;
    return false, sub< Gr | Id(Gr) >;
end function;

// Shape (3), #B = 2 only: K = T x T^g with T normal in K and swapped by any
// g outside K.
IsWreathResidual := function(Gr, K, pi)
    if #Gr div #K ne 2 then return false, sub< Gr | Id(Gr) >; end if;
    g := Rep({ x : x in Generators(Gr) | pi(x) ne Id(Codomain(pi)) }
             join { Id(Gr) });
    if g eq Id(Gr) then return false, sub< Gr | Id(Gr) >; end if;
    for R in NormalSubgroups(K) do
        T := R`subgroup;
        if #T eq 1 or #T^2 ne #K then continue; end if;
        Tg := T^g;
        if #(T meet Tg) eq 1 and #sub< Gr | T, Tg > eq #K then
            return true, T;
        end if;
    end for;
    return false, sub< Gr | Id(Gr) >;
end function;

// ---------------------------------------------------------------------
// Returns true only when the residual is PROPERLY solvable on the strength
// of one of the three cited shapes.  The second return value is a reason
// string, meant to be logged whether the answer is true or false.
// ---------------------------------------------------------------------
KnownResidualIsProperlySolvable := function(ebp1)
    Gr := ebp1`G;
    B  := ebp1`B;
    pi := ebp1`pi;
    K  := Kernel(pi);

    if #K eq 1 then return true, "trivial residual"; end if;

    ok := IsSplitKernel(Gr, K);
    if not ok then
        return false, "residual not split; arithmetic case";
    end if;

    // (1) direct product
    isDirect := HasNormalComplement(Gr, K);
    if isDirect then
        good, why := KnownRegularOverQ(K);
        if good then
            return true, "direct product, K " cat why;
        end if;
        return false, Sprintf("direct product but K (order %o) not in table", #K);
    end if;

    // (2) GAR: split residual whose kernel has GAR over Q.  No constraint
    // on B -- that is the whole point of GAR.
    gar, whyGar := HasGAROverQ(K);
    if gar then
        return true, "split residual, kernel " cat whyGar;
    end if;

    // (3) induced / wreath
    isWr, T := IsWreathResidual(Gr, K, pi);
    if isWr then
        good, why := KnownRegularOverQ(T);
        if good then
            return true, "wreath T wr C2, T " cat why;
        end if;
        return false, Sprintf("wreath but T (order %o) not in table", #T);
    end if;

    return false, Sprintf("split non-direct residual, K order %o: no citation",
                          #K);
end function;
