// =====================================================================
// certificates/structural.m  --  field-independent residual shapes
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m
//   (was lib/known_residuals.m; renamed to say what distinguishes it from
//    the arithmetic certificates, which is that phi never appears here)
//
// Applied to a residual left over after MaximalSplitReduction:
//
//     1 -> K -> G_r -pi-> B -> 1,     phi : G_Q ->> B cyclotomic,
//
// which the nilpotent split tower could not reduce further.  There is no
// general algorithm: deciding proper solvability is the inverse Galois
// problem with a compatibility condition.  This is an explicit TABLE of
// shapes with citations, plus an honest "false" with a reason, so that the
// table grows deliberately rather than by silent fallthrough.
//
// Three shapes, all requiring the residual to be split.
//
// (1) DIRECT PRODUCT  G_r = K x B.  A proper solution is a pair (psi, phi)
//     with psi : G_Q ->> K and Q(psi) cap Q(phi) = Q.  Enough to know K has
//     infinitely many realisations over Q: K solvable (Shafarevich, with
//     ramification chosen away from the primes ramified in Q(phi)), or K
//     regular over Q(t) (table below, then Hilbert irreducibility).
//
// (2) GAR.  Residual split with kernel K having the GAR property over Q.
//     See Malle-Matzat [MM99] III.
//
// (3) INDUCED / WREATH  G_r = T wr B with K = T^#B the base group; Wang's
//     Lemma 3.8 argument.  Implemented for #B = 2 only.
//
// DELIBERATE OMISSION.  Solvable K is accepted in shape (1) but NOT in
// shapes (2) or (3) with a non-direct action, because there one needs a
// B-EQUIVARIANT realisation and Shafarevich does not supply that.  That gap
// is real; do not paper over it by testing IsSolvable at the top.
//
// FIXED: shape (3) used to call KnownRegularOverQ(T), which accepts ANY
// solvable T, contradicting the paragraph above.  For T wr C2 one needs a
// T-extension L/F (F = Q(phi) quadratic) with L and its conjugate L^sigma
// linearly disjoint over F.  For ABELIAN T that is class field theory (ramify
// at a prime of F split over Q but not at its conjugate; this is the
// situation of Wang's Lemma 3.8).  For T regular over Q(t) it is Hilbert
// irreducibility over F.  For general solvable T it may well be true, via
// Shafarevich with local conditions, but nothing here cites it, so shape (3)
// now accepts only those two cases.  This can only LOWER a certified lower
// bound, never produce a false one; diagnose before republishing.
//
// TWO ENTRIES NEED CONFIRMATION BEFORE PUBLICATION, both in shape (2):
//   * the GAR table is cited, not verified here;
//   * the usual GAR statement in [MM99] carries a centraliser hypothesis on
//     the ambient group, and the test below imposes no condition on B or on
//     C_{G_r}(K).  Check the exact form you are relying on.

// ---------------------------------------------------------------------
// Groups with the GAR property over Q: certifies ANY split embedding
// problem with this kernel.  A_n and S_n have GAR for all n >= 5; the bound
// of 9 is only to keep the isomorphism tests cheap.  Widen freely.
// ---------------------------------------------------------------------
//
// A6 in particular deserves a look before publication: Out(A6) = C2^2 is
// exceptional, and GAR is a statement about realising Aut(K).
HasGAROverQ := function(K)
    for m in [5..9] do
        if #K eq Factorial(m) div 2 and IsIsomorphic(K, Alt(m)) then
            return true, Sprintf("A%o (GAR over Q, [MM99] -- UNVERIFIED)", m);
        end if;
    end for;
    if #K eq 168 and IsIsomorphic(K, PSL(2, 7)) then
        return true, "PSL(2,7) (GAR over Q, [MM99] -- UNVERIFIED)";
    end if;
    return false, "";
end function;

// Groups regular over Q(t) (Galois group of a regular extension of Q(t)),
// hence over F(t) for every number field F, with infinitely many linearly
// disjoint specialisations by Hilbert irreducibility.  Non-solvable entries
// only; solvable groups are handled separately below.
KnownRegularTableOverQ := function(K)
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

// Realisable over Q with infinitely many linearly disjoint realisations.
// Enough for the DIRECT PRODUCT branch only.
KnownRegularOverQ := function(K)
    if IsSolvable(K) then
        return true, "solvable (Shafarevich)";
    end if;
    ok, why := KnownRegularTableOverQ(K);
    return ok, why;
end function;

// What shape (3), T wr C2, accepts: abelian T (class field theory) or T in
// the regular table.  NOT general solvable T; see the header.
KnownForWreathOverQuadratic := function(T)
    if IsAbelian(T) then
        return true, "abelian (class field theory over F)";
    end if;
    ok, why := KnownRegularTableOverQ(T);
    return ok, why;
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

// Shape (3), #B = 2 only: K = T x T^g with T normal in K, swapped by any g
// outside K.  (Any two elements outside K differ by an element of K, and
// T^g is normal in K, so T^h = T^g for every h outside K; in particular the
// complement found by IsSplitKernel does swap the factors.)
//
// FIXED: the element outside K used to be picked by Rep on a set with
// Id(Gr) unioned in as an emptiness guard, so Rep could return the guard
// itself and report a false negative.  Test for emptiness first, and fall
// back to a scan over Gr if no GENERATOR happens to lie outside K.
IsWreathResidual := function(Gr, K, pi)
    if #Gr div #K ne 2 then return false, sub< Gr | Id(Gr) >; end if;

    idB := Id(Codomain(pi));
    outside := { x : x in Generators(Gr) | pi(x) ne idB };
    if IsEmpty(outside) then
        outside := { x : x in Gr | pi(x) ne idB };
    end if;
    if IsEmpty(outside) then return false, sub< Gr | Id(Gr) >; end if;
    g := Rep(outside);

    for R in NormalSubgroups(K) do
        T := R`subgroup;
        // FIXED: (#T)^2, parenthesised.  "#T^2" invited a parse as #(T^2).
        if #T eq 1 or (#T)^2 ne #K then continue; end if;
        Tg := T^g;
        if #(T meet Tg) eq 1 and #sub< Gr | T, Tg > eq #K then
            return true, T;
        end if;
    end for;
    return false, sub< Gr | Id(Gr) >;
end function;

// ---------------------------------------------------------------------
// True only when the residual is PROPERLY solvable on the strength of one
// of the three cited shapes.  Second return value is a reason string, meant
// to be logged whether the answer is true or false.
// ---------------------------------------------------------------------
StructuralResidualIsProperlySolvable := function(ebp1)
    Gr := ebp1`G;
    pi := ebp1`pi;
    K  := Kernel(pi);

    if #K eq 1 then return true, "trivial residual"; end if;

    ok := IsSplitKernel(Gr, K);
    if not ok then
        return false, "residual not split; arithmetic case";
    end if;

    isDirect := HasNormalComplement(Gr, K);
    if isDirect then
        good, why := KnownRegularOverQ(K);
        if good then
            return true, "direct product, K " cat why;
        end if;
        return false, Sprintf("direct product but K (order %o) not in table", #K);
    end if;

    gar, whyGar := HasGAROverQ(K);
    if gar then
        return true, "split residual, kernel " cat whyGar;
    end if;

    isWr, T := IsWreathResidual(Gr, K, pi);
    if isWr then
        good, why := KnownForWreathOverQuadratic(T);
        if good then
            return true, "wreath T wr C2, T " cat why;
        end if;
        return false, Sprintf("wreath but T (order %o) not in table", #T);
    end if;

    return false, Sprintf("split non-direct residual, K order %o: no citation", #K);
end function;

// Backwards-compatible alias for anything still calling the old name.
KnownResidualIsProperlySolvable := function(ebp1)
    ok, why := StructuralResidualIsProperlySolvable(ebp1);
    return ok, why;
end function;
