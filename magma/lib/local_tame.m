// =====================================================================
// Local checking (tame finite places and the real place)
// =====================================================================
//
// Extracted verbatim from compute_all_fast.m. The code below is unchanged
// byte-for-byte, so the split cannot alter any computed value.
//
// Requires (load first): records.m

UnitInteger := function(c, f)
    return IntegerRing()!f(c);
end function;

// OPTIMISED: was a linear scan over every element of G. `@@` asks Magma for a
// preimage directly, and `b in Image(pi)` decides existence without enumerating.
// Which preimage comes back does not matter: every caller then ranges over the
// whole coset X0*N, which is the full preimage of b either way.
HasPreimage := function(pi, b)
    if b in Image(pi) then
        return true, b @@ pi;
    end if;
    return false, Id(Domain(pi));
end function;

// How large Kernel(pi) has to get before the conjugacy machinery below is
// worth its overhead.  Both branches decide exactly the same predicate, so
// this only trades one cost model for another.
//
// TO TEST THE FAST BRANCH: set this to 0, which forces every call down it,
// and run run_parallel.py --verify.  Left at 64, a verify pass over the small
// degrees may never execute it at all.
TameLiftDirectLimit := 64;

IsLocalLiftableTameByBImages := function(ebp, p, bX, bY)
    G  := ebp`G; pi := ebp`pi; N  := Kernel(pi);

    okX, X0 := HasPreimage(pi, bX);
    if not okX then return false, "No lift of Frobenius image", <Id(G), Id(G)>; end if;

    okY, Y0 := HasPreimage(pi, bY);
    if not okY then return false, "No lift of inertia image", <Id(G), Id(G)>; end if;

    // We need X in X0*N and Y in Y0*N with X*Y*X^-1 = Y^p.
    Nseq := [ n : n in N ];
    Ys   := [ Y0*n : n in Nseq ];
    Yps  := [ Y^p : Y in Ys ];

    // ---- small kernels: the direct search, unchanged -------------------
    if #Nseq le TameLiftDirectLimit then
        for nX in Nseq do
            X  := X0*nX;
            Xi := X^(-1);
            for k := 1 to #Ys do
                if X*Ys[k]*Xi eq Yps[k] then
                    return true, "Liftable", <X, Ys[k]>;
                end if;
            end for;
        end for;
        return false, "No pair of lifts satisfies tame relation", <Id(G), Id(G)>;
    end if;

    // ---- large kernels: |N| coset tests instead of |N|^2 pairs ---------
    //
    // Fix Y.  The set S = { g in G : g*Y*g^-1 = Y^p } is empty when Y^p is not
    // conjugate to Y, and is otherwise the coset w*C_G(Y) for any single w with
    // w*Y*w^-1 = Y^p:
    //
    //     g*Y*g^-1 = w*Y*w^-1  <=>  (w^-1*g) centralises Y  <=>  g in w*C_G(Y).
    //
    // So "does some X in X0*N work for this Y?" becomes "does w*C_G(Y) meet
    // X0*N?", and since N is normal in G the product N*C_G(Y) is a subgroup:
    //
    //     (w*C) meet (X0*N) non-empty
    //       <=> exists c in C, n in N with w*c = X0*n
    //       <=> exists c in C with X0^-1*w*c in N
    //       <=> X0^-1*w in N*C^-1 = N*C = <N, C>.
    //
    // One membership test per Y, in place of a scan over all of X0*N.
    X0i   := X0^(-1);
    Ngens := Generators(N);

    for k := 1 to #Ys do
        Y := Ys[k];

        // Magma's IsConjugate returns t with Y^t = t^-1*Y*t, so invert it to
        // get the left-conjugation convention used above.
        okc, t := IsConjugate(G, Y, Yps[k]);
        if not okc then continue; end if;
        w := t^(-1);

        CY := Centraliser(G, Y);
        NC := sub< G | Ngens join Generators(CY) >;

        if not (X0i*w in NC) then continue; end if;

        // A solution exists.  Recover an explicit X in (X0*N) meet (w*C_G(Y)):
        // one pass over N, and only on the branch that already succeeded, so it
        // does not affect the asymptotics.
        wi := w^(-1);
        for n in Nseq do
            X := X0*n;
            if wi*X in CY then
                return true, "Liftable", <X, Y>;
            end if;
        end for;

        // Unreachable: the membership test above proves the intersection is
        // non-empty, so the loop must have found X.  Fail loudly rather than
        // silently reporting "not liftable" if that reasoning is ever wrong.
        error "IsLocalLiftableTameByBImages: coset intersection was certified " *
              "non-empty but no witness was found -- this is a bug";
    end for;

    return false, "No pair of lifts satisfies tame relation", <Id(G), Id(G)>;
end function;

IsLocalLiftableTameByCImages := function(ebp, p, xC, yC)
    phi := ebp`phi;
    bX := phi(xC); bY := phi(yC);
    return IsLocalLiftableTameByBImages(ebp, p, bX, bY);
end function;

CyclotomicFrobeniusAtPrime := function(C, f, d, p)
    e := Valuation(d, p); ppow := p^e; m := d div ppow;
    for c in C do
        a := UnitInteger(c, f);
        cond_p_part := (a mod ppow) eq 1;
        if m eq 1 then
            cond_m_part := true;
        else
            cond_m_part := (a mod m) eq (p mod m);
        end if;
        if cond_p_part and cond_m_part then return c; end if;
    end for;
    error "Could not find cyclotomic Frobenius element.";
end function;

CyclotomicInertiaAtPrime := function(C, f, d, p)
    e := Valuation(d, p); ppow := p^e; m := d div ppow;
    gens := [];
    for c in C do
        a := UnitInteger(c, f);
        if m eq 1 then Append(~gens, c);
        elif (a mod m) eq 1 then Append(~gens, c);
        end if;
    end for;
    if #gens eq 0 then return sub< C | Id(C) >; end if;
    return sub< C | gens >;
end function;

PrimeToPPartOfFiniteAbelianSubgroup := function(H, p)
    gens := [];
    for h in Generators(H) do
        n := Order(h); v := Valuation(n, p);
        Append(~gens, (p^v)*h);
    end for;
    if #gens eq 0 then return sub< H | Id(H) >; end if;
    return sub< H | gens >;
end function;

PPrimaryPartOfFiniteAbelianSubgroup := function(H, p)
    gens := [];
    for h in Generators(H) do
        n := Order(h); nprime := n div p^Valuation(n, p);
        Append(~gens, nprime*h);
    end for;
    if #gens eq 0 then return sub< H | Id(H) >; end if;
    return sub< H | gens >;
end function;

InertiaImageInBAtPrime := function(ebp, p)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; B := ebp`B;
    d := ebp`d;
    I := CyclotomicInertiaAtPrime(C, f, d, p);
    imgs := [ phi(t) : t in Generators(I) ];
    if #imgs eq 0 then return sub< B | Id(B) >; end if;
    return sub< B | imgs >;
end function;

TameInertiaImageInBAtPrime := function(ebp, p)
    H := InertiaImageInBAtPrime(ebp, p);
    return PrimeToPPartOfFiniteAbelianSubgroup(H, p);
end function;

WildInertiaImageInBAtPrime := function(ebp, p)
    H := InertiaImageInBAtPrime(ebp, p);
    return PPrimaryPartOfFiniteAbelianSubgroup(H, p);
end function;

IsTamelyRamifiedInBAtPrime := function(ebp, p)
    Htame := TameInertiaImageInBAtPrime(ebp, p);
    Hwild := WildInertiaImageInBAtPrime(ebp, p);
    return (#Htame gt 1) and (#Hwild eq 1);
end function;

TamelyRamifiedPrimesForEbp := function(ebp)
    G := ebp`G; d := ebp`d;
    primes := [];
    for q in Factorization(d) do
        p := q[1];
        if IsTamelyRamifiedInBAtPrime(ebp, p) then Append(~primes, p); end if;
    end for;
    return primes;
end function;

IsCyclotomicTameLocallyLiftableAtPrime := function(ebp, p)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; B := ebp`B;
    d := ebp`d;
    xC := CyclotomicFrobeniusAtPrime(C, f, d, p);
    bX := phi(xC);
    Htame := TameInertiaImageInBAtPrime(ebp, p);
    Hwild := WildInertiaImageInBAtPrime(ebp, p);

    if #Htame eq 1 then return false, "Tame inertia image is trivial", <Id(G), Id(G)>; end if;
    if #Hwild gt 1 then return false, "Wild inertia image is nontrivial", <Id(G), Id(G)>; end if;
    if not IsCyclic(Htame) then return false, "Tame inertia image is not cyclic", <Id(G), Id(G)>; end if;

    gensHtame := [ h : h in Htame | Order(h) eq #Htame ];
    for h in gensHtame do
        bY := B!h;
        ok, msg, wit := IsLocalLiftableTameByBImages(ebp, p, bX, bY);
        if ok then return true, "Liftable for some tame inertia generator", wit; end if;
    end for;
    return false, "No generator of tame inertia image is locally liftable", <Id(G), Id(G)>;
end function;

IsLocallyLiftableAtAllTameFinitePlaces := function(ebp)
    primes := TamelyRamifiedPrimesForEbp(ebp);
    reports := [];
    for p in primes do
        ok, msg, wit := IsCyclotomicTameLocallyLiftableAtPrime(ebp, p);
        Append(~reports, <p, ok, msg>);
        if not ok then return false, reports; end if;
    end for;
    return true, reports;
end function;

IsRealLocallyLiftable := function(ebp)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; pi := ebp`pi;
    d := ebp`d;
    found := false; cminus := Id(C);

    for c in C do
        a := UnitInteger(c, f);
        if (a mod d) eq ((-1) mod d) then
            found := true; cminus := c; break;
        end if;
    end for;

    if not found then return true, "No -1 element found", Id(G); end if;
    b := phi(cminus);

    // OPTIMISED: { g : pi(g) eq b } is exactly the coset g0*Kernel(pi), so scan
    // that instead of all of G.  Same set of candidates, |N| of them instead of
    // |G|.  (A different witness element may be returned; no caller uses it --
    // PassesCheckedLocalTests keeps only the boolean.)
    if not (b in Image(pi)) then
        return false, "Real place not liftable", Id(G);
    end if;
    g0 := b @@ pi;
    N  := Kernel(pi);
    for n in N do
        g := g0*n;
        if g^2 eq Id(G) then
            return true, "Real place liftable", g;
        end if;
    end for;
    return false, "Real place not liftable", Id(G);
end function;

IsLocallyLiftableTameAndReal := function(ebp)
    okFinite, finiteReports := IsLocallyLiftableAtAllTameFinitePlaces(ebp);
    okReal, realMsg, realWitness := IsRealLocallyLiftable(ebp);
    return okFinite and okReal, finiteReports, <okReal, realMsg>;
end function;

PassesCheckedLocalTests := function(ebp)
    assert Modulus(Codomain(ebp`f)) eq ebp`d;
    ok, finiteReports, realReport := IsLocallyLiftableTameAndReal(ebp);
    return ok;
end function;
