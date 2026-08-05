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

IsLocalLiftableTameByBImages := function(ebp, p, bX, bY)
    G  := ebp`G; pi := ebp`pi; N  := Kernel(pi);

    okX, X0 := HasPreimage(pi, bX);
    if not okX then return false, "No lift of Frobenius image", <Id(G), Id(G)>; end if;

    okY, Y0 := HasPreimage(pi, bY);
    if not okY then return false, "No lift of inertia image", <Id(G), Id(G)>; end if;

    // OPTIMISED: same iteration order and same first match as before, but the
    // Y coset and its p-th powers are built once instead of once per nX, and
    // X^(-1) once per outer step instead of once per pair.  That takes the
    // inner loop from (1 mult + 1 power + 1 inverse + 2 mult) down to 2 mults.
    Nseq := [ n : n in N ];
    Ys   := [ Y0*n : n in Nseq ];
    Yps  := [ Y^p : Y in Ys ];

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
    d := Exponent(G);
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
    G := ebp`G; d := Exponent(G);
    primes := [];
    for q in Factorization(d) do
        p := q[1];
        if IsTamelyRamifiedInBAtPrime(ebp, p) then Append(~primes, p); end if;
    end for;
    return primes;
end function;

IsCyclotomicTameLocallyLiftableAtPrime := function(ebp, p)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; B := ebp`B;
    d := Exponent(G);
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
    d := Exponent(G);
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
    ok, finiteReports, realReport := IsLocallyLiftableTameAndReal(ebp);
    return ok;
end function;
