// =====================================================================
// Local checking (tame finite places and the real place)
// =====================================================================
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

// b1 - b2 in B, whether B is written additively (GrpAb, as Gpiphi builds
// it) or multiplicatively (a quotient permutation group, as some tests and
// diagnostics build it).
BDiff := function(b1, b2)
    if Type(b1) eq GrpAbElt then return b1 - b2; end if;
    return b1 * b2^(-1);
end function;

// Is there X, Y in G with pi(X) = bX, pi(Y) = bY and X*Y*X^-1 = Y^p ?
//
// WORKS ON CLASSES OF G, NOT ON ELEMENTS OF N.  B is abelian, so pi is
// constant on conjugacy classes, and if (X, Y) is a solution then so is
// (h X h^-1, h Y h^-1) for every h, with the same images in B.  So Y may be
// taken to be a class representative.  For a fixed Y the solutions X form
// the coset w*C_G(Y) of any one w with w Y w^-1 = Y^p:
//
//     X Y X^-1 = w Y w^-1  <=>  w^-1 X in C_G(Y),
//
// and pi(w*c) = bX for some c in C_G(Y) iff bX - pi(w) lies in pi(C_G(Y)).
// That last test is inside B.  Cost: one ClassMap per class with
// pi(rep) = bY, and IsConjugate + Centraliser only for the classes that are
// stable under p-th powering.  The old version enumerated all of N, and
// for each Y in a coset of N ran IsConjugate and Centraliser.
//
// p-th powering: X Y X^-1 = Y^p forces ord(Y^p) = ord(Y), i.e. p does not
// divide ord(Y), so the lift genuinely factors through the tame quotient.
IsLocalLiftableTameByBImages := function(ebp, p, bX, bY)
    G := ebp`G; pi := ebp`pi; B := Codomain(pi);

    if not (bX in Image(pi)) then
        return false, "No lift of Frobenius image", <Id(G), Id(G)>;
    end if;
    if not (bY in Image(pi)) then
        return false, "No lift of inertia image", <Id(G), Id(G)>;
    end if;

    cls := Classes(G);
    cm  := ClassMap(G);
    for i := 1 to #cls do
        Y := cls[i][3];
        if pi(Y) ne bY then continue; end if;
        if cm(Y^p) ne i then continue; end if;      // Y^p not conjugate to Y

        okc, t := IsConjugate(G, Y, Y^p);           // Y^t = t^-1 Y t = Y^p
        assert okc;
        w := t^(-1);                                // w Y w^-1 = Y^p

        CY := Centraliser(G, Y);
        rho := hom< CY -> B | [ pi(CY.k) : k in [1..Ngens(CY)] ] >;
        target := BDiff(bX, pi(w));
        if target in Image(rho) then
            X := w * (target @@ rho);
            assert X*Y*X^(-1) eq Y^p and pi(X) eq bX and pi(Y) eq bY;
            return true, "Liftable", <X, Y>;
        end if;
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

    // ONE generator suffices.  The tame relation holds for every topological
    // generator y of tame inertia, and if (X, Y) solves the problem for
    // bY = h then (X, Y^u) solves it for h^u, since X Y^u X^-1 = (Y^p)^u.
    // So all generators of Htame give the same answer; the old loop over all
    // of them repeated identical work on every failure.
    h := Rep({ h : h in Htame | Order(h) eq #Htame });
    ok, msg, wit := IsLocalLiftableTameByBImages(ebp, p, bX, B!h);
    if ok then return true, "Liftable (tame)", wit; end if;
    return false, "No tame lift for the tame inertia generator", <Id(G), Id(G)>;
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

    // Need g with pi(g) = b and g^2 = 1.  pi is constant on classes (B is
    // abelian), so it is enough to look at representatives of the classes of
    // elements of order 1 or 2.  The old version scanned the whole coset of N.
    for cl in Classes(G) do
        if cl[1] le 2 and pi(cl[3]) eq b then
            return true, "Real place liftable", cl[3];
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
