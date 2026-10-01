/*****************************************************************************************

    WildProPLocalLiftability.m

    Wild local checking after passage to the maximal pro-p quotient.

    INPUT
    -----

        ebp = rec< EmbeddingProb | B, G, C, f, pi, phi >

    with B abelian, as in GeneratePiPhiList.txt.

    For a prime p, let Dp be the image in B of the local cyclotomic map after
    restriction to G_{Q_p}(p), the maximal pro-p quotient.  We test whether

        G_{Q_p}(p)  --->  Dp

    lifts through

        pi^(-1)(Dp) ---> Dp.

    The lift is NOT required to be surjective.  Since its finite image is a
    p-group, it is enough to search inside one Sylow p-subgroup P of
    pi^(-1)(Dp).  This is valid here because B is abelian: conjugating a
    possible p-group image into P does not change its image in B.

    LOCAL GROUPS
    ------------

    * p odd:

          G_{Q_p}(p) is free pro-p of rank 2.

      Hence the induced pro-p problem is automatically liftable once the two
      prescribed quotient images lift to P; pi(P)=Dp guarantees this.

    * p=2:

          G_{Q_2}(2)
            = < c1,c2,c3 | c1^2 c2^4 [c2,c3] = 1 >,

      where [x,y]=x^(-1)y^(-1)xy.  We use the marked generators

          c1 = rec(-4),
          c2 = rec(1/2),
          c3 = rec(-3).

      With arithmetic local reciprocity, their 2-adic cyclotomic values are

          chi(c1) = -1,
          chi(c2) = 1,
          chi(c3) = (-3)^(-1).

      The odd-order cyclotomic part of c2 is inverse Frobenius, and

          c1 = rec(-1) * c2^(-2).

      This marking satisfies the abelianized relation 2*c1+4*c2=0.  In
      particular, replacing (-3)^(-1) by 5 at arbitrary 2-power precision is
      not correct, although the two agree at low precision.

    MAIN INTERFACES
    ---------------

        WildlyRamifiedPrimesForEbpProP(ebp);

        IsCyclotomicWildProPLocallyLiftableAtPrime(ebp, p);

        IsLocallyLiftableAtAllWildProPPlaces(ebp);

        IsLocallyLiftableTameWildProPAndReal(ebp);

        CleanLocalLiftabilityReportWithWildProP(ebp);

        DetailedWildProPReportAtPrime(ebp, p);

*****************************************************************************************/


WildProPPrimeReportFormat := recformat<
    p,
    is_wild,
    source_description,
    generator_labels,
    C_generator_images,
    B_generator_images,
    wild_inertia_order,
    Dp_order,
    local_preimage_order,
    sylow_order,
    sylow_kernel_order,
    pairs_tested,
    liftable,
    message,
    witness
>;


/*****************************************************************************************
    Basic helpers.
*****************************************************************************************/

WildProPUnitInteger := function(c, f)
    return IntegerRing()!f(c);
end function;


WildProPCongruent := function(a, b, n)

    if n eq 1 then
        return true;
    end if;

    return ((a-b) mod n) eq 0;

end function;


WildProPAbelianSubgroupFromElements := function(A, S)

    if #S eq 0 then
        return sub< A | Id(A) >;
    end if;

    return sub< A | S >;

end function;


WildProPIsPElement := function(x, p)

    n := Order(x);
    return n eq p^Valuation(n, p);

end function;


WildProPFindCyclotomicElementByCRT := function(C, f, n1, a1, n2, a2)

    for c in C do

        a := WildProPUnitInteger(c, f);

        if WildProPCongruent(a, a1, n1) and
           WildProPCongruent(a, a2, n2) then
            return c;
        end if;

    end for;

    error Sprintf(
        "No cyclotomic unit has residues %o mod %o and %o mod %o.",
        a1, n1, a2, n2
    );

end function;


WildProPHasPreimageInWholeGroup := function(pi, b)

    G := Domain(pi);
    B := Codomain(pi);
    bB := B!b;

    for g in G do
        if pi(g) eq bB then
            return true, g;
        end if;
    end for;

    return false, Id(G);

end function;


WildProPHasPreimageInSubgroup := function(G, P, pi, b)

    B := Codomain(pi);
    bB := B!b;

    for x in P do

        xG := G!x;

        if pi(xG) eq bB then
            return true, xG;
        end if;

    end for;

    return false, Id(G);

end function;


WildProPCommutator := function(x, y)
    return x^(-1) * y^(-1) * x * y;
end function;


WildProPQ2RelatorValue := function(x1, x2, x3)
    return x1^2 * x2^4 * WildProPCommutator(x2, x3);
end function;


/*****************************************************************************************
    Canonical p-primary projection of arithmetic Frobenius.

    Write d=p^e*m with (p,m)=1.  On the m-part arithmetic Frobenius is p.
    Suppose its order is n=p^v*u with (p,u)=1.  Raise it to the CRT idempotent
    E satisfying

        E = 1 mod p^v,
        E = 0 mod u.

    This is the natural p-primary projection of the Frobenius element.  On the
    p^e-part the residue is 1.
*****************************************************************************************/

WildProPArithmeticFrobeniusPPartInC := function(C, f, d, p)

    e := Valuation(d, p);
    ppow := p^e;
    m := d div ppow;

    if m eq 1 then
        return Id(C);
    end if;

    Rm := Integers(m);
    frob := Rm!p;
    n := Order(frob);
    v := Valuation(n, p);

    if v eq 0 then
        return Id(C);
    end if;

    pPowerOrder := p^v;
    primeToP := n div pPowerOrder;

    projectionExponent := primeToP *
        InverseMod(primeToP mod pPowerOrder, pPowerOrder);

    residueM := IntegerRing()!(frob^projectionExponent);

    return WildProPFindCyclotomicElementByCRT(
        C, f,
        ppow, 1,
        m, residueM
    );

end function;


/*****************************************************************************************
    Ramified pro-p cyclotomic generators.
*****************************************************************************************/

WildProPOddPrincipalUnitGeneratorInC := function(C, f, d, p)

    e := Valuation(d, p);
    ppow := p^e;
    m := d div ppow;

    return WildProPFindCyclotomicElementByCRT(
        C, f,
        ppow, 1+p,
        m, 1
    );

end function;


WildProPMinusOneGeneratorInC := function(C, f, d)

    e := Valuation(d, 2);
    twopow := 2^e;
    m := d div twopow;

    return WildProPFindCyclotomicElementByCRT(
        C, f,
        twopow, -1,
        m, 1
    );

end function;


WildProPEtaGeneratorInC := function(C, f, d)

    e := Valuation(d, 2);
    twopow := 2^e;
    m := d div twopow;

    etaResidue := InverseMod((-3) mod twopow, twopow);

    return WildProPFindCyclotomicElementByCRT(
        C, f,
        twopow, etaResidue,
        m, 1
    );

end function;


/*****************************************************************************************
    Prescribed images of standard generators of G_{Q_p}(p).

    Returns:
        labels,
        cImages,
        bImages,
        IwildP,
        Dp,
        sourceDescription.
*****************************************************************************************/

WildProPCyclotomicGeneratorData := function(ebp, p)

    G   := ebp`G;
    C   := ebp`C;
    f   := ebp`f;
    phi := ebp`phi;
    B   := ebp`B;

    if not IsAbelian(B) then
        error "WildProPCyclotomicGeneratorData assumes B is abelian.";
    end if;

    d := ebp`d;

    if d mod p ne 0 then
        error Sprintf("Prime %o does not divide d=%o.", p, d);
    end if;

    cFrob := WildProPArithmeticFrobeniusPPartInC(C, f, d, p);

    if p ne 2 then

        cRam := WildProPOddPrincipalUnitGeneratorInC(C, f, d, p);

        labels := [
            "arithmetic Frobenius, p-primary projection",
            "principal-unit wild inertia generator"
        ];

        cImages := [cFrob, cRam];
        bImages := [phi(c) : c in cImages];

        IwildP := WildProPAbelianSubgroupFromElements(B, [bImages[2]]);
        Dp := WildProPAbelianSubgroupFromElements(B, bImages);
        sourceDescription := "free pro-p group of rank 2";

    else

        /*
            c2=rec(1/2) is inverse arithmetic Frobenius.
            c3=rec(-3) has cyclotomic value eta=(-3)^(-1).
            c1=rec(-4)=rec(-1)*c2^(-2).

            Magma writes C and B additively.
        */

        cMinus := WildProPMinusOneGeneratorInC(C, f, d);
        c2 := -cFrob;
        c3 := WildProPEtaGeneratorInC(C, f, d);
        c1 := cMinus - 2*c2;

        labels := [
            "c1 = rec(-4) = rec(-1)*c2^(-2)",
            "c2 = rec(1/2), inverse arithmetic Frobenius",
            "c3 = rec(-3), cyclotomic value (-3)^(-1)"
        ];

        cImages := [c1, c2, c3];
        bImages := [phi(c) : c in cImages];

        bMinus := phi(cMinus);
        bEta := phi(c3);

        IwildP := WildProPAbelianSubgroupFromElements(B, [bMinus, bEta]);
        Dp := WildProPAbelianSubgroupFromElements(B, bImages);

        if 2*bImages[1] + 4*bImages[2] ne Id(B) then
            error "The extracted Q_2 images do not satisfy 2*b1+4*b2=0.";
        end if;

        sourceDescription :=
            "<c1,c2,c3 | c1^2 c2^4 [c2,c3] = 1>";

    end if;

    for c in cImages do
        if not WildProPIsPElement(c, p) then
            error "Internal error: a local pro-p cyclotomic generator is not a p-element.";
        end if;
    end for;

    for b in bImages do
        if not WildProPIsPElement(b, p) then
            error "Internal error: a local pro-p quotient image is not a p-element.";
        end if;
    end for;

    return labels, cImages, bImages, IwildP, Dp, sourceDescription;

end function;


/*****************************************************************************************
    Wild-prime detection.
*****************************************************************************************/

IsWildlyRamifiedProPAtPrime := function(ebp, p)

    labels, cImages, bImages, IwildP, Dp, sourceDescription :=
        WildProPCyclotomicGeneratorData(ebp, p);

    return #IwildP gt 1;

end function;


WildlyRamifiedPrimesForEbpProP := function(ebp)

    d := ebp`d;
    primes := [];

    for q in Factorization(d) do

        p := q[1];

        if IsWildlyRamifiedProPAtPrime(ebp, p) then
            Append(~primes, p);
        end if;

    end for;

    return primes;

end function;


/*****************************************************************************************
    Construct H=pi^(-1)(Dp).
*****************************************************************************************/

WildProPLocalPreimageGroup := function(ebp, Dp)

    G  := ebp`G;
    B  := ebp`B;
    pi := ebp`pi;
    N  := Kernel(pi);

    gens := [G!n : n in Generators(N)];

    for b in Generators(Dp) do

        ok, g := WildProPHasPreimageInWholeGroup(pi, B!b);

        if not ok then
            error "A generator of Dp has no preimage under pi.";
        end if;

        Append(~gens, G!g);

    end for;

    if #gens eq 0 then
        return sub< G | Id(G) >;
    end if;

    return sub< G | gens >;

end function;


/*****************************************************************************************
    Choose one Sylow p-subgroup P of H and verify pi(P)=Dp.

    Kp=P meet Ker(pi) is the kernel of pi restricted to P.
*****************************************************************************************/

WildProPSylowTargetData := function(ebp, Dp, p)

    G  := ebp`G;
    B  := ebp`B;
    pi := ebp`pi;
    N  := Kernel(pi);

    H := WildProPLocalPreimageGroup(ebp, Dp);
    P := SylowSubgroup(H, p);
    Kp := P meet N;

    imageGens := [pi(G!x) : x in Generators(P)];
    imageP := WildProPAbelianSubgroupFromElements(B, imageGens);

    if (#imageP ne #Dp) or not (imageP subset Dp) then
        error Sprintf(
            "The chosen Sylow %o-subgroup has image order %o, expected %o.",
            p, #imageP, #Dp
        );
    end if;

    return H, P, Kp;

end function;


/*****************************************************************************************
    Fiber of pi|P over b.  It is x0*Kp.
*****************************************************************************************/

WildProPFiberInsideSylow := function(ebp, P, Kp, b)

    G  := ebp`G;
    pi := ebp`pi;

    ok, x0 := WildProPHasPreimageInSubgroup(G, P, pi, b);

    if not ok then
        return false, [];
    end if;

    fiber := [x0*(G!k) : k in Kp];

    return true, fiber;

end function;


/*****************************************************************************************
    Solve the Q_2 relation inside P.

    Instead of a cubic search, precompute all x1^2 in the c1-fiber and use

        x1^2 = (x2^4 [x2,x3])^(-1).

    The remaining search is quadratic in #Kp.
*****************************************************************************************/

WildProPSolveQ2RelationInSylow := function(ebp, P, Kp, b1, b2, b3)

    G := ebp`G;

    ok1, fiber1 := WildProPFiberInsideSylow(ebp, P, Kp, b1);
    ok2, fiber2 := WildProPFiberInsideSylow(ebp, P, Kp, b2);
    ok3, fiber3 := WildProPFiberInsideSylow(ebp, P, Kp, b3);

    if not (ok1 and ok2 and ok3) then
        return false, [], 0;
    end if;

    squareTable := AssociativeArray(G);

    for x1 in fiber1 do
        squareTable[x1^2] := x1;
    end for;

    pairsTested := 0;

    for x2 in fiber2 do

        x2four := x2^4;

        for x3 in fiber3 do

            pairsTested +:= 1;

            rhs := (x2four * WildProPCommutator(x2, x3))^(-1);

            if IsDefined(squareTable, rhs) then

                x1 := squareTable[rhs];

                if WildProPQ2RelatorValue(x1, x2, x3) eq Id(G) then
                    return true, [x1, x2, x3], pairsTested;
                end if;

            end if;

        end for;

    end for;

    return false, [], pairsTested;

end function;


/*****************************************************************************************
    Detailed test at one prime.
*****************************************************************************************/

DetailedWildProPReportAtPrime := function(ebp, p)

    G := ebp`G;

    labels, cImages, bImages, IwildP, Dp, sourceDescription :=
        WildProPCyclotomicGeneratorData(ebp, p);

    isWild := #IwildP gt 1;

    if not isWild then

        return rec< WildProPPrimeReportFormat |
            p                    := p,
            is_wild              := false,
            source_description   := sourceDescription,
            generator_labels     := labels,
            C_generator_images   := cImages,
            B_generator_images   := bImages,
            wild_inertia_order   := #IwildP,
            Dp_order             := #Dp,
            local_preimage_order := 0,
            sylow_order          := 0,
            sylow_kernel_order   := 0,
            pairs_tested         := 0,
            liftable             := false,
            message              := "Wild inertia image is trivial; this prime is not tested as wild.",
            witness              := []
        >;

    end if;

    H, P, Kp := WildProPSylowTargetData(ebp, Dp, p);

    if p ne 2 then

        ok1, x1 := WildProPHasPreimageInSubgroup(G, P, ebp`pi, bImages[1]);
        ok2, x2 := WildProPHasPreimageInSubgroup(G, P, ebp`pi, bImages[2]);

        if not (ok1 and ok2) then

            return rec< WildProPPrimeReportFormat |
                p                    := p,
                is_wild              := true,
                source_description   := sourceDescription,
                generator_labels     := labels,
                C_generator_images   := cImages,
                B_generator_images   := bImages,
                wild_inertia_order   := #IwildP,
                Dp_order             := #Dp,
                local_preimage_order := #H,
                sylow_order          := #P,
                sylow_kernel_order   := #Kp,
                pairs_tested         := 0,
                liftable             := false,
                message              := "Internal failure: a prescribed image has no lift in P.",
                witness              := []
            >;

        end if;

        return rec< WildProPPrimeReportFormat |
            p                    := p,
            is_wild              := true,
            source_description   := sourceDescription,
            generator_labels     := labels,
            C_generator_images   := cImages,
            B_generator_images   := bImages,
            wild_inertia_order   := #IwildP,
            Dp_order             := #Dp,
            local_preimage_order := #H,
            sylow_order          := #P,
            sylow_kernel_order   := #Kp,
            pairs_tested         := 0,
            liftable             := true,
            message              := "Liftable: the odd-p source is free pro-p of rank 2.",
            witness              := [x1, x2]
        >;

    end if;

    ok, witness, pairsTested := WildProPSolveQ2RelationInSylow(
        ebp, P, Kp,
        bImages[1], bImages[2], bImages[3]
    );

    if ok then

        return rec< WildProPPrimeReportFormat |
            p                    := p,
            is_wild              := true,
            source_description   := sourceDescription,
            generator_labels     := labels,
            C_generator_images   := cImages,
            B_generator_images   := bImages,
            wild_inertia_order   := #IwildP,
            Dp_order             := #Dp,
            local_preimage_order := #H,
            sylow_order          := #P,
            sylow_kernel_order   := #Kp,
            pairs_tested         := pairsTested,
            liftable             := true,
            message              := "Liftable: a triple satisfies c1^2*c2^4*[c2,c3]=1 in P.",
            witness              := witness
        >;

    end if;

    return rec< WildProPPrimeReportFormat |
        p                    := p,
        is_wild              := true,
        source_description   := sourceDescription,
        generator_labels     := labels,
        C_generator_images   := cImages,
        B_generator_images   := bImages,
        wild_inertia_order   := #IwildP,
        Dp_order             := #Dp,
        local_preimage_order := #H,
        sylow_order          := #P,
        sylow_kernel_order   := #Kp,
        pairs_tested         := pairsTested,
        liftable             := false,
        message              := "Not liftable in the pro-2 quotient: no prescribed triple satisfies the relator.",
        witness              := []
    >;

end function;


/*****************************************************************************************
    Primitive interface parallel to the tame test.
*****************************************************************************************/

IsCyclotomicWildProPLocallyLiftableAtPrime := function(ebp, p)

    R := DetailedWildProPReportAtPrime(ebp, p);
    return R`liftable, R`message, R`witness;

end function;


/*****************************************************************************************
    Test all wildly ramified finite places, only in maximal pro-p quotients.
*****************************************************************************************/

IsLocallyLiftableAtAllWildProPPlaces := function(ebp)

    primes := WildlyRamifiedPrimesForEbpProP(ebp);
    reports := [];

    for p in primes do

        R := DetailedWildProPReportAtPrime(ebp, p);
        Append(~reports, R);

        if not R`liftable then
            return false, reports;
        end if;

    end for;

    return true, reports;

end function;


/*****************************************************************************************
    Combined tame + wild-pro-p + real test.

    TameLocalLiftability.m (the uploaded tamechecking.txt) must already be loaded.
*****************************************************************************************/

IsLocallyLiftableTameWildProPAndReal := function(ebp)

    okTame, tameReports := IsLocallyLiftableAtAllTameFinitePlaces(ebp);
    okWild, wildReports := IsLocallyLiftableAtAllWildProPPlaces(ebp);
    okReal, realMsg, realWitness := IsRealLocallyLiftable(ebp);

    return okTame and okWild and okReal,
           tameReports,
           wildReports,
           <okReal, realMsg>;

end function;


/*****************************************************************************************
    Compact reports.
*****************************************************************************************/

CleanWildProPLiftabilityReport := function(ebp)

    reports := [];

    for p in WildlyRamifiedPrimesForEbpProP(ebp) do

        R := DetailedWildProPReportAtPrime(ebp, p);

        if R`liftable then
            Append(~reports, <"wild-pro-p", p, "liftable">);
        else
            Append(~reports, <"wild-pro-p", p, "not liftable">);
        end if;

    end for;

    return reports;

end function;


CleanLocalLiftabilityReportWithWildProP := function(ebp)

    reports := [];

    for p in TamelyRamifiedPrimesForEbp(ebp) do

        ok, msg, wit := IsCyclotomicTameLocallyLiftableAtPrime(ebp, p);

        if ok then
            Append(~reports, <"tame", p, "liftable">);
        else
            Append(~reports, <"tame", p, "not liftable">);
        end if;

    end for;

    reports cat:= CleanWildProPLiftabilityReport(ebp);

    okReal, realMsg, realWitness := IsRealLocallyLiftable(ebp);

    if okReal then
        Append(~reports, <"real", 0, "liftable">);
    else
        Append(~reports, <"real", 0, "not liftable">);
    end if;

    return reports;

end function;


/*****************************************************************************************
    Printers.
*****************************************************************************************/

PrintDetailedWildProPPrimeReport := procedure(ebp, R)

    print "============================================================";
    print "Wild local pro-p report at p =", R`p;
    print "is wildly ramified in B?      =", R`is_wild;
    print "source                        =", R`source_description;
    print "# wild inertia image          =", R`wild_inertia_order;
    print "# Dp (local pro-p image)      =", R`Dp_order;
    print "# pi^(-1)(Dp)                 =", R`local_preimage_order;
    print "# chosen Sylow p-subgroup     =", R`sylow_order;
    print "# Sylow kernel                =", R`sylow_kernel_order;
    print "pairs tested                  =", R`pairs_tested;

    print "Prescribed generator images:";

    for i := 1 to #R`generator_labels do
        print "  label   =", R`generator_labels[i];
        print "  C-unit  =", WildProPUnitInteger(R`C_generator_images[i], ebp`f);
        print "  B-image =", R`B_generator_images[i];
    end for;

    print "liftable                      =", R`liftable;
    print "message                       =", R`message;

    if R`liftable then
        print "witness                       =", R`witness;
    end if;

    print "============================================================";

end procedure;


PrintWildProPReportForEbp := procedure(ebp)

    primes := WildlyRamifiedPrimesForEbpProP(ebp);

    if #primes eq 0 then
        print "No wildly ramified finite primes in the pro-p cyclotomic quotient.";
        return;
    end if;

    for p in primes do
        R := DetailedWildProPReportAtPrime(ebp, p);
        PrintDetailedWildProPPrimeReport(ebp, R);
    end for;

end procedure;


/*****************************************************************************************
    Entry point used by lib/<ordering>/fullcheck.m.

    This is a NECESSARY condition only: it can reject a pair, never certify one.
    It must therefore feed BWupperLocal and nothing else.  Wiring it into the
    lower bound would be unsound -- see the scope warning in
    magma/lib/WildProP_README.md.
*****************************************************************************************/

PassesCheckedLocalTestsWithWild := function(ebp)
    ok := IsLocallyLiftableTameWildProPAndReal(ebp);
    return ok;
end function;
