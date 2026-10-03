// =====================================================================
// witness_body.m  --  verify witness fields for lower bounds on b_W
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering
// (for EvaluatePairs), and certificates/shared.m (for KernelResidues).
// Load this LAST, exactly like driver.m.  See data/witnesses/README.md.
//
// A witness is a polynomial f whose splitting field K~ has Galois group G.
// Let F = K~ cap Q(mu_d) and N0 = Gal(K~/F).  Then K~ is a proper solution,
// WITH EXACT INTERSECTION, of the pair (pi, phi) with Ker(pi) = N0 and phi
// cutting out F.  So b_W >= b(pi, phi), unconditionally on the certificates.
//
// Everything is computed on the Galois group G that GaloisGroup returns, as
// a permutation group on the roots of f.  It is conjugate in S_n to
// TransitiveGroup(n, k), and b(pi, phi) is invariant under that conjugation
// (cycle types are preserved), so nothing needs transporting.
//
// IDENTIFYING phi.  F, hence N0 and the residues fixing F, is determined
// exactly.  The identification Gal(F/Q) = G/N0 is narrowed with Frobenius
// cycle types: for a prime l not dividing d * disc(f), phi(l mod d) must lie
// in pi(c) for some class c of G whose cycle type is the factorisation
// pattern of f mod l.  The true pair always passes, so eliminating pairs that
// fail is sound.  Cycle types do not distinguish g from g^-1, so phi and
// (inversion on B) . phi always survive together; the reported bound is the
// minimum of b over the survivors, which is valid whichever one is true.

WitnessStrip := function(s)
    out := "";
    for k := 1 to #s do
        ch := s[k];
        if ch ne " " and ch ne "\t" and ch ne "\r" then out cat:= ch; end if;
    end for;
    return out;
end function;

// Cycle type of a permutation, as a sorted sequence of cycle lengths
// including fixed points.
WitnessCycleType := function(g)
    n := Degree(Parent(g));
    ct := [];
    for c in CycleStructure(g) do
        ct cat:= [ c[1] : j in [1..c[2]] ];
    end for;
    pad := n - &+([0] cat ct);          // in case fixed points are omitted
    ct cat:= [ 1 : j in [1..pad] ];
    return Sort(ct);
end function;

// Factorisation pattern of f mod l, l not dividing disc(f) * lc(f).  This is
// the cycle type of Frobenius at l acting on the roots of f.
WitnessFrobeniusCycleType := function(f, l)
    fl := PolynomialRing(GF(l)) ! f;
    ct := [];
    for t in Factorization(fl) do
        ct cat:= [ Degree(t[1]) : j in [1..t[2]] ];
    end for;
    return Sort(ct);
end function;

// Number field from a GaloisSubgroup polynomial, made monic over Q.
WitnessFieldFromPoly := function(g)
    gQ := PolynomialRing(Rationals()) ! g;
    gQ := gQ / LeadingCoefficient(gQ);
    return NumberField(gQ);
end function;

// Returns N0 = Gal(K~/F) for F = K~ cap Q(mu_d), and the set of residues
// u mod d with sigma_u trivial on F.
//
// F is the compositum of the fields K~^N, N normal containing [G,G], that
// lie in Q(mu_d), so N0 is the intersection of those N.  Only N with G/N a
// possible quotient of (Z/dZ)^* need testing: #(G/N) divides #C and
// Exp(G/N) divides Exp(C).
WitnessCyclotomicPart := function(G, S, d)
    units := [ u : u in [1..d-1] | Gcd(u, d) eq 1 ];
    if #units le 1 then
        return G, Set(units);                       // Q(mu_d) = Q
    end if;

    Kd := NumberField(CyclotomicPolynomial(d));     // Kd.1 = zeta_d
    C := MultiplicativeGroup(Integers(d));
    nC := #C;
    eC := Exponent(C);

    AbG, q := AbelianQuotient(G);
    try
        subs := Subgroups(AbG : IndexLimit := nC);
    catch err
        subs := Subgroups(AbG);
    end try;

    N0 := G;
    for R in subs do
        Sb := R`subgroup;
        m := #AbG div #Sb;
        if m eq 1 or nC mod m ne 0 then continue; end if;
        if eC mod Exponent(quo< AbG | Sb >) ne 0 then continue; end if;
        N := Sb @@ q;
        if N0 subset N then continue; end if;       // K~^N already inside F
        g := GaloisSubgroup(S, N);
        if Degree(g) ne m or not IsIrreducible(g) then
            error Sprintf("GaloisSubgroup returned a polynomial of degree %o "
                          cat "(irreducible: %o) for a subgroup of index %o",
                          Degree(g), IsIrreducible(g), m);
        end if;
        if IsSubfield(WitnessFieldFromPoly(g), Kd) then
            N0 := N0 meet N;
        end if;
    end for;

    if N0 eq G then
        return G, Set(units);
    end if;

    m0 := Index(G, N0);
    g0 := GaloisSubgroup(S, N0);
    F0 := WitnessFieldFromPoly(g0);
    ok, emb := IsSubfield(F0, Kd);
    if not ok then
        error "compositum of cyclotomic subfields is not cyclotomic -- bug";
    end if;
    alpha := emb(F0.1);
    c := Eltseq(alpha);
    z := Kd.1;
    res := { u : u in units |
             &+[ c[i] * z^(u*(i-1)) : i in [1..#c] ] eq alpha };
    if #res * m0 ne #units then
        error Sprintf("residues fixing F: found %o, expected phi(d)/[F:Q] = %o",
                      #res, #units div m0);
    end if;
    return N0, res;
end function;

// Verify one witness.  Returns
//   b       lower bound for b_W proven by this field
//   exact   true if every surviving identification gives the same b
//   bM, bT  recomputed from the field's own Galois group
//   nsurv   number of surviving pairs
//   msg     a short description
VerifyWitness := function(label, coeffs : MaxPrimes := 300)
    parts := Split(label, "T");
    if #parts ne 2 then error "bad label " cat label; end if;
    n := StringToInteger(parts[1]);
    k := StringToInteger(parts[2]);

    f := Polynomial(Integers(), coeffs);
    if Degree(f) ne n then
        error Sprintf("polynomial has degree %o, label says %o", Degree(f), n);
    end if;
    if not IsIrreducible(f) then error "polynomial is reducible"; end if;

    // Magma's GaloisGroup over Q is proven by default; if your version
    // needs a parameter for that, this is the one line to change.
    G, _, S := GaloisGroup(f);
    k1, n1 := TransitiveGroupIdentification(G);
    if n1 ne n or k1 ne k then
        error Sprintf("Galois group is %oT%o, not %o", n1, k1, label);
    end if;

    d, a, nS, nP, bM, bT, ev := EvaluatePairs(G);
    N0, res := WitnessCyclotomicPart(G, S, d);

    if N0 eq G then
        return bM, true, bM, bT, 1,
               Sprintf("K~ cap Q(mu_%o) = Q: witnesses only the trivial pair", d);
    end if;

    cands := [ item : item in ev |
               Kernel(item[2]`pi) eq N0 and KernelResidues(item[2], d) eq res ];
    if #cands eq 0 then
        // Phase 1 drops pairs whose kernel has no element of minimal
        // exponent: such fields are counted with a smaller power of X.
        return 0, true, bM, bT, 0,
               Sprintf("[F:Q] = %o, but Ker(pi) has no minimal element", Index(G, N0));
    end if;

    cls := Classes(G);
    types := [ WitnessCycleType(c[3]) : c in cls ];
    disc := Discriminant(f);
    lc := LeadingCoefficient(f);
    surv := cands;
    l := 2;
    tested := 0;
    while #surv gt 1 and #{ s[3] : s in surv } gt 1 and tested lt MaxPrimes do
        l := NextPrime(l);
        if d mod l eq 0 or disc mod l eq 0 or lc mod l eq 0 then continue; end if;
        tested +:= 1;
        T := WitnessFrobeniusCycleType(f, l);
        idx := [ i : i in [1..#cls] | types[i] eq T ];
        if #idx eq 0 then
            error Sprintf("no class of G has the cycle type of f mod %o -- bug", l);
        end if;
        surv := [ s : s in surv |
                  s[2]`phi((Integers(d) ! l) @@ s[2]`f)
                      in { s[2]`pi(cls[i][3]) : i in idx } ];
    end while;
    if #surv eq 0 then
        error "no pair is consistent with the Frobenius data -- convention bug?";
    end if;

    bvals := { s[3] : s in surv };
    return Min(bvals), #bvals eq 1, bM, bT, #surv,
           Sprintf("[F:Q] = %o, %o of %o identifications survive %o primes",
                   Index(G, N0), #surv, #cands, tested);
end function;

// Process a witness file.  orderingName is "disc" or "prp"; rows marked
// "both" are processed by either.
VerifyWitnessFile := procedure(infile, outfile, orderingName : MaxPrimes := 300)
    Write(outfile, "label|b_witness|exact|b_M|b_T|survivors|source"
          : Overwrite := true);
    lines := Split(Read(infile), "\n");
    for ln in lines do
        s := WitnessStrip(ln);
        if #s eq 0 or s[1] eq "#" or (#s ge 6 and Substring(s, 1, 6) eq "label|") then
            continue;
        end if;
        fields := Split(ln, "|");
        if #fields lt 4 then
            printf "  skipping malformed line: %o\n", ln;
            continue;
        end if;
        label := WitnessStrip(fields[1]);
        ord   := WitnessStrip(fields[2]);
        if ord ne "both" and ord ne orderingName then continue; end if;
        source := WitnessStrip(fields[4]);

        failed := false;
        msg := "";
        try
            coeffs := [ Integers() ! c : c in eval WitnessStrip(fields[3]) ];
            b, exact, bM, bT, nsurv, why := VerifyWitness(label, coeffs
                                                          : MaxPrimes := MaxPrimes);
        catch err
            failed := true;
            msg := CleanForField(Sprint(err`Object));
        end try;

        if failed then
            Write(outfile, Sprintf("%o|ERROR|%o", label, msg));
            printf "  %o: ERROR %o\n", label, msg;
            continue;
        end if;
        Write(outfile, Sprintf("%o|%o|%o|%o|%o|%o|%o", label, b,
                               exact select 1 else 0, bM, bT, nsurv, source));
        printf "  %o (%o): b_witness = %o%o, b_M = %o, b_T = %o; %o\n",
               label, source, b, exact select "" else " (conservative)",
               bM, bT, why;
    end for;
end procedure;
