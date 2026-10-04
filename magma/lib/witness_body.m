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
//
// QUOTIENT / ALTERNATE-REPRESENTATION WITNESSES.  When a polynomial does not
// realise the target nTk permutation representation directly, it is treated as
// a witness for a QUOTIENT G/M, including M = 1.  Thus a field with the same
// ABSTRACT Galois group in a different transitive representation can still be
// a full witness for nTk.  For M > 1, M must be peelable by a chain of
// admissible split-tower layers (nilpotent and complemented, odd with the
// mu(K) condition and complemented, or GAR), each taken in the quotient by
// the previous ones.  Any proper
// G/M-solution then lifts to a proper G-solution (see split_tower.m), and if
// moreover M <= [G,G], every abelian subextension of the lift already lies in
// the G/M-field, so the intersection with Q(mu_d) is unchanged and the pair is
// still witnessed with exact intersection.  M with M not inside [G,G] are
// skipped for that reason.  See VerifyResidualWitness below.

WitnessStrip := function(s)
    out := "";
    for k := 1 to #s do
        ch := s[k];
        if ch ne " " and ch ne "\t" and ch ne "\r" then out cat:= ch; end if;
    end for;
    return out;
end function;

// Parse the coefficient-vector syntax accepted by witnesses.txt.  Keep this
// deliberately tiny: witness files are data, not executable Magma input.
WitnessParseCoeffs := function(s)
    t := WitnessStrip(s);
    if #t lt 2 or t[1] ne "[" or t[#t] ne "]" then
        error "polynomial coefficients must have the form [c0,c1,...,cn]";
    end if;
    if #t eq 2 then return []; end if;
    body := Substring(t, 2, #t - 2);
    pieces := Split(body, ",");
    if #pieces eq 0 then return []; end if;
    coeffs := [];
    for u in pieces do
        if #u eq 0 then error "empty polynomial coefficient"; end if;
        Append(~coeffs, StringToInteger(u));
    end for;
    return coeffs;
end function;

// Canonical representation written to verified_*.txt.  run_parallel.py uses
// this to detect a stale verification file after witnesses.txt is edited.
WitnessCoeffString := function(coeffs)
    out := "[";
    for i := 1 to #coeffs do
        if i gt 1 then out cat:= ","; end if;
        out cat:= Sprint(Integers() ! coeffs[i]);
    end for;
    return out cat "]";
end function;

// GaloisGroup(f) may use conditional steps.  A witness is intended to be a
// rigorous arithmetic certificate, so insist that Magma proves those steps.
WitnessProvenGaloisGroup := function(f)
    G, roots, S := GaloisGroup(f);
    if not GaloisProof(f, S) then
        error "Magma could not prove the computed Galois group (GaloisProof failed)";
    end if;
    return G, roots, S;
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

// Verify one full witness after its proven Galois group has already been
// computed.  This fast path is used when the polynomial realises exactly the
// target transitive representation.  Returns
//   b       lower bound for b_W proven by this field
//   identification_exact  true if every surviving identification gives the same b
//   bM, bT  recomputed from the field's own Galois group
//   nsurv   number of surviving pairs
//   msg     a short description
VerifyWitnessDirectCore := function(label, f, G, S : MaxPrimes := 300)
    parts := Split(label, "T");
    if #parts ne 2 then error "bad label " cat label; end if;
    n := StringToInteger(parts[1]);
    k := StringToInteger(parts[2]);

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
    while #surv gt 1 and #{ x[3] : x in surv } gt 1 and tested lt MaxPrimes do
        l := NextPrime(l);
        if d mod l eq 0 or disc mod l eq 0 or lc mod l eq 0 then continue; end if;
        tested +:= 1;
        T := WitnessFrobeniusCycleType(f, l);
        idx := [ i : i in [1..#cls] | types[i] eq T ];
        if #idx eq 0 then
            error Sprintf("no class of G has the cycle type of f mod %o -- bug", l);
        end if;
        surv := [ x : x in surv |
                  x[2]`phi((Integers(d) ! l) @@ x[2]`f)
                      in { x[2]`pi(cls[i][3]) : i in idx } ];
    end while;
    if #surv eq 0 then
        error "no pair is consistent with the Frobenius data -- convention bug?";
    end if;

    bvals := { x[3] : x in surv };
    return Min(bvals), #bvals eq 1, bM, bT, #surv,
           Sprintf("[F:Q] = %o, %o of %o identifications survive %o primes",
                   Index(G, N0), #surv, #cands, tested);
end function;

// Historical direct API, kept for tests and interactive use.
VerifyWitness := function(label, coeffs : MaxPrimes := 300)
    parts := Split(label, "T");
    if #parts ne 2 then error "bad label " cat label; end if;
    n := StringToInteger(parts[1]);

    f := Polynomial(Integers(), coeffs);
    if Degree(f) ne n then
        error Sprintf("polynomial has degree %o, label says %o", Degree(f), n);
    end if;
    if not IsIrreducible(f) then error "polynomial is reducible"; end if;

    G, _, S := WitnessProvenGaloisGroup(f);
    return VerifyWitnessDirectCore(label, f, G, S : MaxPrimes := MaxPrimes);
end function;

// ---------------------------------------------------------------------
// Quotient / alternate-representation witnesses
// ---------------------------------------------------------------------

// All automorphisms of Gam, by closure over the generators of
// AutomorphismGroup(Gam).  Elements are GrpAutoElt, applied as a(x).
WitnessAutList := function(Gam : Cap := 20000)
    A := AutomorphismGroup(Gam);
    gg := [ Gam.i : i in [1..Ngens(Gam)] ];
    key := func< a | [ a(x) : x in gg ] >;
    gensA := [ A.i : i in [1..Ngens(A)] ];
    e := Id(A);
    seen := { key(e) };
    list := [ e ];
    frontier := [ e ];
    while #frontier gt 0 do
        new := [];
        for a in frontier do
            for g in gensA do
                b := a * g;
                k := key(b);
                if not (k in seen) then
                    Include(~seen, k);
                    Append(~list, b);
                    Append(~new, b);
                    if #list gt Cap then
                        error Sprintf("more than %o automorphisms; raise Cap", Cap);
                    end if;
                end if;
            end for;
        end for;
        frontier := new;
    end while;
    return list;
end function;

// alpha = iso . aut : Gam -> Gam -> G/M.  A plain function rather than a
// func<> closure, so that nothing depends on how loop variables are captured.
WitnessAlpha := function(iso, aut, x)
    return iso(aut(x));
end function;

// One admissible split-tower layer: L normal in G, and a GAR layer, or
// complemented and nilpotent [NSW 9.6.10], or complemented of odd order with
// the mu(K) condition [NSW 9.5.8] -- exactly the layers split_tower.m peels.
WitnessSingleLayer := function(G, L)
    if IsGARLayer(L) then return true, Sprintf("GAR(%o)", #L); end if;
    if LayerAllowed(G, L) and IsSplitKernel(G, L) then
        return true, Sprintf(IsNilpotent(L) select "nilp(%o)" else "odd(%o)", #L);
    end if;
    return false, "";
end function;

// Is there a chain 1 = M_0 < M_1 < ... < M_r = M of normal subgroups of G
// such that each M_i / M_(i-1) is an admissible layer of G / M_(i-1)?  Then
// a proper G/M-solution climbs back to a proper G-solution one layer at a
// time, exactly as in the split tower.
//
// The search is phrased in the ORIGINAL group, with K the cumulative subgroup
// already peeled off.  As in split_tower.m, the memo stores the largest
// remaining depth at which a K has been expanded, so reaching K later by a
// shorter chain can still expose a witness tower.  The third return value says
// whether a negative answer was exhaustive (true) or hit the depth limit
// (false).
WitnessTowerReachesFrom := function(G0, Mtarget, K, depth, seen)
    if K eq Mtarget then return true, "", seen, true; end if;
    if depth le 0 then return false, "", seen, false; end if;

    if #K eq 1 then
        GK := G0;
        qK := IdentityHomomorphism(G0);
        targetK := Mtarget;
    else
        GK, qK := quo< G0 | K >;
        targetK := Mtarget @ qK;
    end if;

    Ls := [ R`subgroup : R in NormalSubgroups(GK)
            | #R`subgroup gt 1 and R`subgroup subset targetK ];
    Sort(~Ls, func< X, Y | #Y - #X >);

    complete := true;
    anyAdmissible := false;
    for L in Ls do
        ok, why := WitnessSingleLayer(GK, L);
        if not ok then continue; end if;
        anyAdmissible := true;

        K1 := L @@ qK;
        if K1 eq Mtarget then return true, why, seen, true; end if;

        nextDepth := depth - 1;
        if TowerSeenDepth(seen, K1) ge nextDepth then continue; end if;
        seen := TowerRecordDepth(seen, K1, nextDepth);
        ok2, why2, seen, childComplete := $$(
            G0, Mtarget, K1, nextDepth, seen
        );
        if ok2 then return true, why cat ", " cat why2, seen, true; end if;
        if not childComplete then complete := false; end if;
    end for;

    if not anyAdmissible then return false, "", seen, true; end if;
    return false, "", seen, complete;
end function;

WitnessTowerReaches := function(G, M : Depth := 16)
    triv := sub< G | Id(G) >;
    ok, why, seen, complete := WitnessTowerReachesFrom(
        G, M, triv, Depth, [* <triv, Depth> *]
    );
    return ok, why, complete;
end function;

// May a proper G/M-solution be lifted to a proper G-solution with the same
// intersection with Q(mu_d)?  M must be reachable by admissible tower
// layers, and M <= [G,G].
WitnessQuotientKernelOK := function(G, M)
    if #M eq 1 then return true, "M = 1"; end if;
    if not (M subset DerivedSubgroup(G)) then
        return false, "M is not inside [G,G]: the lift could meet Q(mu_d) in more than F";
    end if;
    ok, why, complete := WitnessTowerReaches(G, M);
    if ok then return true, "tower layers " cat why; end if;
    if complete then
        return false, "not reachable by admissible tower layers";
    end if;
    return false, "not found by the depth-limited admissible tower search";
end function;

// Verify a quotient witness: f defines a field whose Galois group Gam is a
// quotient G/M of G = TransitiveGroup(n, k), with M = 1 allowed.  Same
// returns as VerifyWitness.
//
// Every isomorphism alpha : Gam -> G/M gives a genuine proper G/M-solution
// rho_alpha, so each alpha (and each admissible M) proves its own bound; the
// result is the maximum over them.  For a fixed alpha the realised kernel is
// N = q^-1(alpha(N0)), and phi is narrowed with Frobenius cycle types in Gam,
// transported by alpha, exactly as in VerifyWitness; the bound for that alpha
// is the minimum of b over the survivors.
VerifyQuotientWitnessCore := function(label, f, Gam, S : MaxPrimes := 300)
    parts := Split(label, "T");
    if #parts ne 2 then error "bad label " cat label; end if;
    n := StringToInteger(parts[1]);
    k := StringToInteger(parts[2]);
    G := TransitiveGroup(n, k);

    if #G mod #Gam ne 0 then
        error Sprintf("Galois group has order %o, which does not divide #G = %o", #Gam, #G);
    end if;

    d, a, nS, nP, bM, bT, ev := EvaluatePairs(G);
    N0g, res := WitnessCyclotomicPart(Gam, S, d);

    // Do NOT return early when F = Q.  We must first prove that Gal(f) really
    // occurs as an admissible quotient G/M; otherwise an unrelated group of
    // order dividing #G could be (incorrectly) accepted as a residual witness.

    // Frobenius data in Gam, collected once.
    clsG := Classes(Gam);
    types := [ WitnessCycleType(c[3]) : c in clsG ];
    disc := Discriminant(f);
    lc := LeadingCoefficient(f);
    frob := [];
    l := 2;
    while #frob lt MaxPrimes do
        l := NextPrime(l);
        if d mod l eq 0 or disc mod l eq 0 or lc mod l eq 0 then continue; end if;
        T := WitnessFrobeniusCycleType(f, l);
        idx := [ i : i in [1..#clsG] | types[i] eq T ];
        if #idx eq 0 then
            error Sprintf("no class of Gal(f) has the cycle type of f mod %o -- bug", l);
        end if;
        Append(~frob, < l, idx >);
    end while;

    best := -1; bestExact := true; bestSurv := 0; bestWhy := "";
    tried := 0;
    for R in NormalSubgroups(G) do
        M := R`subgroup;
        if #M * #Gam ne #G then continue; end if;
        ok, whyM := WitnessQuotientKernelOK(G, M);
        if not ok then continue; end if;
        Q, q := quo< G | M >;
        isIso, iso := IsIsomorphic(Gam, Q);
        if not isIso then continue; end if;
        tried +:= 1;

        for aut in WitnessAutList(Gam) do
            N := sub< Q | [ WitnessAlpha(iso, aut, x) : x in Generators(N0g) ] > @@ q;
            cands := [ item : item in ev |
                       Kernel(item[2]`pi) eq N and KernelResidues(item[2], d) eq res ];
            if #cands eq 0 then continue; end if;   // kernel has no minimal element

            surv := cands;
            for fr in frob do
                if #surv le 1 or #{ s[3] : s in surv } le 1 then break; end if;
                l := fr[1];
                surv := [ s : s in surv |
                          s[2]`phi((Integers(d) ! l) @@ s[2]`f)
                              in { s[2]`pi(WitnessAlpha(iso, aut, clsG[i][3]) @@ q)
                                   : i in fr[2] } ];
            end for;
            if #surv eq 0 then
                error "no pair is consistent with the Frobenius data -- convention bug?";
            end if;
            bvals := { s[3] : s in surv };
            if Min(bvals) gt best then
                best := Min(bvals);
                bestExact := #bvals eq 1;
                bestSurv := #surv;
                bestWhy := Sprintf("via G/M with #M = %o (%o), [F:Q] = %o",
                                   #M, whyM, Index(Gam, N0g));
            end if;
        end for;
    end for;

    if tried eq 0 then
        error Sprintf("no admissible normal M of %o with G/M isomorphic to Gal(f) (order %o)",
                      label, #Gam);
    end if;
    if best lt 0 then
        return 0, true, bM, bT, 0, "every realised kernel misses the minimal elements";
    end if;
    return best, bestExact, bM, bT, bestSurv, "residual witness " cat bestWhy;

end function;

// Historical residual API, kept for tests and interactive use.
VerifyResidualWitness := function(label, coeffs : MaxPrimes := 300)
    f := Polynomial(Integers(), coeffs);
    if not IsIrreducible(f) then error "polynomial is reducible"; end if;
    Gam, _, S := WitnessProvenGaloisGroup(f);
    return VerifyQuotientWitnessCore(label, f, Gam, S : MaxPrimes := MaxPrimes);
end function;

// Unified production verifier.  A full witness is just the M = 1 case of a
// quotient witness, but the direct path is much faster when the polynomial
// already realises the target nTk permutation representation.  Otherwise we
// fall back to the abstract quotient search, EVEN WHEN Degree(f) = n.  This
// lets a field for a different transitive representation of the same abstract
// group witness the target representation as well.
VerifyAnyWitness := function(label, coeffs : MaxPrimes := 300)
    parts := Split(label, "T");
    if #parts ne 2 then error "bad label " cat label; end if;
    n := StringToInteger(parts[1]);
    k := StringToInteger(parts[2]);

    f := Polynomial(Integers(), coeffs);
    if not IsIrreducible(f) then error "polynomial is reducible"; end if;
    Gam, _, S := WitnessProvenGaloisGroup(f);

    sameRep := false;
    if Degree(f) eq n then
        try
            k1, n1 := TransitiveGroupIdentification(Gam);
            sameRep := n1 eq n and k1 eq k;
        catch err
            // If this permutation representation has no transitive-library
            // identification, the abstract quotient path below is still valid.
            sameRep := false;
        end try;
    end if;
    if sameRep then
        // Do not put the direct verification itself inside the try/catch: a
        // genuine arithmetic/programming error there must be reported, not
        // silently converted into an abstract-quotient fallback.
        return VerifyWitnessDirectCore(label, f, Gam, S : MaxPrimes := MaxPrimes);
    end if;

    return VerifyQuotientWitnessCore(label, f, Gam, S : MaxPrimes := MaxPrimes);
end function;

// Process a witness file.  VerifyAnyWitness chooses the direct fast path or
// the abstract quotient/M=1 path automatically; polynomial degree is not used
// as a correctness criterion.  orderingName is "disc" or "prp"; rows marked
// "both" are processed by either.
VerifyWitnessFile := procedure(infile, outfile, orderingName : MaxPrimes := 300)
    Write(outfile, "label|b_witness|identification_exact|b_M|b_T|survivors|source|poly"
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
            coeffs := WitnessParseCoeffs(fields[3]);
            b, exact, bM, bT, nsurv, why := VerifyAnyWitness(
                label, coeffs : MaxPrimes := MaxPrimes
            );
        catch err
            failed := true;
            msg := CleanForField(Sprint(err`Object));
        end try;

        if failed then
            Write(outfile, Sprintf("%o|ERROR|%o", label, msg));
            printf "  %o: ERROR %o\n", label, msg;
            continue;
        end if;
        Write(outfile, Sprintf("%o|%o|%o|%o|%o|%o|%o|%o", label, b,
                               exact select 1 else 0, bM, bT, nsurv, source,
                               WitnessCoeffString(coeffs)));
        printf "  %o (%o): b_witness = %o%o, b_M = %o, b_T = %o; %o\n",
               label, source, b, exact select "" else " (conservative)",
               bM, bT, why;
    end for;
end procedure;
