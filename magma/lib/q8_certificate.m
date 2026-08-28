// =====================================================================
// Residual Q8 embedding problems, decided by Witt's criterion
// =====================================================================
//
// Requires (load first): records.m, splitting.m, split_tower.m
//
// After MaximalSplitReduction a great many pairs bottom out at a residual
// problem whose group is Q8.  There are exactly two shapes, and both are
// classical:
//
//   (a)  1 -> C_2 -> Q8 -> C2 x C2 -> 1,  phi cuts out F = Q(sqrt a, sqrt b)
//   (b)  1 -> C_4 -> Q8 -> C_2      -> 1,  phi cuts out F = Q(sqrt a)
//
// WITT (1936).  Q(sqrt a, sqrt b) embeds in a Q8-extension of Q iff the
// quadratic forms <a, b, ab> and <1, 1, 1> are equivalent over Q; that is,
// a, b, ab all positive and (a,b)(a,ab)(b,ab) = 1 at every place.
//
// Case (a) is Witt read off directly.  Solvable => properly solvable here for
// free: every proper subgroup of Q8 is cyclic, so its image in C2 x C2 has
// order at most 2 and cannot be onto.
//
// Case (b) needs a search: we need SOME Q8-extension having Q(sqrt a) as one
// of its three quadratic subfields, i.e. some b with Witt(a,b).  Expanding
// the Hasse invariants, Witt(a,b) with a,b>0 is equivalent to
//
//              (b, -a) = (a, -1)   in Br(Q)[2],
//
// and the algebras of the form (b,-a) are exactly those split by Q(sqrt -a).
// So such a b exists iff (a,-1) is split by Q(sqrt -a), i.e.
//
//   CRITERION.  For a > 0 squarefree, Q(sqrt a) lies in a Q8-extension of Q
//   iff at every place v where the quaternion algebra (a,-1) ramifies, -a is
//   a nonsquare in Q_v.
//
// (The positivity of b is automatic: (b,-a)_oo = 1 for b > 0, and
// (a,-1)_oo = 1 because a > 0.)  Case (b) is properly solvable exactly when
// this holds -- an improper solution would be a C_4-extension, which is why
// the search over b is the right question and not merely solvability.
//
// This criterion was checked against brute-force search over b for every
// squarefree a < 200; they agree.  a = 7 fails, a = 2, 3, 5 pass.

// ---------------------------------------------------------------------
// Which quadratic field does an index-2 subgroup of (Z/dZ)^* cut out?
// Done with Kronecker symbols rather than number fields: the quadratic
// subfields of Q(mu_d) are the Q(sqrt m) whose fundamental discriminant
// divides d, and the character (m/.) has kernel the given subgroup.
// ---------------------------------------------------------------------
FundamentalDiscriminant := function(m)
    if m mod 4 eq 1 then return m; else return 4*m; end if;
end function;

// residues: the subgroup of (Z/dZ)^* to be cut out, as a set of integers.
// Returns true, m  with the fixed field equal to Q(sqrt m), or false.
QuadraticFieldOfSubgroup := function(d, residues)
    units := [ u : u in [1..d-1] | Gcd(u, d) eq 1 ];
    for D in Divisors(d) do
        for sgn in [1, -1] do
            m := sgn * SquarefreeFactorization(D);
            if m eq 1 then continue; end if;
            if not IsDivisibleBy(d, Abs(FundamentalDiscriminant(m))) then
                continue;
            end if;
            ker := { u : u in units | KroneckerSymbol(m, u) eq 1 };
            if ker eq { u : u in residues } then return true, m; end if;
        end for;
    end for;
    return false, 0;
end function;

// The subgroup of (Z/dZ)^* corresponding to Ker(phi) inside C.
KernelResidues := function(ebp, d)
    C := ebp`C; f := ebp`f; phi := ebp`phi;
    return { IntegerRing()!f(c) mod d : c in C | phi(c) eq Id(ebp`B) };
end function;

// ---------------------------------------------------------------------
// Witt's criterion
// ---------------------------------------------------------------------
BadPlaces := function(nums)
    P := { 2 };
    for n in nums do
        if n ne 0 then
            for q in PrimeDivisors(Abs(n)) do Include(~P, q); end for;
        end if;
    end for;
    return Sort(Setseq(P));
end function;

// (x,y)_p, with p = -1 meaning the real place.  Magma's HilbertSymbol takes
// -1 for the infinite place; if your version disagrees, this is the one line
// to change.
Hilb := function(x, y, p)
    return HilbertSymbol(RationalField()!x, RationalField()!y, p);
end function;

WittEmbeds := function(a, b)
    ab := a*b;
    if a le 0 or b le 0 then return false; end if;
    for p in [-1] cat BadPlaces([a, b, ab]) do
        if Hilb(a,b,p) * Hilb(a,ab,p) * Hilb(b,ab,p) ne 1 then
            return false;
        end if;
    end for;
    return true;
end function;

IsSquareInQp := function(m, p)
    if p eq -1 then return m gt 0; end if;
    v := Valuation(m, p);
    if IsOdd(v) then return false; end if;
    u := m div p^v;
    if p eq 2 then return (u mod 8) eq 1; end if;
    return IsSquare(GF(p) ! u);
end function;

// Does Q(sqrt a) sit inside some Q8-extension of Q?
QuadraticInQ8 := function(a)
    if a le 0 then return false; end if;
    a := SquarefreeFactorization(a);
    if a eq 1 then return false; end if;
    for p in [-1] cat BadPlaces([a, -1, -a]) do
        if Hilb(a, -1, p) eq -1 then
            if IsSquareInQp(-a, p) then return false; end if;
        end if;
    end for;
    return true;
end function;

// ---------------------------------------------------------------------
// The certificate.  ebp1 is assumed already maximally split-reduced.
// Returns true only when the pair is PROPERLY solvable.
// ---------------------------------------------------------------------
CertifyResidualQ8 := function(ebp1, d)
    G := ebp1`G; B := ebp1`B; N := Kernel(ebp1`pi);
    if #G ne 8 or IdentifyGroup(G) ne <8, 4> then return false, "not Q8"; end if;

    resid := KernelResidues(ebp1, d);

    if #N eq 2 and #B eq 4 then
        // biquadratic phi: recover the three quadratic subfields
        quads := [];
        // the quadratic subfields of F are the Q(sqrt m) whose character is
        // trivial on Ker(phi)
        for D in Divisors(d) do
            for sgn in [1, -1] do
                m := sgn * SquarefreeFactorization(D);
                if m eq 1 then continue; end if;
                if not IsDivisibleBy(d, Abs(FundamentalDiscriminant(m))) then continue; end if;
                if forall{ u : u in resid | KroneckerSymbol(m, u) eq 1 } then
                    Include(~quads, m);
                end if;
            end for;
        end for;
        if #quads lt 2 then return false, "could not identify F"; end if;
        a := quads[1]; b := quads[2];
        return WittEmbeds(a, b), Sprintf("biquadratic (%o, %o)", a, b);
    end if;

    if #N eq 4 and #B eq 2 then
        ok, a := QuadraticFieldOfSubgroup(d, resid);
        if not ok then return false, "could not identify F"; end if;
        return QuadraticInQ8(a), Sprintf("quadratic Q(sqrt %o)", a);
    end if;

    return false, "unexpected Q8 shape";
end function;

// ---------------------------------------------------------------------
// Top-level: does this pair certify a PROPER solution?
// ---------------------------------------------------------------------
CertifyAdmissible := function(ebp, d)
    ebp1, allAbelian, _ := MaximalSplitReduction(ebp);
    if not allAbelian then
        // the climb back up the tower is not justified; stay silent
        return false, "non-abelian summand split off";
    end if;
    if #Kernel(ebp1`pi) eq 1 then
        return true, "fully split";
    end if;
    return CertifyResidualQ8(ebp1, d);
end function;
