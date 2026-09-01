// =====================================================================
// certificates/shared.m  --  what every ARITHMETIC certificate needs
// =====================================================================
//
// Requires (load first): records.m
//
// The certificate files divide in two:
//
//   structural.m   field-independent.  Every entry is a statement about the
//                  SHAPE of the residual plus a realisability fact; phi never
//                  enters.
//   central.m, q8.m
//                  arithmetic.  These look at which subfield of Q(mu_d) the
//                  pair actually cuts out, or at local conditions.
//
// Everything here is machinery for the second kind: turning phi into a field,
// and Hilbert symbols over Q.  It used to live inside the Q8 file, where the
// next arithmetic certificate could not reach it.
//
// BASE FIELD.  This whole codebase is over Q -- Gpiphi takes the full
// (Z/dZ)^* as Gal(Q(mu_d)/Q).  Several statements below are Q-specific and
// are marked as such.

// Fundamental discriminant of the quadratic field Q(sqrt m), m squarefree.
// Named FundDisc, not FundamentalDiscriminant, to avoid shadowing the Magma
// intrinsic of that name.
FundDisc := function(m)
    if m mod 4 eq 1 then return m; else return 4*m; end if;
end function;

// The subgroup of (Z/dZ)^* corresponding to Ker(phi), as a set of integers.
KernelResidues := function(ebp, d)
    C := ebp`C; f := ebp`f; phi := ebp`phi;
    return { IntegerRing()!f(c) mod d : c in C | phi(c) eq Id(ebp`B) };
end function;

// Every quadratic subfield of the field cut out by phi, as a list of
// squarefree m with Q(sqrt m) contained in Q(phi).
//
// Done with Kronecker symbols rather than number fields: the quadratic
// subfields of Q(mu_d) are the Q(sqrt m) with |disc| dividing d, and
// Q(sqrt m) is contained in Q(phi) exactly when (m/.) is trivial on the
// residues of Ker(phi).  For those m the divisibility test forces d even
// whenever m is 2 or 3 mod 4, so every unit u mod d is odd and
// KroneckerSymbol(m, u) agrees with the character of the fundamental
// discriminant.
QuadraticSubfieldsOfPhi := function(d, residues)
    out := [];
    for D in Divisors(d) do
        for sgn in [1, -1] do
            m := sgn * SquarefreeFactorization(D);
            if m eq 1 then continue; end if;
            if not IsDivisibleBy(d, Abs(FundDisc(m))) then continue; end if;
            if forall{ u : u in residues | KroneckerSymbol(m, u) eq 1 } then
                Include(~out, m);
            end if;
        end for;
    end for;
    return out;
end function;

// The quadratic field cut out by an index-2 subgroup of (Z/dZ)^*, i.e. the
// m whose character has EXACTLY the given kernel.
QuadraticFieldOfSubgroup := function(d, residues)
    units := [ u : u in [1..d-1] | Gcd(u, d) eq 1 ];
    for D in Divisors(d) do
        for sgn in [1, -1] do
            m := sgn * SquarefreeFactorization(D);
            if m eq 1 then continue; end if;
            if not IsDivisibleBy(d, Abs(FundDisc(m))) then continue; end if;
            ker := { u : u in units | KroneckerSymbol(m, u) eq 1 };
            if ker eq { u : u in residues } then return true, m; end if;
        end for;
    end for;
    return false, 0;
end function;

// ---------------------------------------------------------------------
// Hilbert symbols over Q.  p = -1 means the real place, which is Magma's
// HilbertSymbol convention; if your version disagrees, Hilb is the one line
// to change.
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

Hilb := function(x, y, p)
    return HilbertSymbol(RationalField()!x, RationalField()!y, p);
end function;

IsSquareInQp := function(m, p)
    if p eq -1 then return m gt 0; end if;
    v := Valuation(m, p);
    if IsOdd(v) then return false; end if;
    u := m div p^v;
    if p eq 2 then return (u mod 8) eq 1; end if;
    return IsSquare(GF(p) ! u);
end function;
