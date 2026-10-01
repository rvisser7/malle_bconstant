// =====================================================================
// Embedding problems: Gpiphi, IsTrivialQuotientEbp
// =====================================================================
//
// Requires (load first): records.m
//
// Both functions are identical in the disc and prp sources, so they live
// here rather than in either ordering subfolder.
//
// Gpiphi now returns the pair list AND a grouping of its indices by pi.
// Several phi share each pi, and everything expensive in Phase 1 depends on
// pi alone -- Kernel(pi), then Classes/ClassMap of the kernel (both
// orderings, see class_orbits.m).  Walking the flat list recomputes all of
// that once per phi; walking the groups computes it once per pi.

// PRUNING (new).  A pair needs a surjection C ->> B = AbG/S, so
//   * #B divides #C, and
//   * Exp(B) divides e := Exp(C), i.e. S contains e*AbG.
// So the subgroups S are enumerated in Ae := AbG / e*AbG, of index dividing
// #C, instead of over the whole subgroup lattice of AbG -- for a 2-group of
// degree 32 with AbG = C2^10 that is the difference between a handful of
// subgroups of index <= #C and essentially all of them.  Subgroups of Ae
// are in bijection with subgroups of AbG containing e*AbG, with the same
// quotients, so the set of pairs is unchanged up to that identification.
//
// MinReps (disc ordering): representatives of the minimal-index classes of
// G.  Ker(pi) meets Smin iff some minimal class maps INTO S, since the map
// to AbG is constant on classes and Ker(pi) is the preimage of S.  Pairs
// failing this are skipped by Theorem 2.16 anyway; this drops them before
// Kernel(pi) is ever formed.  Leave MinReps empty to keep every S (prp,
// where every non-identity class is minimal).
//
// pair_index still means position in T, but T now omits the pruned pairs,
// so indices are not comparable with output from before this change.

Gpiphi := function(G, d : MinReps := [])
    C, f := MultiplicativeGroup(Integers(d));
    AbG, f_AbG := AbelianQuotient(G);
    AbC, f_AbC := AbelianQuotient(C);
    nC := #AbC;
    e := nC eq 1 select 1 else Exponent(AbC);

    E := sub< AbG | [ AbG | e*AbG.i : i in [1..Ngens(AbG)] ] >;
    Ae, fAe := quo< AbG | E >;
    toAe := f_AbG * fAe;
    imgs := [ toAe(r) : r in MinReps ];

    // IndexLimit is only a hint to Magma; the divisibility filter below is
    // what guarantees correctness, so the fallback is safe.
    try
        SubAe := Subgroups(Ae : IndexLimit := nC);
    catch err
        SubAe := Subgroups(Ae);
    end try;

    Pair := [];
    groups := [];
    for R in SubAe do
        S := R`subgroup;
        if nC mod (#Ae div #S) ne 0 then continue; end if;
        if #imgs gt 0 and not exists{ x : x in imgs | x in S } then continue; end if;

        Q, fQ := quo< Ae | S >;
        pi := toAe * fQ;
        allphi, fallphi := Hom(AbC, Q);

        grp := [];
        for h in allphi do
            phi_map := fallphi(h);
            if IsSurjective(phi_map) then
                phi := f_AbC * phi_map;
                ebp := rec< EmbeddingProb |
                    B := Q, G := G, C := C, f := f, pi := pi, phi := phi, d := d
                >;
                Append(~Pair, ebp);
                Append(~grp, #Pair);
            end if;
        end for;
        if #grp gt 0 then Append(~groups, grp); end if;
    end for;
    return Pair, groups;
end function;

// Reference implementation: the pre-pruning enumeration over ALL subgroups
// of AbG.  Not used in production; tests/test_gpiphi_pruning.m checks that
// Gpiphi produces the same multiset of b-values.
GpiphiReference := function(G, d)
    C, f := MultiplicativeGroup(Integers(d));
    AbG, f_AbG := AbelianQuotient(G);
    AbC, f_AbC := AbelianQuotient(C);
    Pair := [];
    groups := [];
    for R in Subgroups(AbG) do
        S := R`subgroup;
        Q, fQ := quo< AbG | S >;
        pi := f_AbG * fQ;
        allphi, fallphi := Hom(AbC, Q);
        grp := [];
        for h in allphi do
            phi_map := fallphi(h);
            if IsSurjective(phi_map) then
                Append(~Pair, rec< EmbeddingProb | B := Q, G := G, C := C, f := f,
                                   pi := pi, phi := f_AbC * phi_map, d := d >);
                Append(~grp, #Pair);
            end if;
        end for;
        if #grp gt 0 then Append(~groups, grp); end if;
    end for;
    return Pair, groups;
end function;

IsTrivialQuotientEbp := function(ebp)
    return #ebp`B eq 1;
end function;
