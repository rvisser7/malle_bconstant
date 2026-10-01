// =====================================================================
// Embedding problems: Gpiphi, IsTrivialQuotientEbp
// =====================================================================
//
// Verbatim from the discriminant-ordering source; unchanged byte-for-byte.
//
// Requires (load first): records.m
//
// Both functions are identical in the disc and prp sources, so they live
// here rather than in either ordering subfolder.
//
// Gpiphi now returns the pair list AND a grouping of its indices by pi.
// Several phi share each pi, and everything expensive in Phase 1 depends on
// pi alone -- Kernel(pi), and then Classes/ClassMap of the kernel (prp) or
// Smin meet N (disc).  Walking the flat list recomputes all of that once per
// phi; walking the groups computes it once per pi.  The pair list itself is
// unchanged, so pair_index still means position in T.

Gpiphi := function(G, d)
    C, f := MultiplicativeGroup(Integers(d));
    AbG, f_AbG := AbelianQuotient(G);
    AbC, f_AbC := AbelianQuotient(C); 
    SubG := Subgroups(AbG);
    Pair := [];
    groups := [];
    
    for i := 1 to #SubG do
        S := SubG[i]`subgroup;
        Q, fQ := quo<AbG | S>;
        pi := f_AbG * fQ;
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

IsTrivialQuotientEbp := function(ebp)
    return #ebp`B eq 1;
end function;
