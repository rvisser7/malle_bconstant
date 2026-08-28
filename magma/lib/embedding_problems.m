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

Gpiphi := function(G, d)
    C, f := MultiplicativeGroup(Integers(d));
    AbG, f_AbG := AbelianQuotient(G);
    AbC, f_AbC := AbelianQuotient(C); 
    SubG := Subgroups(AbG);
    Pair := [];
    
    for i := 1 to #SubG do
        S := SubG[i]`subgroup;
        Q, fQ := quo<AbG | S>;
        pi := f_AbG * fQ;
        allphi, fallphi := Hom(AbC, Q);
        
        for h in allphi do
            phi_map := fallphi(h);
            if IsSurjective(phi_map) then
                phi := f_AbC * phi_map;
                ebp := rec< EmbeddingProb |
                    B := Q, G := G, C := C, f := f, pi := pi, phi := phi
                >;
                Append(~Pair, ebp);
            end if;
        end for;
    end for;
    return Pair;
end function;

IsTrivialQuotientEbp := function(ebp)
    return #ebp`B eq 1;
end function;
