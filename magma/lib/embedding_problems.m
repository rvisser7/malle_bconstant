// =====================================================================
// Enumeration of embedding problems: Gpiphi
// =====================================================================
//
// Extracted verbatim from compute_all_fast.m. The code below is unchanged
// byte-for-byte, so the split cannot alter any computed value.
//
// Requires (load first): records.m

Gpiphi := function(G)
    d := Exponent(G);
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
