// =====================================================================
// Splitting conditions
// =====================================================================
//
// Extracted verbatim from compute_all_fast.m. The code below is unchanged
// byte-for-byte, so the split cannot alter any computed value.
//
// Requires (load first): records.m

// OPTIMISED: was computing the ENTIRE subgroup lattice of G and then throwing
// away everything of the wrong order.  OrderEqual pushes that filter into
// Magma's search.  Testing one representative per conjugacy class is still
// sound because K is normal in every call site (N1 and Nbar are both normal),
// so #(H^g meet K) = #(H meet K).
IsSplitKernel := function(G, K)
    targetOrder := #G div #K;
    SG := Subgroups(G : OrderEqual := targetOrder);
    for R in SG do
        H := R`subgroup;
        if #(H meet K) ne 1 then continue; end if;
        return true, H;
    end for;
    return false, sub< G | Id(G) >;
end function;

ImageSubgroupUnderMap := function(H, q)
    Q := Codomain(q);
    imgs := [];
    for h in Generators(H) do
        Append(~imgs, q(h));
    end for;
    if #imgs eq 0 then return sub< Q | Id(Q) >; end if;
    return sub< Q | imgs >;
end function;

IsTwoStepSplitReduction := function(ebp)
    G  := ebp`G;
    pi := ebp`pi;
    N  := Kernel(pi);
    NG := NormalSubgroups(G);

    for R in NG do
        N1 := R`subgroup;
        if not N1 subset N then continue; end if;

        ok1, H1 := IsSplitKernel(G, N1);
        if not ok1 then continue; end if;

        G1, q1 := quo< G | N1 >;
        Nbar := ImageSubgroupUnderMap(N, q1);

        ok2, H2 := IsSplitKernel(G1, Nbar);
        if not ok2 then continue; end if;

        return true, N1, q1, H1, H2;
    end for;

    Nzero := sub< G | Id(G) >;
    Gdummy, qdummy := quo< G | Nzero >;
    return false, Nzero, qdummy, sub< G | Id(G) >, sub< Gdummy | Id(Gdummy) >;
end function;

SplitReduction := function(ebp)
    ok, N1, q1, H1, H2 := IsTwoStepSplitReduction(ebp);
    G1 := Codomain(q1);
    
    if ok then
        pi1 := hom< G1 -> ebp`B | [ ebp`pi(G1.i @@ q1) : i in [1..Ngens(G1)] ] >;
    else
        pi1 := hom< G1 -> ebp`B | [ Id(ebp`B) : i in [1..Ngens(G1)] ] >;
    end if;
    
    ebp1 := rec< EmbeddingProb |
        B := ebp`B, G := G1, C := ebp`C, f := ebp`f, pi := pi1, phi := ebp`phi, d := ebp`d
    >;
    
    return ok, ebp1, N1, q1, H1, H2;
end function;
