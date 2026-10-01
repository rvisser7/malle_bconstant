// =====================================================================
// Splitting conditions
// =====================================================================
//
// Requires (load first): records.m

// Does the normal subgroup K have a complement in G?  Returns the answer
// and, if yes, one complement.
//
// First choice: Complements(G, K), which works by cohomology when K (or
// G/K) is soluble -- always true in the split tower, where K is nilpotent
// or of odd order,
// and in the certificates, where G/K is abelian.  If Magma declines (e.g.
// both K and G/K insoluble) we fall back to the old exhaustive search:
// conjugacy classes of subgroups of order #G/#K, one of which meets K
// trivially iff K is complemented.  Testing one representative per class is
// sound because K is normal, so #(H^g meet K) = #(H meet K).
IsSplitKernel := function(G, K)
    if #K eq 1 then return true, G; end if;
    if #K eq #G then return true, sub< G | Id(G) >; end if;

    decided := false;
    ok := false;
    H := sub< G | Id(G) >;
    try
        comps := Complements(G, K);
        decided := true;
        if #comps gt 0 then ok := true; H := comps[1]; end if;
    catch err
        decided := false;
    end try;
    if decided then return ok, H; end if;

    targetOrder := #G div #K;
    for R in Subgroups(G : OrderEqual := targetOrder) do
        H := R`subgroup;
        if #(H meet K) eq 1 then return true, H; end if;
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
