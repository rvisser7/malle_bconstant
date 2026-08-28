// =====================================================================
// FullCheck -- DISCRIMINANT ordering
// =====================================================================
//
// Verbatim from the discriminant-ordering source; unchanged byte-for-byte.
//
// Requires (load first): records.m, splitting.m, local_tame.m, embedding_problems.m, disc/orbits.m

FullCheck := function(G)
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    T := Gpiphi(G, d);

    bM := 0; 
    bT := 0;
    evaluated_pairs := []; 

    // Phase 1: Fast Orbit Evaluation
    for j := 1 to #T do
        ebp := T[j];

        Sminpi := SminIntersectionKerPi(ebp, Smin);
        if #Sminpi eq 0 then continue; end if;

        numberSminInKer, bval := bpiphi(ebp, Smin);
        bval_int := Integers()!bval; 

        if bval_int gt bT then bT := bval_int; end if;

        if IsTrivialQuotientEbp(ebp) then
            if bval_int gt bM then bM := bval_int; end if;
        end if;

        Append(~evaluated_pairs, <j, ebp, bval_int>);
    end for;

    BWlowerSplit := bM; 
    BWupperLocal := bM;
    splitCandidates := []; 
    localCandidates := [];

    // Phase 2: Heavy Local Checks (Threshold-Optimized)
    if bM lt bT then
        for item in evaluated_pairs do
            j := item[1];
            ebp := item[2];
            bval_int := item[3];
            
            autoSolved := false;
            ebp1_generated := false;

            if bval_int gt BWlowerSplit then
                ebp1, allAbelian := MaximalSplitReduction(ebp);
                ebp1_generated := true;

                if not allAbelian then
                    autoSolved := false;
                elif #Kernel(ebp1`pi) eq 1 then
                    autoSolved := true;
                else
                    autoSolved := CertifyResidualQ8(ebp1, d);
                end if;
                
                if autoSolved then
                    BWlowerSplit := bval_int;

                    cand := rec< FullCheckCandidateFormat |
                        pair_index        := j,
                        b_value           := bval_int,
                        B_order           := #ebp`B,
                        Ker_order         := #Kernel(ebp`pi),
                        passes_split      := true,
                        passes_local      := false,
                        reduced_G_order   := #ebp1`G,
                        reduced_Ker_order := #Kernel(ebp1`pi)
                    >;
                    Append(~splitCandidates, cand);
                end if;
            end if;

            if bval_int gt BWupperLocal then
                okLocal := PassesCheckedLocalTests(ebp);
                
                if okLocal then
                    BWupperLocal := bval_int;

                    if not ebp1_generated then
                        ebp1 := MaximalSplitReduction(ebp);
                    end if;

                    cand := rec< FullCheckCandidateFormat |
                        pair_index        := j,
                        b_value           := bval_int,
                        B_order           := #ebp`B,
                        Ker_order         := #Kernel(ebp`pi),
                        passes_split      := autoSolved, 
                        passes_local      := true,
                        reduced_G_order   := #ebp1`G,
                        reduced_Ker_order := #Kernel(ebp1`pi)
                    >;
                    Append(~localCandidates, cand);
                end if;
            end if;
            
            if BWlowerSplit eq bT and BWupperLocal eq bT then
                break;
            end if;

        end for;
    end if;

    assert BWlowerSplit le BWupperLocal;
    R := rec< FullCheckResultFormat |
        group_order      := #G, minimal_index    := a,
        number_of_Smin   := #Smin, number_of_pairs  := #T,
        b_M              := bM, b_T              := bT,
        BW_lower_split   := BWlowerSplit, BW_upper_local   := BWupperLocal,
        split_candidates := splitCandidates, local_candidates := localCandidates
    >;

    return R;
end function;
