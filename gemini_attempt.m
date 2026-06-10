// Helper to calculate the permutation index of an element
PermIndex := function(g, deg)
    C := CycleStructure(g);
    k := 0; n := 0;
    for i:=1 to #C do
       k := k + C[i][2];
       n := n + C[i][2]*C[i][1];
    end for;
    return deg - (k + (deg - n));
end function;

// Main Function to compute Wang's Conjecture b-constant over Q
ComputeWangsBOverQ := procedure(G)
    deg := Degree(G);
    
    // STEP 1: Find elements with minimal index (Malle's a-constant)
    all_inds := [PermIndex(g, deg) : g in G | g ne Id(G)];
    min_exp := Min(all_inds);
    
    // STEP 2: Compute the cyclotomic d-constant strictly for minimal elements
    S_min := [g : g in G | g ne Id(G) and PermIndex(g, deg) eq min_exp];
    d := Lcm([Order(g) : g in S_min]);
    
    print "==================================================";
    printf "Permutation Group Degree: %o, Order: %o\n", deg, #G;
    printf "Minimal Index (a-constant): %o\n", min_exp;
    printf "Cyclotomic d-constant: %o\n", d;
    print "==================================================";
    
    // Construct the universe group G x (Z/dZ)* 
    C, f := MultiplicativeGroup(Integers(d));
    H := sub<C|Id(C)>;
    r, CP := CosetAction(C, H);
    r := Inverse(r);
    CG, iG, iC := DirectProduct(G, CP);
    
    NG := NormalSubgroups(G);
    NC := NormalSubgroups(CP);
    
    // STEP 3: Identify valid quotient pairs
    Box := [];
    for i:=1 to #NG do
        N := NG[i]`subgroup;
        // Condition: ind(Ker(pi)) == ind(G)
        N_elts := [g : g in N | g ne Id(G)];
        if #N_elts eq 0 or Min([PermIndex(g, deg) : g in N_elts]) ne min_exp then 
            continue; 
        end if;
        
        for j:=1 to #NC do
             D := NC[j]`subgroup;
             if IsIsomorphic(quo<G|N>, quo<CP|D>) then
                 Include(~Box, [i,j]);
             end if; 
        end for;
    end for;
    
    max_b_M := 0;
    max_b_T := 0;
    max_b_Wang := 0;
    
    for b in Box do
        i:=b[1]; j:=b[2];
        N:=NG[i]`subgroup;
        D:=NC[j]`subgroup;
        QG, qG:=quo<G|N>;
        QC, qC:=quo<CP|D>;
        _, iso := IsIsomorphic(QG, QC);
        
        // Restrict strictly to S_min_N (Definition 2.8)
        S_min_N := [g : g in N | g in S_min];
        
        // Build the Fiber Product G1
        S:=[];
        for g in CG do
            x:=iC[1](g); y:=iC[2](g);
            if iso(qG(x)) eq qC(y) then Include(~S,g); end if;
        end for;
        G1:=sub<CG|S>;
        
        // Compute twisted orbits exactly on S_min_N via Burnside's Lemma
        fix:=0;
        for g in G1 do
            x:=iC[1](g); y:=iC[2](g);
            c:=y^(-1);
            c:=IntegerRing()!f(r(c));
            
            for n in S_min_N do
                 if n^x eq n^c then fix:=fix+1; end if;
            end for;
        end for;
        
        // This is guaranteed to be a perfect integer by Burnside's Lemma
        Orb:=Integers() ! (fix/Order(G1)); 
        
        // Track baseline and Turkelli maximums
        if #N eq #G and #D eq #CP then max_b_M := Orb; end if;
        if Orb gt max_b_T then max_b_T := Orb; end if;
        
        // ------------------------------------------------
        // DYNAMIC LIFTING CHECK FOR k = Q
        // ------------------------------------------------
        is_solvable := true;
        
        // A. Infinite Place Obstruction Check
        if d gt 2 then
            minus_one := Integers(d)!(-1);
            
            // ROBUST FIX: Search CP for the element that maps to -1
            CP_minus_one := Id(CP);
            for w in CP do
                if f(r(w)) eq minus_one then
                    CP_minus_one := w;
                    break;
                end if;
            end for;
            
            img_inf := qC(CP_minus_one);
            
            if img_inf ne Id(QC) then
                has_real_lift := false;
                for x in G do
                    if iso(qG(x)) eq img_inf and Order(x) le 2 then
                        has_real_lift := true;
                        break;
                    end if;
                end for;
                if not has_real_lift then is_solvable := false; end if;
            end if;
        end if;
        
        // B. Tame/Central Finite Prime Obstruction Check 
        if is_solvable and IsAbelian(G) then
            fact := Factorization(d);
            for p_tup in fact do
                p := p_tup[1];
                if Valuation(d, p) gt Valuation(p-1, p) and #QC mod p eq 0 then
                    target_order := p^(Valuation(d, p));
                    
                    has_elt := false;
                    for c_class in Classes(G) do
                        if c_class[1] mod target_order eq 0 then
                            has_elt := true;
                            break;
                        end if;
                    end for;
                    
                    if not has_elt then is_solvable := false; end if;
                end if;
            end for;
        end if;
        
        // If the embedding survives all local checks over Q, it is globally valid!
        if is_solvable and (Orb gt max_b_Wang) then
            max_b_Wang := Orb;
        end if;
    end for;
    
    printf "Malle's original b_M: %o\n", max_b_M;
    printf "Türkelli's modified b_T: %o\n", max_b_T;
    printf "Jiuya Wang's Refined b:   %o\n", max_b_Wang;
    print "==================================================";
end procedure;

// Test Case: The C_3 wr C_4 counterexample
G := WreathProduct(CyclicGroup(3), CyclicGroup(4));
ComputeWangsBOverQ(G);
