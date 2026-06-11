// Goal: Compute Malle's a, Malle's b (b_M), and Turkelli's b (b_T)
// for all Transitive Groups of degree n, and log to a file.

/* Output structure: GrpAb, GrpPerm, GrpAb, Map, Map, Map */
EmbeddingProb := recformat<
    B, G, C, f, pi, phi
>;

// ---------------------------------------------------------
// 1. Generate all (\pi, \phi) pairs
// ---------------------------------------------------------
Gpiphi := function(G)
    d := Exponent(G);
    C, f := MultiplicativeGroup(Integers(d));
    H := sub<C|Id(C)>;

    Box := [];
    NG := NormalSubgroups(G);
    NC := Subgroups(C);
    
    for i := 1 to #NG do
        N := NG[i]`subgroup;
        if IsAbelian(quo<G|N>) then
            for j := 1 to #NC do
                 D := NC[j]`subgroup;
                 if IsIsomorphic(AbelianQuotient(quo<G|N>), quo<C|D>) then         
                     Include(~Box, i); 
                     break j;
                 end if; 
            end for;
        end if;
    end for;

    Pair := [];
    for i in Box do
        HG := NG[i]`subgroup;
        QG, fQG := quo<G|HG>;
        QGA, fQGA := AbelianQuotient(QG);
        pi := fQG * fQGA;

        CA, fCA := AbelianQuotient(C);
        allphi, fallphi := Hom(CA, QGA);
        
        for h in allphi do
            if IsSurjective(fallphi(h)) then
                phi := fCA * fallphi(h);
                ebp := rec< EmbeddingProb |
                    B   := Codomain(pi),
                    G   := Domain(pi),
                    C   := Domain(phi),
                    f   := f,
                    pi  := pi,
                    phi := phi
                >;
                Append(~Pair, ebp);
            end if;
        end for;
    end for;
    
    return Pair;
end function;

// ---------------------------------------------------------
// 2. Prepare Smin
// ---------------------------------------------------------
ind := function(g)
    C := CycleStructure(g);
    k := 0; 
    n := 0;
    for i := 1 to #C do
       k := k + C[i][2];
       n := n + C[i][2] * C[i][1];
    end for;
    return n - k;
end function;

MinIndex := function(G)
    A := []; 
    a := #G;
    for g in G do
        if g ne Id(G) and ind(g) lt a then
            a := ind(g);
            A := [g];
        elif g ne Id(G) and ind(g) eq a then
            Append(~A, g);
        end if;
    end for;
    return a, A;
end function;

// ---------------------------------------------------------
// 3. Compute orbits function
// ---------------------------------------------------------
bpiphi := function(ebp, Smin)
    B := ebp`B;
    G := ebp`G;
    C := ebp`C;
    f := ebp`f;
    pi := ebp`pi;
    phi := ebp`phi;

    H := sub<C|Id(C)>;
    r, CP := CosetAction(C, H);
    r := Inverse(r);
    CG, into, onto := DirectProduct(G, CP);
    
    S := [];
    for g in CG do
        x := onto[1](g);
        a := onto[2](g);
        a := r(a);
        if pi(x) eq phi(a) then 
            Include(~S, g); 
        end if;
    end for;
    CGfiber := sub<CG|S>;

    Sminpi := [];
    N := Kernel(pi);
    for s in Smin do
       if s in N then 
           Include(~Sminpi, s); 
       end if;
    end for;

    if #Sminpi gt 0 then
        fix := 0;
        for g in CGfiber do
            x := onto[1](g);
            a := onto[2](g); 
            a := r(a);
            a := IntegerRing()!f(a);
            k := 0;
            for s in Sminpi do
                 if s in N then
                      if x * s * x^(-1) eq s^a then 
                          k := k + 1; 
                      end if;
                 end if;
            end for;
            fix := fix + k;
        end for;
        
        Orb := fix / Order(CGfiber);
        bpiphi_val := Orb;
    else 
        bpiphi_val := 0;
    end if;

    return #Sminpi, bpiphi_val;
end function;

// ---------------------------------------------------------
// 4. Compute Constants Wrapper
// ---------------------------------------------------------
ComputeConstants := function(G)
    a, Smin := MinIndex(G);
    T := Gpiphi(G);

    b_T := 0;
    b_M := 0;

    for ebp in T do
        size_Sminpi, orb := bpiphi(ebp, Smin);
        orb_int := Integers()!orb; 

        if orb_int gt b_T then
            b_T := orb_int;
        end if;

        if Order(Codomain(ebp`pi)) eq 1 then
            b_M := orb_int;
        end if;
    end for;

    return a, b_M, b_T;
end function;

// ---------------------------------------------------------
// 5. Automated File Output for Transitive Groups
// ---------------------------------------------------------
EvaluateDegree := procedure(n)
    // Create the filename based on n
    filename := Sprintf("Constants_Degree_%o.txt", n);
    
    // Initialize the file (using Overwrite := true clears any old data from previous runs)
    header := Sprintf("Evaluating Transitive Groups of Degree %o\n==========================================", n);
    Write(filename, header : Overwrite := true);
    
    num_groups := NumberOfTransitiveGroups(n);
    print Sprintf("Starting evaluation of %o groups for degree %o. Outputting to %o", num_groups, n, filename);
    print "--------------------------------------------------------------------------------";
    
    // Iterate through all transitive groups of degree n
    for i := 1 to num_groups do
        G := TransitiveGroup(n, i);
        
        // Compute the constants
        a, b_M, b_T := ComputeConstants(G);
        
        // Format the result
        result_str := Sprintf("Group %oT%o: a = %o, b_M = %o, b_T = %o", n, i, a, b_M, b_T);
        
        // Write to file and print to console
        Write(filename, result_str);
        print result_str; 
        
        // Check for the "DIFFERENT!" condition
        if b_M ne b_T then
            diff_str := "    ---> DIFFERENT! b_M != b_T";
            Write(filename, diff_str);
            print diff_str;
        end if;
    end for;
    
    print "==========================================";
    print "Finished! Results saved to:", filename;
end procedure;

/* ---------------------------------------------------------
   Execution: Change the number below to test different degrees!
   --------------------------------------------------------- */
   
EvaluateDegree(4);