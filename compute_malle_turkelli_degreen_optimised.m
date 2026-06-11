// Goal: Compute Malle's a, Malle's b (b_M), and Turkelli's b (b_T)
// for all Transitive Groups of degree n, and log to a file.

/* Output structure: GrpAb, GrpPerm, GrpAb, Map, Map, Map */
EmbeddingProb := recformat<
    B, G, C, f, pi, phi
>;
// ---------------------------------------------------------
// 1. Generate all (\pi, \phi) pairs (Optimized via Abelianization)
// ---------------------------------------------------------
Gpiphi := function(G)
    d := Exponent(G);
    C, f := MultiplicativeGroup(Integers(d));

    // Obtain the abelianization of G directly
    AbG, f_AbG := AbelianQuotient(G);
    
    // C is already abelian, but routing it through AbelianQuotient 
    // strictly types it as GrpAb to ensure Magma's Hom() works flawlessly.
    AbC, f_AbC := AbelianQuotient(C); 

    // We only need the subgroups of the abelianization
    SubG := Subgroups(AbG);
    Pair := [];
    
    // Iterate through all quotients of G^ab
    for i := 1 to #SubG do
        S := SubG[i]`subgroup;
        Q, fQ := quo<AbG | S>;
        
        // Construct the projection pi: G -> G^ab -> Q
        pi := f_AbG * fQ;
        
        // Find all surjective homomorphisms from C to this abelian quotient Q
        allphi, fallphi := Hom(AbC, Q);
        
        for h in allphi do
            phi_map := fallphi(h);
            if IsSurjective(phi_map) then
                // Construct the full map phi: C -> AbC -> Q
                phi := f_AbC * phi_map;
                
                ebp := rec< EmbeddingProb |
                    B   := Q,
                    G   := G,
                    C   := C,
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
// 2. Prepare Smin (Optimized via Conjugacy Classes)
// ---------------------------------------------------------
ind := function(g)
    // Index = Degree - (Total number of cycles)
    return Degree(Parent(g)) - &+[ c[2] : c in CycleStructure(g) ];
end function;

MinIndex := function(G)
    classes := Classes(G);
    min_ind := Degree(G);
    
    // Find the absolute minimum index using just class representatives
    for i := 1 to #classes do 
        rep := classes[i][3];
        if rep eq Id(G) then continue; end if;
        
        idx := ind(rep);
        if idx lt min_ind then
            min_ind := idx;
        end if;
    end for;
    
    // Collect all elements achieving this minimum index
    Smin := {}; // Sets automatically handle uniqueness
    for i := 1 to #classes do
        rep := classes[i][3];
        if rep ne Id(G) and ind(rep) eq min_ind then
            // Grab the entire conjugacy class instantly
            Smin join:= Conjugates(G, rep);
        end if;
    end for;
    
    return min_ind, Setseq(Smin);
end function;

// ---------------------------------------------------------
// 3. Compute orbits function (Ultra-Optimized via BFS Orbits)
// ---------------------------------------------------------
bpiphi := function(ebp, Smin)
    G := ebp`G;
    C := ebp`C;
    pi := ebp`pi;
    phi := ebp`phi;
    f := ebp`f;
    N := Kernel(pi);

    // 1. Filter Smin to elements in the kernel of pi
    Sminpi := { s : s in Smin | s in N };
    
    if IsEmpty(Sminpi) then
        return 0, 0;
    end if;

    // 2. Build the generators of the fiber product action
    action_pairs := [];
    
    // Action from generators of the kernel (N)
    for n in Generators(N) do
        // The 'G!' explicitly casts the subgroup element 'n' into the parent group 'G'
        Append(~action_pairs, <G!n, 1>); 
    end for;
    
    // Action from generators of C
    for c in Generators(C) do
        b := phi(c);
        x_c := b @@ pi; // Find preimage of b in G under pi
        a_val := IntegerRing()!(f(c));
        // Cast x_c to G as well, just to guarantee uniform typing
        Append(~action_pairs, <G!x_c, a_val>); 
    end for;

    // 3. Compute orbits via Breadth-First Search (BFS)
    visited := {};
    orbits := 0;
    
    for s in Sminpi do
        if s in visited then 
            continue; 
        end if;
        
        orbits +:= 1;
        
        // Start BFS for the current orbit
        queue := [s];
        Include(~visited, s);
        
        idx := 1;
        while idx le #queue do
            curr := queue[idx];
            idx +:= 1;
            
            // Apply all generators to find the rest of the orbit
            for pair in action_pairs do
                x := pair[1];
                a_val := pair[2];
                
                next_s := x * (curr^a_val) * x^(-1);
                
                if not (next_s in visited) then
                    Include(~visited, next_s);
                    Append(~queue, next_s);
                end if;
            end for;
        end while;
    end for;

    return #Sminpi, orbits;
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
