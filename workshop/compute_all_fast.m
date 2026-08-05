// =====================================================================
// Unified Magma Script: b_M, b_T, and b_W Bounds Evaluation
// Includes: Splitting tests, Local Tame/Real Checks, BFS Orbits, 
// Two-Phase Bypassing, and Command Line Execution.
// =====================================================================

// =====================================================================
// 1. Record Formats 
// =====================================================================
EmbeddingProb := recformat<
    B, G, C, f, pi, phi
>;

FullCheckCandidateFormat := recformat<
    pair_index, b_value, B_order, Ker_order,
    passes_split, passes_local, reduced_G_order, reduced_Ker_order
>;

FullCheckResultFormat := recformat<
    group_order, minimal_index, number_of_Smin, number_of_pairs,
    b_M, b_T, BW_lower_split, BW_upper_local,
    split_candidates, local_candidates
>;

// =====================================================================
// 2. Splitting Conditions 
// =====================================================================
IsSplitKernel := function(G, K)
    targetOrder := #G div #K;
    SG := Subgroups(G);
    for R in SG do
        H := R`subgroup;
        if #H ne targetOrder then continue; end if;
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
        B := ebp`B, G := G1, C := ebp`C, f := ebp`f, pi := pi1, phi := ebp`phi
    >;
    
    return ok, ebp1, N1, q1, H1, H2;
end function;

// =====================================================================
// 3. Local Checking 
// =====================================================================
UnitInteger := function(c, f)
    return IntegerRing()!f(c);
end function;

HasPreimage := function(pi, b)
    G := Domain(pi);
    for g in G do
        if pi(g) eq b then return true, g; end if;
    end for;
    return false, Id(G);
end function;

IsLocalLiftableTameByBImages := function(ebp, p, bX, bY)
    G  := ebp`G; pi := ebp`pi; N  := Kernel(pi);

    okX, X0 := HasPreimage(pi, bX);
    if not okX then return false, "No lift of Frobenius image", <Id(G), Id(G)>; end if;

    okY, Y0 := HasPreimage(pi, bY);
    if not okY then return false, "No lift of inertia image", <Id(G), Id(G)>; end if;

    for nX in N do
        X := X0*nX;
        for nY in N do
            Y := Y0*nY;
            if X*Y*X^(-1) eq Y^p then
                return true, "Liftable", <X,Y>;
            end if;
        end for;
    end for;
    return false, "No pair of lifts satisfies tame relation", <Id(G), Id(G)>;
end function;

IsLocalLiftableTameByCImages := function(ebp, p, xC, yC)
    phi := ebp`phi;
    bX := phi(xC); bY := phi(yC);
    return IsLocalLiftableTameByBImages(ebp, p, bX, bY);
end function;

CyclotomicFrobeniusAtPrime := function(C, f, d, p)
    e := Valuation(d, p); ppow := p^e; m := d div ppow;
    for c in C do
        a := UnitInteger(c, f);
        cond_p_part := (a mod ppow) eq 1;
        if m eq 1 then
            cond_m_part := true;
        else
            cond_m_part := (a mod m) eq (p mod m);
        end if;
        if cond_p_part and cond_m_part then return c; end if;
    end for;
    error "Could not find cyclotomic Frobenius element.";
end function;

CyclotomicInertiaAtPrime := function(C, f, d, p)
    e := Valuation(d, p); ppow := p^e; m := d div ppow;
    gens := [];
    for c in C do
        a := UnitInteger(c, f);
        if m eq 1 then Append(~gens, c);
        elif (a mod m) eq 1 then Append(~gens, c);
        end if;
    end for;
    if #gens eq 0 then return sub< C | Id(C) >; end if;
    return sub< C | gens >;
end function;

PrimeToPPartOfFiniteAbelianSubgroup := function(H, p)
    gens := [];
    for h in Generators(H) do
        n := Order(h); v := Valuation(n, p);
        Append(~gens, (p^v)*h);
    end for;
    if #gens eq 0 then return sub< H | Id(H) >; end if;
    return sub< H | gens >;
end function;

PPrimaryPartOfFiniteAbelianSubgroup := function(H, p)
    gens := [];
    for h in Generators(H) do
        n := Order(h); nprime := n div p^Valuation(n, p);
        Append(~gens, nprime*h);
    end for;
    if #gens eq 0 then return sub< H | Id(H) >; end if;
    return sub< H | gens >;
end function;

InertiaImageInBAtPrime := function(ebp, p)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; B := ebp`B;
    d := Exponent(G);
    I := CyclotomicInertiaAtPrime(C, f, d, p);
    imgs := [ phi(t) : t in Generators(I) ];
    if #imgs eq 0 then return sub< B | Id(B) >; end if;
    return sub< B | imgs >;
end function;

TameInertiaImageInBAtPrime := function(ebp, p)
    H := InertiaImageInBAtPrime(ebp, p);
    return PrimeToPPartOfFiniteAbelianSubgroup(H, p);
end function;

WildInertiaImageInBAtPrime := function(ebp, p)
    H := InertiaImageInBAtPrime(ebp, p);
    return PPrimaryPartOfFiniteAbelianSubgroup(H, p);
end function;

IsTamelyRamifiedInBAtPrime := function(ebp, p)
    Htame := TameInertiaImageInBAtPrime(ebp, p);
    Hwild := WildInertiaImageInBAtPrime(ebp, p);
    return (#Htame gt 1) and (#Hwild eq 1);
end function;

TamelyRamifiedPrimesForEbp := function(ebp)
    G := ebp`G; d := Exponent(G);
    primes := [];
    for q in Factorization(d) do
        p := q[1];
        if IsTamelyRamifiedInBAtPrime(ebp, p) then Append(~primes, p); end if;
    end for;
    return primes;
end function;

IsCyclotomicTameLocallyLiftableAtPrime := function(ebp, p)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; B := ebp`B;
    d := Exponent(G);
    xC := CyclotomicFrobeniusAtPrime(C, f, d, p);
    bX := phi(xC);
    Htame := TameInertiaImageInBAtPrime(ebp, p);
    Hwild := WildInertiaImageInBAtPrime(ebp, p);

    if #Htame eq 1 then return false, "Tame inertia image is trivial", <Id(G), Id(G)>; end if;
    if #Hwild gt 1 then return false, "Wild inertia image is nontrivial", <Id(G), Id(G)>; end if;
    if not IsCyclic(Htame) then return false, "Tame inertia image is not cyclic", <Id(G), Id(G)>; end if;

    gensHtame := [ h : h in Htame | Order(h) eq #Htame ];
    for h in gensHtame do
        bY := B!h;
        ok, msg, wit := IsLocalLiftableTameByBImages(ebp, p, bX, bY);
        if ok then return true, "Liftable for some tame inertia generator", wit; end if;
    end for;
    return false, "No generator of tame inertia image is locally liftable", <Id(G), Id(G)>;
end function;

IsLocallyLiftableAtAllTameFinitePlaces := function(ebp)
    primes := TamelyRamifiedPrimesForEbp(ebp);
    reports := [];
    for p in primes do
        ok, msg, wit := IsCyclotomicTameLocallyLiftableAtPrime(ebp, p);
        Append(~reports, <p, ok, msg>);
        if not ok then return false, reports; end if;
    end for;
    return true, reports;
end function;

IsRealLocallyLiftable := function(ebp)
    G := ebp`G; C := ebp`C; f := ebp`f; phi := ebp`phi; pi := ebp`pi;
    d := Exponent(G);
    found := false; cminus := Id(C);

    for c in C do
        a := UnitInteger(c, f);
        if (a mod d) eq ((-1) mod d) then
            found := true; cminus := c; break;
        end if;
    end for;

    if not found then return true, "No -1 element found", Id(G); end if;
    b := phi(cminus);

    for g in G do
        if pi(g) eq b and g^2 eq Id(G) then
            return true, "Real place liftable", g;
        end if;
    end for;
    return false, "Real place not liftable", Id(G);
end function;

IsLocallyLiftableTameAndReal := function(ebp)
    okFinite, finiteReports := IsLocallyLiftableAtAllTameFinitePlaces(ebp);
    okReal, realMsg, realWitness := IsRealLocallyLiftable(ebp);
    return okFinite and okReal, finiteReports, <okReal, realMsg>;
end function;

PassesCheckedLocalTests := function(ebp)
    ok, finiteReports, realReport := IsLocallyLiftableTameAndReal(ebp);
    return ok;
end function;

// =====================================================================
// 4. Optimized Orbit Counting & Data Prep 
// =====================================================================
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

ind := function(g)
    return Degree(Parent(g)) - &+[ c[2] : c in CycleStructure(g) ];
end function;

MinIndex := function(G)
    classes := Classes(G);
    min_ind := Degree(G);
    
    for i := 1 to #classes do 
        rep := classes[i][3];
        if rep ne Id(G) and ind(rep) lt min_ind then
            min_ind := ind(rep);
        end if;
    end for;
    
    Smin := {}; 
    for i := 1 to #classes do
        rep := classes[i][3];
        if rep ne Id(G) and ind(rep) eq min_ind then
            Smin join:= Conjugates(G, rep);
        end if;
    end for;
    
    return min_ind, Setseq(Smin);
end function;

bpiphi := function(ebp, Smin)
    G := ebp`G; C := ebp`C; pi := ebp`pi; phi := ebp`phi; f := ebp`f;
    N := Kernel(pi);
    Sminpi := { s : s in Smin | s in N };
    
    if IsEmpty(Sminpi) then return 0, 0; end if;

    action_pairs := [];
    for n in Generators(N) do Append(~action_pairs, <G!n, 1>); end for;
    for c in Generators(C) do
        b := phi(c);
        x_c := b @@ pi; 
        a_val := IntegerRing()!(f(c));
        Append(~action_pairs, <G!x_c, a_val>); 
    end for;

    visited := {};
    orbits := 0;
    
    for s in Sminpi do
        if s in visited then continue; end if;
        orbits +:= 1;
        queue := [s];
        Include(~visited, s);
        
        idx := 1;
        while idx le #queue do
            curr := queue[idx];
            idx +:= 1;
            for pair in action_pairs do
                x := pair[1]; a_val := pair[2];
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

SminIntersectionKerPi := function(ebp, Smin)
    pi := ebp`pi; N := Kernel(pi);
    Sminpi := [];
    for s in Smin do
        if s in N then Append(~Sminpi, s); end if;
    end for;
    return Sminpi;
end function;

IsTrivialQuotientEbp := function(ebp)
    return #ebp`B eq 1;
end function;

// =====================================================================
// 5. Full Check Function (Optimized Two-Phase Bound Evaluation)
// =====================================================================
FullCheck := function(G)
    a, Smin := MinIndex(G);
    T := Gpiphi(G);

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
                autoSolved, ebp1, N1, q1, H1, H2 := SplitReduction(ebp);
                ebp1_generated := true;
                
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
                        _, ebp1, _, _, _, _ := SplitReduction(ebp);
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

    R := rec< FullCheckResultFormat |
        group_order      := #G, minimal_index    := a,
        number_of_Smin   := #Smin, number_of_pairs  := #T,
        b_M              := bM, b_T              := bT,
        BW_lower_split   := BWlowerSplit, BW_upper_local   := BWupperLocal,
        split_candidates := splitCandidates, local_candidates := localCandidates
    >;

    return R;
end function;

// =====================================================================
// 6. Automated Output Generator
// =====================================================================
EvaluateDegreeBWBounds := procedure(n)
    filename := Sprintf("BW_Bounds_Degree_%o.txt", n);
    header := Sprintf("Evaluating b_W bounds for Transitive Groups of Degree %o\n==========================================\n", n);
    Write(filename, header : Overwrite := true);
    
    num_groups := NumberOfTransitiveGroups(n);
    print Sprintf("Starting bounds evaluation of %o groups for degree %o. Outputting to %o", num_groups, n, filename);
    print "--------------------------------------------------------------------------------";
    
    for i := 1 to num_groups do
        G := TransitiveGroup(n, i);
        R := FullCheck(G);
        
        result_str := Sprintf("Group %oT%o: b_M = %o, b_T = %o, BW_lower_split = %o, BW_upper_local = %o", 
            n, i, R`b_M, R`b_T, R`BW_lower_split, R`BW_upper_local);
        
        Write(filename, result_str);
        print result_str; 
        
        if R`BW_lower_split lt R`BW_upper_local then
            diff_str := "    ---> DIFFERENT! BW_lower_split < BW_upper_local";
            Write(filename, diff_str);
            print diff_str;
        end if;
    end for;
    
    print "==========================================";
    print "Finished! Bounds data saved to:", filename;
end procedure;

// =====================================================================
// 7. Command Line Execution
// =====================================================================
if assigned n then
    n_int := StringToInteger(n); 
    EvaluateDegreeBWBounds(n_int);
else
    print "Error: No degree specified. Run with: magma -b n:=<degree> script_name.m";
end if;
quit;
