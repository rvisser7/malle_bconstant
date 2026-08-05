// =====================================================================
// Orbit counting -- DISCRIMINANT ordering
// =====================================================================
//
// Verbatim from the discriminant-ordering source; unchanged byte-for-byte.
//
// Requires (load first): records.m, embedding_problems.m
//
// ind(g) = deg - #cycles(g). MinIndex cuts Smin down to the elements
// attaining the minimum; bpiphi then BFSes over ELEMENTS of Smin meet N,
// so the action has to include N's generators as well as the C ones.
// Contrast lib/prp/orbits.m, which BFSes over conjugacy classes.

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
