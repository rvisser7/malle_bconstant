// =====================================================================
// Orbit counting -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
// Class-based BFS. Under the prp ordering every non-identity element has
// index 1, so Smin is all of G minus the identity and Smin meet Ker(pi) is
// just N minus the identity. There is therefore no ind / MinIndex /
// SminIntersectionKerPi here: the disc versions of those three exist only
// to cut Smin down, and under prp there is nothing to cut.
//
// The optimisation that matters: orbits are computed on the CONJUGACY
// CLASSES of N via ClassMap, not on its elements. N-conjugation is quotiented
// out by working with classes, so the action only needs the C generators,
// where the disc version also has to push N's generators through.
//
// Requires (load first): records.m, embedding_problems.m

// Orbit counting via BFS acting purely on Conjugacy Classes of N
bpiphi := function(ebp)
    G := ebp`G; C := ebp`C; pi := ebp`pi; phi := ebp`phi; f := ebp`f;
    N := Kernel(pi);
    
    if #N eq 1 then return 0, 0; end if;

    N_classes := Classes(N);
    cm := ClassMap(N);
    id_idx := cm(Id(N));
    
    action_maps := [];
    for c in Generators(C) do
        b := phi(c);
        x_c := b @@ pi; 
        a_val := IntegerRing()!(f(c));
        Append(~action_maps, <G!x_c, a_val>); 
    end for;

    visited := {};
    orbits := 0;
    
    all_indices := { 1 .. #N_classes } diff { id_idx };
    
    for i in all_indices do
        if i in visited then continue; end if;
        orbits +:= 1;
        
        queue := [i];
        Include(~visited, i);
        
        idx := 1;
        while idx le #queue do
            curr_idx := queue[idx];
            idx +:= 1;
            
            rep := N_classes[curr_idx][3];
            
            for pair in action_maps do
                x_c := pair[1]; 
                a_val := pair[2];
                
                next_el := x_c^(-1) * (rep^a_val) * x_c;
                next_idx := cm(next_el);
                
                if not (next_idx in visited) then
                    Include(~visited, next_idx);
                    Append(~queue, next_idx);
                end if;
            end for;
        end while;
    end for;
    
    // We return (#N - 1) as the size of the set we evaluated
    return (#N - 1), orbits;
end function;
