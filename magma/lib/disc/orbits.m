// =====================================================================
// Orbit counting -- DISCRIMINANT ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, class_orbits.m
//
// ind(g) = deg - #cycles(g).  The production path now works on conjugacy
// classes, exactly like the prp ordering: see lib/class_orbits.m.  The only
// disc-specific input is the keep predicate ind(g) = ind(G).
//
// Previously this file materialised every element of Smin (MinIndex), took
// an LCM over all of them, and for every pi tested each one for membership
// in Ker(pi) before a BFS over ELEMENTS.  MinIndexClasses gets a, d and
// #Smin from the classes of G instead, and nothing element-sized is built.
//
// MinIndex and bpiphi (the element versions) are kept as the reference
// implementation that tests/test_orbits_agree_disc.m compares against, and
// for the diagnostics that still call them.  They are not used in
// production.

ind := function(g)
    return Degree(Parent(g)) - &+[ c[2] : c in CycleStructure(g) ];
end function;

// Production: a = ind(G), the minimal-index classes (representatives),
// #Smin, and d = lcm of the orders of the minimal-index elements.
MinIndexClasses := function(G)
    cls := [ c : c in Classes(G) | c[1] gt 1 ];
    if #cls eq 0 then
        // trivial group: matches the old MinIndex (a = degree, Smin empty)
        return Degree(G), [], 0, 1;
    end if;
    inds := [ ind(c[3]) : c in cls ];
    a := Minimum(inds);
    mins := [ cls[k] : k in [1..#cls] | inds[k] eq a ];
    reps := [ c[3] : c in mins ];
    return a, reps, &+[ c[2] : c in mins ], LCM([ c[1] : c in mins ]);
end function;

// Per-pi context.  Second argument is the minimal index a.
MakeKernelCtx := function(ebp, a)
    return MakeClassOrbitCtx(ebp, func< g | ind(g) eq a >);
end function;

bpiphiCtx := function(ebp, ctx)
    n, b := ClassOrbitCount(ebp, ctx);
    return n, b;
end function;

// ---------------------------------------------------------------------
// Reference implementation (elements, not classes).  Not used in
// production.
// ---------------------------------------------------------------------
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
        x_c := phi(c) @@ pi;
        Append(~action_pairs, <G!x_c, IntegerRing()!(f(c))>);
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
                next_s := pair[1]^(-1) * (curr^pair[2]) * pair[1];
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
    N := Kernel(ebp`pi);
    return [ s : s in Smin | s in N ];
end function;
