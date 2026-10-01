// =====================================================================
// Orbit counting -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m, class_orbits.m
//
// Under the prp ordering every non-identity element has index 1, so Smin is
// all of G minus the identity and Smin meet Ker(pi) is just N minus the
// identity. There is therefore no ind / MinIndex / SminIntersectionKerPi
// here: the disc versions of those exist only to cut Smin down.
//
// Orbits are counted on the CONJUGACY CLASSES of N, which quotients out
// N-conjugation, so the action only needs the C generators where the disc
// version also has to push N's generators through.
//
// WHERE THE TIME WENT.  The class-based BFS is right but was paying a
// ClassMap evaluation per class, per generator of C, per PAIR. On a kernel
// of order in the millions that dominates everything: 24T24040 spent about
// forty hours in Phase 1 and none in Phase 2.
//
// The twisted action (x, a) : y -> x^-1 y^a x splits into two permutations
// of the class indices, and both are cacheable:
//
//   POWERING  P_a : i -> class of rep_i^a.  Depends only on a = f(c), which
//             is a property of the generator c of C, not of phi.
//
//   CONJUGATION  C_x : i -> class of x^-1 rep_i x.  Depends only on the
//             coset xN, i.e. only on b = phi(c) in B, because conjugating by
//             an element of N fixes every class of N. And C is an
//             anti-homomorphism, C_{x1x2} = C_{x2} . C_{x1}, so it is enough
//             to build it for preimages of the GENERATORS of B and compose;
//             any preimage of a given b gives the same permutation, so the
//             order of composition does not matter either.
//
// Conjugation is an automorphism, so x^-1 rep^a x = (x^-1 rep x)^a and the
// two commute: the action of one generator of C is the single permutation
// i -> C_b(P_a(i)), built once per pair from cached pieces.
//
// So per pi we pay (Ngens(B) + Ngens(C)) * #classes ClassMap evaluations,
// once, and every pair after that is integer array lookups. The visited set
// is a boolean sequence rather than a set of integers for the same reason.

// Per-pi data, computed once and reused for every phi over that pi.  The
// machinery (and the explanation above of why it is cacheable) now lives in
// lib/class_orbits.m, shared with the disc ordering; prp counts every
// non-identity class of N.
MakeKernelCtx := function(ebp)
    return MakeClassOrbitCtx(ebp, func< g | Order(g) gt 1 >);
end function;

// Returns (#N - 1, number of orbits), as before.
bpiphiCtx := function(ebp, ctx)
    n, b := ClassOrbitCount(ebp, ctx);
    return n, b;
end function;

// ---------------------------------------------------------------------
// Reference implementation: the original BFS, calling ClassMap inside the
// inner loop and rebuilding its kernel data from scratch. Not used in
// production. tests/test_orbits_agree_prp.m checks bpiphiCtx against THIS,
// pair by pair, so the comparison is against the old algorithm and not
// against a wrapper round the new one.
// ---------------------------------------------------------------------
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

    return (#N - 1), orbits;
end function;
