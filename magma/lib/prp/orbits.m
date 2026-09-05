// =====================================================================
// Orbit counting -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
// Requires (load first): records.m, embedding_problems.m
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

// Per-pi data, computed once and reused for every phi over that pi.
KernelCtx := recformat<
    N, classes, cm, id_idx, nclasses,
    Cgens,          // generators of C, in a fixed order
    powperm,        // powperm[k] = P_{a_k} for the k-th generator of C
    conjperm,       // conjperm[j] = C_{x_j} for the j-th generator of B
    Bgens           // generators of B, in the matching order
>;

MakeKernelCtx := function(ebp)
    N := Kernel(ebp`pi);
    if #N eq 1 then
        return rec< KernelCtx | N := N >;
    end if;

    G := ebp`G; B := ebp`B; C := ebp`C; f := ebp`f; pi := ebp`pi;
    cls := Classes(N);
    cm  := ClassMap(N);
    K   := #cls;

    Cgens := [ c : c in Generators(C) ];
    powperm := [];
    for k := 1 to #Cgens do
        a := IntegerRing()!(f(Cgens[k]));
        Append(~powperm, [ cm((cls[i][3])^a) : i in [1..K] ]);
    end for;

    Bgens := [ B.j : j in [1..Ngens(B)] ];
    conjperm := [];
    for j := 1 to #Bgens do
        x := Bgens[j] @@ pi;
        xg := G!x;
        Append(~conjperm, [ cm(xg^(-1) * (cls[i][3]) * xg) : i in [1..K] ]);
    end for;

    return rec< KernelCtx |
        N := N, classes := cls, cm := cm, id_idx := cm(Id(N)), nclasses := K,
        Cgens := Cgens, powperm := powperm,
        conjperm := conjperm, Bgens := Bgens >;
end function;

// C_b for an arbitrary b in B, as a product of the cached generator
// permutations. Pure array work: no ClassMap evaluations.
ConjPermForB := function(ctx, b)
    K := ctx`nclasses;
    perm := [ i : i in [1..K] ];
    e := Eltseq(b);
    for j := 1 to Minimum(#e, #ctx`conjperm) do
        m := e[j] mod Order(ctx`Bgens[j]);
        for t := 1 to m do
            perm := [ ctx`conjperm[j][perm[i]] : i in [1..K] ];
        end for;
    end for;
    return perm;
end function;

bpiphiCtx := function(ebp, ctx)
    N := ctx`N;
    if #N eq 1 then return 0, 0; end if;

    phi := ebp`phi;
    K := ctx`nclasses;

    // One permutation per generator of C: power, then conjugate.
    actperms := [];
    for k := 1 to #ctx`Cgens do
        cp := ConjPermForB(ctx, phi(ctx`Cgens[k]));
        pp := ctx`powperm[k];
        Append(~actperms, [ cp[pp[i]] : i in [1..K] ]);
    end for;

    visited := [ false : i in [1..K] ];
    visited[ctx`id_idx] := true;
    orbits := 0;

    for i := 1 to K do
        if visited[i] then continue; end if;
        orbits +:= 1;
        queue := [i];
        idx := 1;
        while idx le #queue do
            curr := queue[idx];
            idx +:= 1;
            for p in actperms do
                nxt := p[curr];
                if not visited[nxt] then
                    visited[nxt] := true;
                    Append(~queue, nxt);
                end if;
            end for;
        end while;
    end for;

    // We return (#N - 1) as the size of the set we evaluated
    return (#N - 1), orbits;
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
