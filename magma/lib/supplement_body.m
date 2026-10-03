// =====================================================================
// supplement_body.m  --  what would the supplement certificate add?
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering,
//                        i.e. load this LAST, exactly like driver.m.
//
// The supplement step in certify.m is OFF by default (SupplementDepth := 0)
// so that published numbers do not move silently.  This recomputes each
// group with SupplementDepth := depth (default 1) and prints only the
// groups whose bracket changes.  Since the step can only certify MORE pairs,
// a change can only raise L; U is printed as a sanity check and must not
// move.
//
// Use it on the open brackets (rows with \N in the wang column) first.

DiagnoseSupplementIndices := procedure(n, indices, orderingName, depth)
    printf "degree %o, ordering %o: supplement certificate, depth %o\n",
           n, orderingName, depth;
    print "label|b_M|b_T|L0|U0|L1|U1";
    raised := 0;
    for i in indices do
        G := TransitiveGroup(n, i);
        R0 := FullCheck(G);
        if R0`BW_lower_split eq R0`BW_upper_local then continue; end if;
        R1 := FullCheck(G : SupplementDepth := depth);
        if R1`BW_lower_split ne R0`BW_lower_split
           or R1`BW_upper_local ne R0`BW_upper_local then
            printf "%oT%o|%o|%o|%o|%o|%o|%o\n", n, i, R0`b_M, R0`b_T,
                   R0`BW_lower_split, R0`BW_upper_local,
                   R1`BW_lower_split, R1`BW_upper_local;
            assert R1`BW_upper_local eq R0`BW_upper_local;
            raised +:= 1;
            for c in R1`split_candidates do
                printf "    certificate: %o\n", c`certificate;
            end for;
        end if;
    end for;
    printf "TOTAL raised: %o\n", raised;
end procedure;
