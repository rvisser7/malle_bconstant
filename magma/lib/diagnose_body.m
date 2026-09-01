// =====================================================================
// diagnose_body.m  --  sound vs legacy local policy, shared body
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering,
//                        i.e. load this LAST, exactly like driver.m.
//
// FullCheck must already exist when this procedure is DEFINED: Magma
// resolves free identifiers in a body at definition time.  That is also why
// the two entry points diagnose_disc.m and diagnose_prp.m are separate
// files rather than one file with an `ordering:=` switch -- `load` is a
// top-level directive and cannot appear inside an `if`.
//
// Recomputes each group's bracket under both
//
//   DefaultLocalPolicy   a failed tame test at p | #Ker(pi), and a failed
//                        pro-p test, count as UNDETERMINED rather than as a
//                        veto
//   LegacyLocalPolicy    both veto, as the pre-refactor code did
//
// and prints only the groups where the two disagree.  Run this BEFORE
// recomputing any published column: the disagreement set is exactly the set
// of cells whose upper bound was previously too small, hence the set of b_W
// values and status codes that may have to be withdrawn to \N.
//
// Also reports, per group:
//   undet     pairs admitted to the upper bound on an undetermined verdict
//   central   pairs that could have raised the lower bound, whose residual
//             is central, and which did not certify.  These are the ones a
//             complete local decision at every place would close.

DiagnoseIndices := procedure(n, indices, orderingName)
    printf "degree %o, ordering %o: sound vs legacy local policy\n", n, orderingName;
    print "label|b_M|b_T|sound_L|sound_U|legacy_L|legacy_U|undet|central";

    moved := 0;
    undetTotal := 0;
    centralTotal := 0;

    for i in indices do
        G := TransitiveGroup(n, i);
        Rs := FullCheck(G : Policy := DefaultLocalPolicy);
        Rl := FullCheck(G : Policy := LegacyLocalPolicy);

        undetTotal   +:= Rs`undetermined_local;
        centralTotal +:= Rs`central_residual_stalled;

        if Rs`BW_lower_split ne Rl`BW_lower_split or
           Rs`BW_upper_local ne Rl`BW_upper_local then
            moved +:= 1;
            printf "%oT%o|%o|%o|%o|%o|%o|%o|%o|%o\n",
                   n, i, Rs`b_M, Rs`b_T,
                   Rs`BW_lower_split, Rs`BW_upper_local,
                   Rl`BW_lower_split, Rl`BW_upper_local,
                   Rs`undetermined_local, Rs`central_residual_stalled;
        end if;
    end for;

    printf "%o of %o groups move under the correction\n", moved, #indices;
    printf "undetermined verdicts: %o;  stalled central residuals: %o\n",
           undetTotal, centralTotal;
end procedure;
