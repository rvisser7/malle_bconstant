// =====================================================================
// Entry point: p = 2 marking diagnostic, product-of-ramified-primes ordering
// =====================================================================
//
//     magma -b n:=16 [idxfile:=idx.txt] diagnose_marking_prp.m
//
// Not a test.  Reports every pair whose p = 2 wild verdict could depend on
// the one unverified part of the Demushkin marking in wild_prop.m (the
// unramified exponent of x2).  See lib/marking_body.m.

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/local_tame.m";
load "lib/wild_prop.m";
load "lib/local_verdict.m";
load "lib/certificates/shared.m";
load "lib/certificates/structural.m";
load "lib/certificates/central.m";
load "lib/certificates/q8.m";
load "lib/certify.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/prp/orbits.m";
load "lib/bw_phase2.m";
load "lib/prp/fullcheck.m";
load "lib/marking_body.m";

// ---------------------------------------------------------------------
// Command line, at TOP LEVEL: `assigned` is only reliable here.
// ---------------------------------------------------------------------
if assigned n then
    n_int := StringToInteger(n);
    if assigned idxfile then
        raw := Read(idxfile);
        indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
    else
        indices := [1 .. NumberOfTransitiveGroups(n_int)];
    end if;
    DiagnoseMarkingIndices(n_int, indices, "prp");
else
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] diagnose_marking_prp.m";
end if;
quit;
