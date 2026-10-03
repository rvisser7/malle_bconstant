// =====================================================================
// Entry point: supplement-certificate diagnostic, discriminant ordering
// =====================================================================
//
//     magma -b n:=12 [idxfile:=idx.txt] [depth:=1] diagnose_supplements_disc.m
//
// Not a test.  Recomputes each open bracket with the supplement step of
// certify.m switched on and prints the groups whose lower bound rises.
// See lib/supplement_body.m.

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
load "lib/disc/orbits.m";
load "lib/bw_phase2.m";
load "lib/disc/fullcheck.m";
load "lib/supplement_body.m";

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
    dep := assigned depth select StringToInteger(depth) else 1;
    DiagnoseSupplementIndices(n_int, indices, "disc", dep);
else
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] [depth:=1] diagnose_supplements_disc.m";
end if;
quit;
