// =====================================================================
// Entry point: policy diagnostic, discriminant ordering
// =====================================================================
//
//     magma -b n:=12 [idxfile:=idx.txt] diagnose_disc.m
//
// Not a test: it measures how many published cells the local-policy
// correction changes.  See lib/diagnose_body.m for what the columns mean.
//
// Same load order as compute_disc.m, plus diagnose_body.m in place of
// driver.m.  `load` is top level only, which is why there is one of these
// per ordering rather than an `ordering:=` switch.

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
load "lib/disc/orbits.m";
load "lib/bw_phase2.m";
load "lib/disc/fullcheck.m";
load "lib/diagnose_body.m";

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
    DiagnoseIndices(n_int, indices, "disc");
else
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] diagnose_disc.m";
end if;
quit;
