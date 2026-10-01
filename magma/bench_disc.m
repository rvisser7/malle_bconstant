// =====================================================================
// Entry point: timing breakdown, discriminant ordering
// =====================================================================
//
//     magma -b n:=15 [idxfile:=idx.txt] bench_disc.m
//
// Prints per-group Phase 1 / Phase 2 seconds. See lib/bench_body.m.

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
load "lib/bench_body.m";

if assigned n then
    n_int := StringToInteger(n);
    if assigned idxfile then
        raw := Read(idxfile);
        indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
    else
        indices := [1 .. NumberOfTransitiveGroups(n_int)];
    end if;
    BenchIndices(n_int, indices);
else
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] bench_disc.m";
end if;
quit;
