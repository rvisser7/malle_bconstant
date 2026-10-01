// =====================================================================
// Entry point: per-pair verdict report, product-of-ramified-primes ordering
// =====================================================================
//
//     magma -b n:=20 i:=297 verdicts_prp.m
//
// See lib/verdict_report.m for how to read the output.  Same load order as
// compute_prp.m, with verdict_report.m in place of driver.m.

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
load "lib/prp/orbits.m";
load "lib/bw_phase2.m";
load "lib/prp/fullcheck.m";
load "lib/verdict_report.m";

if assigned n and assigned i then
    ReportVerdicts(StringToInteger(n), StringToInteger(i));
else
    print "Error: need both. Use: magma -b n:=<degree> i:=<index> verdicts_prp.m";
end if;
quit;
