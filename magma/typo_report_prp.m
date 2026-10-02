// =====================================================================
// Entry point: effect of the reversed-action typo, prp ordering
// =====================================================================
//
//     magma -b n:=12 [idxfile:=idx.txt] typo_report_prp.m
//
// One line per group: the correct bracket [L, U], the bracket the reversed
// action would have produced, how many pairs have b(pi,phi) != b(pi,-phi),
// and whether the bracket differs.  See lib/typo_report_body.m.

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
load "lib/typo_report_body.m";

if assigned n then
    n_int := StringToInteger(n);
    if assigned idxfile then
        raw := Read(idxfile);
        indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
    else
        indices := [1 .. NumberOfTransitiveGroups(n_int)];
    end if;
    TypoReport(n_int, indices);
else
    print "Use: magma -b n:=<degree> [idxfile:=<path>] typo_report_prp.m";
end if;
quit;
