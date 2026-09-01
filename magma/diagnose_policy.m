// =====================================================================
// diagnose_policy.m  --  how much does the local-policy correction move?
// =====================================================================
//
//     magma -b n:=12 ordering:=disc [idxfile:=idx.txt] diagnose_policy.m
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

if not assigned n then
    print "Usage: magma -b n:=<degree> ordering:=<disc|prp> [idxfile:=path] diagnose_policy.m";
    quit;
end if;
if not assigned ordering then ordering := "disc"; end if;

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

if ordering eq "prp" then
    load "lib/prp/orbits.m";
    load "lib/bw_phase2.m";
    load "lib/prp/fullcheck.m";
else
    load "lib/disc/orbits.m";
    load "lib/bw_phase2.m";
    load "lib/disc/fullcheck.m";
end if;

n_int := StringToInteger(n);
if assigned idxfile then
    raw := Read(idxfile);
    indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
else
    indices := [1 .. NumberOfTransitiveGroups(n_int)];
end if;

printf "degree %o, ordering %o: sound vs legacy local policy\n", n_int, ordering;
print "label|b_M|b_T|sound_L|sound_U|legacy_L|legacy_U|undet|central";

moved := 0;
for i in indices do
    G := TransitiveGroup(n_int, i);
    Rs := FullCheck(G : Policy := DefaultLocalPolicy);
    Rl := FullCheck(G : Policy := LegacyLocalPolicy);

    if Rs`BW_lower_split ne Rl`BW_lower_split or
       Rs`BW_upper_local ne Rl`BW_upper_local then
        moved +:= 1;
        printf "%oT%o|%o|%o|%o|%o|%o|%o|%o|%o\n",
               n_int, i, Rs`b_M, Rs`b_T,
               Rs`BW_lower_split, Rs`BW_upper_local,
               Rl`BW_lower_split, Rl`BW_upper_local,
               Rs`undetermined_local, Rs`central_residual_stalled;
    end if;
end for;

printf "%o of %o groups move under the correction\n", moved, #indices;
quit;
