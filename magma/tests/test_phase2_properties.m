// =====================================================================
// tests/test_phase2_properties.m
// =====================================================================
//
//     magma -b tests/test_phase2_properties.m      (run from magma/)
//
// Property-style checks for Phase 2: pair enumeration order must not matter,
// a verified KnownLower=b_T must be an immediate exact answer, and stale or
// impossible witness metadata must be rejected.

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

failures := 0;
G := TransitiveGroup(6, 5);
d, _, _, _, bM, bT, pairs := EvaluatePairs(G);
rev := [* pairs[#pairs-k+1] : k in [1..#pairs] *];
L1, U1, _, _, _, _ := BWBoundsFromPairs(d, pairs, bM, bT, DefaultLocalPolicy);
L2, U2, _, _, _, _ := BWBoundsFromPairs(d, rev,   bM, bT, DefaultLocalPolicy);
printf "  order invariance: [%o,%o] vs [%o,%o]\n", L1, U1, L2, U2;
if <L1,U1> ne <L2,U2> then failures +:= 1; end if;

R := FullCheck(G : KnownLower := bT, KnownBM := bM, KnownBT := bT);
printf "  KnownLower=b_T: [%o,%o], exact=%o\n",
       R`BW_lower_split, R`BW_upper_local, R`BW_lower_exact;
if <R`BW_lower_split,R`BW_upper_local,R`BW_lower_exact> ne <bT,bT,bT> then
    failures +:= 1;
end if;

badBM := false;
try
    _ := FullCheck(G : KnownLower := 1, KnownBM := bM+1, KnownBT := bT);
catch e
    badBM := true;
end try;
badBT := false;
try
    _ := FullCheck(G : KnownLower := 1, KnownBM := bM, KnownBT := bT+1);
catch e
    badBT := true;
end try;
badLower := false;
try
    _ := FullCheck(G : KnownLower := bT+1, KnownBM := bM, KnownBT := bT);
catch e
    badLower := true;
end try;
printf "  stale witness guards: bM=%o bT=%o lower=%o\n", badBM, badBT, badLower;
if not (badBM and badBT and badLower) then failures +:= 1; end if;

printf "test_phase2_properties: %o failures\n", failures;
assert failures eq 0;
print "test_phase2_properties: PASS";
quit;
