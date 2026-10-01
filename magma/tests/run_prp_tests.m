// =====================================================================
// tests/run_prp_tests.m  --  regression against Wang's worked examples
// =====================================================================
//
//     magma -b tests/run_prp_tests.m    (run from magma/)
//
// b_M and b_T are asserted exactly: they are pure orbit counts and must not
// move.  b_W is asserted only as a bracket b_M <= L <= U <= b_T, since the
// bracket legitimately widens or narrows as certificates and local policy
// change.

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

// <degree, index, expected b_M, expected b_T, source>
CASES := [
    < 6, 5,     5,  5, "C3 wr C2: hand count, 3 orbits inside N plus 2 outside" >,
    <12, 131,  19, 29, "C3 wr C4, Wang Example 3.5: b_M^rad = 19, b_T^rad = 29" >,
    <16, 1192, 50, 79, "C4 wr C4, Wang Example 3.6: largest b(pi,phi) = 79 at Q(i). SLOW" >
];

failures := 0;

for c in CASES do
    n := c[1]; i := c[2]; expM := c[3]; expT := c[4];
    G := TransitiveGroup(n, i);
    R := FullCheck(G);

    printf "  %oT%o: b_M=%o b_T=%o BW=[%o,%o] undet=%o central_stalled=%o\n",
           n, i, R`b_M, R`b_T, R`BW_lower_split, R`BW_upper_local,
           R`undetermined_local, R`central_residual_stalled;

    if R`b_M ne expM or R`b_T ne expT then
        printf "    FAIL: expected b_M=%o b_T=%o  [%o]\n", expM, expT, c[5];
        failures +:= 1;
    end if;
    if not (R`b_M le R`BW_lower_split and
            R`BW_lower_split le R`BW_upper_local and
            R`BW_upper_local le R`b_T) then
        print "    FAIL: bracket out of order";
        failures +:= 1;
    end if;
end for;

printf "run_prp_tests: %o failures\n", failures;
assert failures eq 0;
print "run_prp_tests: PASS";
quit;
