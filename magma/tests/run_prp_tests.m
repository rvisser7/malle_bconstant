// =====================================================================
// tests/run_prp_tests.m  --  regression against Wang's worked examples
// =====================================================================
//
//     magma -b tests/run_prp_tests.m    (run from magma/)
//
// b_M and b_T are asserted exactly: they are pure orbit counts and must not
// move.  b_W is asserted exactly ONLY where it is proven (Wang Theorem 1.3
// with the 2-part corrected, or a direct argument noted beside the case):
// the test fails if that value lies outside the bracket [L, U], and merely
// reports if the bracket has not collapsed onto it.  Elsewhere only
// b_M <= L <= U <= b_T is asserted.
//
// Groups are built from their structure (WreathProduct), not from a
// hard-coded TransitiveGroup index: the old fixture "20T27 = C5 wr C4" was
// not C5 wr C4 at all (its prp b_M is 6; C5 wr C4 has b_M^rad = 51), and the
// disc values happened to coincide, so the test passed without testing what
// it claimed.
//
// Run with slow:=1 to include the large cases.

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

W := func< l, m | WreathProduct(CyclicGroup(l), CyclicGroup(m)) >;

// < group, name, expected b_M, expected b_T, proven b_W (-1 = none),
//   source, slow? >
CASES := [*
    < W(3, 2), "C3 wr C2", 5, 5, 5,
      "hand count, 3 orbits inside N plus 2 outside; b_M = b_T", false >,
    < W(3, 4), "C3 wr C4", 19, 29, -1,
      "Wang Example 3.5: b_M^rad = 19, b_T^rad = 29 (Conj. 6 predicts 19)", false >,
    < W(5, 4), "C5 wr C4", 51, 164, -1,
      "independent brute force: b_M^rad = 51, max b(pi,phi) = 164 at Q(mu_5)", false >,
    < W(4, 4), "C4 wr C4", 50, 79, -1,
      "Wang Example 3.6: largest b(pi,phi) = 79 at Q(i)", true >,
    < TransitiveGroup(15, 95), "15T95 = A5^3 : C6", 45, 49, 49,
      "only pair above b_M: F = Q(sqrt 5); A5^3 is a GAR layer "
      cat "[MM99 IV.3.5], residual C6 -> C2 splits.  Exact intersection "
      cat "holds: G^ab = C6, so K cap Q(mu_180) is the C6 field Q(sqrt 5) E "
      cat "cut down, and E can be any cyclic cubic, e.g. conductor 7", true >
*];

Label := function(G)
    try
        i, n := TransitiveGroupIdentification(G);
        return Sprintf("%oT%o", n, i);
    catch e
        return Sprintf("degree %o, order %o", Degree(G), #G);
    end try;
end function;

runSlow := assigned slow;
failures := 0;

for c in CASES do
    if c[7] and not runSlow then
        printf "  (skipping %o: slow; run with slow:=1)\n", c[2];
        continue;
    end if;
    G := c[1];
    R := FullCheck(G);
    L := R`BW_lower_split; U := R`BW_upper_local;

    printf "  %o [%o]: b_M=%o b_T=%o BW=[%o,%o] undet=%o central_stalled=%o\n",
           c[2], Label(G), R`b_M, R`b_T, L, U,
           R`undetermined_local, R`central_residual_stalled;

    if R`b_M ne c[3] or R`b_T ne c[4] then
        printf "    FAIL: expected b_M=%o b_T=%o  [%o]\n", c[3], c[4], c[6];
        failures +:= 1;
    end if;
    if not (R`b_M le L and L le U and U le R`b_T) then
        print "    FAIL: bracket out of order";
        failures +:= 1;
    end if;
    if c[5] ge 0 then
        if c[5] lt L or c[5] gt U then
            printf "    FAIL: proven b_W = %o lies outside [%o,%o]  [%o]\n", c[5], L, U, c[6];
            failures +:= 1;
        elif L ne U then
            printf "    note: proven b_W = %o, bracket not yet collapsed\n", c[5];
        end if;
    end if;
end for;

printf "run_prp_tests: %o failures\n", failures;
assert failures eq 0;
print "run_prp_tests: PASS";
quit;
