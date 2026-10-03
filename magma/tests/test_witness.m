// =====================================================================
// tests/test_witness.m  --  witness-field verification (disc ordering)
// =====================================================================
//
//     magma -b tests/test_witness.m      (run from magma/)
//
// Small fields whose answers are known by hand:
//
//   x^6 - 2x^3 + 4   6T5 = C3 wr C2 (Kluners).  Its roots are cube roots of
//                    1 +- sqrt(-3), so K~ contains Q(sqrt -3) = Q(mu_3), and
//                    d = 3 for disc.  It witnesses b_W >= 2 = b_T.
//   x^3 - 2          3T2 = S3.  Disc d = 2, so Q(mu_d) = Q: only the
//                    trivial pair, b_witness = b_M = 1.
//   x^3 - 2 as 3T1   wrong label: must be reported as an error.

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
load "lib/driver.m";
load "lib/witness_body.m";

failures := 0;

b, exact, bM, bT, ns, why := VerifyWitness("6T5", [4,0,0,-2,0,0,1]);
printf "  6T5  x^6-2x^3+4: b=%o exact=%o b_M=%o b_T=%o (%o)\n", b, exact, bM, bT, why;
if <b, exact, bM, bT> ne <2, true, 1, 2> then failures +:= 1; end if;

b, exact, bM, bT, ns, why := VerifyWitness("3T2", [-2,0,0,1]);
printf "  3T2  x^3-2:       b=%o exact=%o b_M=%o b_T=%o (%o)\n", b, exact, bM, bT, why;
if <b, exact, bM, bT> ne <1, true, 1, 1> then failures +:= 1; end if;

raised := false;
try
    _ := VerifyWitness("3T1", [-2,0,0,1]);
catch err
    raised := true;
end try;
printf "  3T1  x^3-2 (wrong label): error raised = %o\n", raised;
if not raised then failures +:= 1; end if;

printf "test_witness: %o failures\n", failures;
assert failures eq 0;
print "test_witness: PASS";
quit;
