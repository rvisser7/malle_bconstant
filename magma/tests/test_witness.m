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
//
// With slow:=1, also two RESIDUAL witnesses (degree-16 fields for
// G/O_5(G), see data/witnesses/README.md), each expected to give b_T:
//
//   20T397  Q16 field,  Gal(K/Q(sqrt5)) = C8   ->  b_witness = 2
//   20T396  QD16 field, Gal(K/Q(sqrt5)) = D8   ->  b_witness = 2

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


// Production verifier accepts the same field through a different transitive
// representation of the SAME ABSTRACT group (M = 1).  Find a degree-6
// transitive copy of S3 dynamically so the test does not hard-code the T-id.
s3six := 0;
for kk := 1 to NumberOfTransitiveGroups(6) do
    if IsIsomorphic(TransitiveGroup(6, kk), Sym(3)) then
        s3six := kk;
        break;
    end if;
end for;
if s3six eq 0 then
    print "  no degree-6 transitive S3 found -- unexpected";
    failures +:= 1;
else
    lab6 := Sprintf("6T%o", s3six);
    b, exact, bM, bT, ns, why := VerifyAnyWitness(lab6, [-2,0,0,1]);
    printf "  %o from cubic S3 field (alternate representation): b=%o b_M=%o b_T=%o (%o)\n",
           lab6, b, bM, bT, why;
    if b lt 0 or b gt bT or bM gt bT then failures +:= 1; end if;
end if;

// A verified witness can be injected before Phase 2.  6T5 has b_witness=b_T=2,
// so no certificate search is needed and the result records exact-intersection
// provenance from the witness rather than the standing b_M assumption.
Rw := FullCheck(TransitiveGroup(6, 5) : KnownLower := 2, KnownBM := 1, KnownBT := 2);
printf "  KnownLower fast path: BW=[%o,%o], exact lower=%o, assumption=%o\n",
       Rw`BW_lower_split, Rw`BW_upper_local, Rw`BW_lower_exact,
       Rw`lower_uses_bM_assumption;
if <Rw`BW_lower_split, Rw`BW_upper_local, Rw`BW_lower_exact,
    Rw`lower_uses_bM_assumption> ne <2,2,2,false> then
    failures +:= 1;
end if;

// witnesses.txt is data, not executable Magma.
parsed := WitnessParseCoeffs(" [4, 0, 0, -2, 0, 0, 1] ");
printf "  coefficient parser: %o\n", parsed;
if parsed ne [4,0,0,-2,0,0,1] then failures +:= 1; end if;

badparse := false;
try
    _ := WitnessParseCoeffs("[1,1+1,1]");
catch err
    badparse := true;
end try;
printf "  executable coefficient input rejected = %o\n", badparse;
if not badparse then failures +:= 1; end if;

// Regression for the residual F = Q path.  x^3-x-1 has Galois group S3 and
// does not contain Q(mu_3).  Its order divides #A4, but S3 is not a quotient
// of A4.  It must therefore be rejected, not accepted early as a trivial-pair
// residual witness for 4T4 = A4.
badresidual := false;
try
    _ := VerifyResidualWitness("4T4", [-1,-1,0,1]);
catch err
    badresidual := true;
end try;
printf "  unrelated residual group with F=Q rejected = %o\n", badresidual;
if not badresidual then failures +:= 1; end if;

if assigned slow then
    for c in [
        < "20T397", [111045689000000,-171736784000000,95714448000000,-18991071640000,
                     -1939992521000,1253116572000,-76821581400,-26955558320,3083021051,
                     283142072,-42555092,-1642576,281220,5424,-872,-8,1], 2 >,
        < "20T396", [15625,0,-37500,0,40500,0,-23000,0,8075,0,-1800,0,260,0,-20,0,1], 2 >
    ] do
        b, exact, bM, bT, ns, why := VerifyResidualWitness(c[1], c[2]);
        printf "  %o residual: b=%o exact=%o b_M=%o b_T=%o (%o)\n", c[1], b, exact, bM, bT, why;
        if b ne c[3] or bT ne c[3] then failures +:= 1; end if;
    end for;
else
    print "  (skipping the residual witnesses: slow; run with slow:=1)";
end if;

printf "test_witness: %o failures\n", failures;
assert failures eq 0;
print "test_witness: PASS";
quit;
