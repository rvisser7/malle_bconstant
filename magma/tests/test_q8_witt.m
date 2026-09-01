// =====================================================================
// tests/test_q8_witt.m
// =====================================================================
//
//     magma -b tests/test_q8_witt.m        (run from magma/)
//
// The Q8 file used to assert, in a comment, that its closed-form criterion
// for "Q(sqrt a) lies in some Q8-extension" had been checked against a brute
// force search over the auxiliary b for every squarefree a < 200.  A claim
// in a comment is not a check.  This is the check.
//
// Directions are not symmetric.  If brute force finds a witness b and the
// criterion says no, the criterion is WRONG and the test fails.  If the
// criterion says yes and brute force finds nothing, that is only evidence
// the search bound is too small, so it warns.

load "lib/records.m";
load "lib/certificates/shared.m";
load "lib/certificates/q8.m";

ABOUND := 200;
BBOUND := 500;

printf "test_q8_witt: criterion vs brute force, a < %o, b < %o\n", ABOUND, BBOUND;

failures := 0;
warnings := 0;
checked  := 0;

for a in [2..ABOUND] do
    if not IsSquarefree(a) then continue; end if;
    checked +:= 1;

    crit := QuadraticInQ8(a);

    brute := false;
    witness := 0;
    for b in [2..BBOUND] do
        if not IsSquarefree(b) then continue; end if;
        if b eq a then continue; end if;
        if WittEmbeds(a, b) then
            brute := true; witness := b; break;
        end if;
    end for;

    if brute and not crit then
        printf "  FAIL a=%o: Witt(%o,%o) holds but the criterion says no\n", a, a, witness;
        failures +:= 1;
    elif crit and not brute then
        printf "  warn a=%o: criterion says yes, no b < %o found\n", a, BBOUND;
        warnings +:= 1;
    end if;
end for;

// Spot values quoted in the old comment.
assert not QuadraticInQ8(7);
assert QuadraticInQ8(2);
assert QuadraticInQ8(3);
assert QuadraticInQ8(5);

printf "  %o squarefree a checked, %o failures, %o warnings\n",
       checked, failures, warnings;
assert failures eq 0;
print "test_q8_witt: PASS";
quit;
