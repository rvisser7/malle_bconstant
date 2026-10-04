// =====================================================================
// tests/test_local_verdict_fixtures.m
// =====================================================================
//
//     magma -b tests/test_local_verdict_fixtures.m      (run from magma/)
//
// Small arithmetic fixtures for the three-valued local logic and the central
// local-global certificate.  They avoid large wreath products while encoding
// the same elementary obstructions used in Wang's examples.
//
//   C4 -> C2, F = Q(sqrt 5) inside Q(mu_5): liftable (Q(zeta_5)).
//   C4 -> C2, F = Q(i)      inside Q(mu_4): obstructed at infinity.
//   C8 -> C2, F = Q(sqrt 5): obstructed at 5; a tame C8 inertia lift would
//                             have order 8, impossible over Q_5.

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/local_tame.m";
load "lib/wild_prop.m";
load "lib/local_verdict.m";
load "lib/certificates/shared.m";
load "lib/certificates/central.m";
load "lib/embedding_problems.m";

KernelResidues := function(ebp)
    r := [ (IntegerRing()!ebp`f(c)) mod ebp`d : c in Kernel(ebp`phi) ];
    Sort(~r);
    return r;
end function;

FindQuadraticPair := function(G, d, residues)
    T, _ := Gpiphi(G, d);
    for ebp in T do
        if #ebp`B eq 2 and KernelResidues(ebp) eq residues then
            return ebp;
        end if;
    end for;
    error Sprintf("quadratic pair with kernel residues %o mod %o not found", residues, d);
end function;

failures := 0;

// Q(sqrt 5) in a cyclic quartic extension.
e5 := FindQuadraticPair(CyclicGroup(4), 5, [1,4]);
v5, _ := LocalVerdict(e5, DefaultLocalPolicy);
ok5, why5 := CertifyCentralResidual(e5, DefaultLocalPolicy);
printf "  C4 -> C2, Q(sqrt5): local=%o central=%o (%o)\n", v5, ok5, why5;
if v5 ne LocalVerdictYes or not ok5 then failures +:= 1; end if;

// Q(i) cannot be the quadratic subfield of a cyclic quartic extension: the
// non-trivial quotient coset has no involution, so the real place obstructs.
ei := FindQuadraticPair(CyclicGroup(4), 4, [1]);
vinf, msginf := LocalVerdictAtRealPlace(ei);
oki, whyi := CertifyCentralResidual(ei, DefaultLocalPolicy);
printf "  C4 -> C2, Q(i): real=%o (%o), central=%o (%o)\n",
       vinf, msginf, oki, whyi;
if vinf ne LocalVerdictNo or oki then failures +:= 1; end if;

// Q(sqrt5) cannot lie in a cyclic C8-extension.  Here 5 does not divide the
// kernel C4, so a failed tame test is an exact No (not Unknown).
e8 := FindQuadraticPair(CyclicGroup(8), 5, [1,4]);
v8, msg8 := LocalVerdictAtPrime(e8, 5, DefaultLocalPolicy);
printf "  C8 -> C2, Q(sqrt5) at 5: verdict=%o (%o)\n", v8, msg8;
if v8 ne LocalVerdictNo then failures +:= 1; end if;

printf "test_local_verdict_fixtures: %o failures\n", failures;
assert failures eq 0;
print "test_local_verdict_fixtures: PASS";
quit;
