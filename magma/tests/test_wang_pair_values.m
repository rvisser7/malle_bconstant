// =====================================================================
// tests/test_wang_pair_values.m
// =====================================================================
//
//     magma -b tests/test_wang_pair_values.m      (run from magma/)
//
// A maximum-only regression can miss a bug that permutes the b(pi,phi)
// values among different cyclotomic fields.  Wang Example 3.5 gives all four
// values for G = C3 wr C4 in the product-of-ramified-primes ordering:
//
//   Q(i)          17      kernel residues {1,5}  mod 12
//   Q(sqrt 3)     17      kernel residues {1,11} mod 12
//   Q(sqrt -3)    29      kernel residues {1,7}  mod 12
//   Q             19      trivial quotient
//
// Test the individual phi, not only b_M=19 and b_T=29.

load "lib/records.m";
load "lib/embedding_problems.m";
load "lib/class_orbits.m";
load "lib/prp/orbits.m";

KernelResidues := function(ebp)
    r := [ (IntegerRing()!ebp`f(c)) mod ebp`d : c in Kernel(ebp`phi) ];
    Sort(~r);
    return r;
end function;

G := WreathProduct(CyclicGroup(3), CyclicGroup(4));
d := Exponent(G);
assert d eq 12;
T, groups := Gpiphi(G, d);

foundQ := 0;
foundI := 0;
found3 := 0;
foundm3 := 0;
failures := 0;

for grp in groups do
    ctx := MakeKernelCtx(T[grp[1]]);
    if ctx`nkept eq 0 then continue; end if;
    for j in grp do
        ebp := T[j];
        _, b := bpiphiCtx(ebp, ctx);
        b := Integers()!b;

        if #ebp`B eq 1 then
            foundQ +:= 1;
            if b ne 19 then
                printf "  FAIL Q: got b=%o, expected 19\n", b;
                failures +:= 1;
            end if;
        elif #ebp`B eq 2 then
            r := KernelResidues(ebp);
            if r eq [1,5] then
                foundI +:= 1;
                if b ne 17 then failures +:= 1; end if;
            elif r eq [1,11] then
                found3 +:= 1;
                if b ne 17 then failures +:= 1; end if;
            elif r eq [1,7] then
                foundm3 +:= 1;
                if b ne 29 then failures +:= 1; end if;
            end if;
        end if;
    end for;
end for;

printf "  Q=%o, Q(i)=%o, Q(sqrt3)=%o, Q(sqrt-3)=%o\n",
       foundQ, foundI, found3, foundm3;
if <foundQ, foundI, found3, foundm3> ne <1,1,1,1> then
    print "  FAIL: did not identify each of Wang's four pairs exactly once";
    failures +:= 1;
end if;

printf "test_wang_pair_values: %o failures\n", failures;
assert failures eq 0;
print "test_wang_pair_values: PASS";
quit;
