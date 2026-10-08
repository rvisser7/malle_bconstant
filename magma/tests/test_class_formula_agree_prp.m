// =====================================================================
// tests/test_class_formula_agree_prp.m
// =====================================================================
//
//     magma -b tests/test_class_formula_agree_prp.m      (run from magma/)
//
// EvaluatePairs now defaults to the class formula (class_orbits.m, CLASS
// FORMULA), which never forms Ker(pi).  This asserts, PAIR BY PAIR, that it
// agrees with the per-kernel orbit count (MakeKernelCtx / bpiphiCtx), with
// and without the PCGroup route.  b_M and b_T alone would not be enough:
// they are maxima, and a wrong pair could leave them intact.
//
// Then a sweep over every transitive group of degree <= MaxDeg (default 10;
// pass maxdeg:=12 for more) comparing the full evaluated_pairs lists of
// EvaluatePairs(G : Method := "formula") and (G : Method := "kernel").

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

CASES := [
    < 6,    5>,   // C3 wr C2, B cyclic
    < 8,   10>,
    < 8,   23>,   // (Z/dZ)^* non-cyclic
    <10,   20>,
    <12,    5>,   // C3 : C4
    <12,  131>,   // C3 wr C4, Wang Example 3.5
    <12,  218>,
    <15,   95>,   // A5^3 : C6, non-solvable: exercises UsePC := false path
    <16, 1192>,   // C4 wr C4; B = C2 x C4, multi-generator B
    <16, 1863>,
    <20,   27>,
    <24, 14337>   // 36864 elements, 124 classes
];

failures := 0;
checked := 0;

for c in CASES do
    n := c[1]; i := c[2];
    G := TransitiveGroup(n, i);
    d := Exponent(G);
    T, groups := Gpiphi(G, d);
    keepfn := func< g | Order(g) gt 1 >;
    dataPC  := MakeClassFormulaData(G, T[1]`C, T[1]`f, keepfn : UsePC := true);
    dataPerm := MakeClassFormulaData(G, T[1]`C, T[1]`f, keepfn : UsePC := false);

    for grp in groups do
        ctx := MakeKernelCtx(T[grp[1]]);
        e1 := MakeClassFormulaPiCtx(T[grp[1]], dataPC);
        e2 := MakeClassFormulaPiCtx(T[grp[1]], dataPerm);
        if (ctx`nkept eq 0) ne (#e1 eq 0) or (#e1 eq 0) ne (#e2 eq 0) then
            printf "  FAIL %oT%o: kernel/class-formula disagree on whether pi counts\n", n, i;
            failures +:= 1;
            continue;
        end if;
        if ctx`nkept eq 0 then continue; end if;
        for j in grp do
            ebp := T[j];
            _, b0 := bpiphiCtx(ebp, ctx);
            b1 := ClassFormulaCount(ebp, e1);
            b2 := ClassFormulaCount(ebp, e2);
            checked +:= 1;
            if b0 ne b1 or b0 ne b2 then
                printf "  FAIL %oT%o pair %o: kernel %o, formula(PC) %o, formula(perm) %o\n",
                       n, i, j, b0, b1, b2;
                failures +:= 1;
            end if;
        end for;
    end for;
    printf "  %oT%o: %o pairs\n", n, i, #T;
end for;

MaxDeg := assigned maxdeg select StringToInteger(maxdeg) else 10;
for n in [2..MaxDeg] do
    for i in [1..NumberOfTransitiveGroups(n)] do
        G := TransitiveGroup(n, i);
        d1, a1, s1, p1, bM1, bT1, ev1 := EvaluatePairs(G : Method := "formula");
        d2, a2, s2, p2, bM2, bT2, ev2 := EvaluatePairs(G : Method := "kernel");
        same := [d1, a1, s1, p1, bM1, bT1] eq [d2, a2, s2, p2, bM2, bT2]
                and #ev1 eq #ev2
                and forall{ k : k in [1..#ev1] | ev1[k][1] eq ev2[k][1] and ev1[k][3] eq ev2[k][3] };
        checked +:= #ev1;
        if not same then
            printf "  FAIL %oT%o: EvaluatePairs formula vs kernel differ (b_M %o/%o, b_T %o/%o)\n",
                   n, i, bM1, bM2, bT1, bT2;
            failures +:= 1;
        end if;
    end for;
    printf "  degree %o swept\n", n;
end for;

printf "test_class_formula_agree_prp: %o pairs checked, %o failures\n", checked, failures;
assert failures eq 0;
print "test_class_formula_agree_prp: PASS";
quit;
