// =====================================================================
// inspect_stalled.m  --  why did the b_W bracket not collapse?
// =====================================================================
//
//   magma -b n:=15 idx:=76,77,83 inspect_stalled.m
//
// Read-only diagnostic.  Touches nothing in the pipeline: it re-runs the
// pair enumeration for each group, and for every pair whose bval exceeds
// b_M but which CertifyAdmissible declines, prints the residual left over
// after the nilpotent split-tower, plus the facts that decide which
// certificate (if any) ought to apply to it.
//
// Columns of each UNCERT line:
//   b          the pair's b(pi,phi)
//   |B|        size of the abelian quotient
//   G_r, K_r   residual group and its kernel, after MaximalSplitReduction
//   split      is the residual extension split?
//   direct     is the residual a DIRECT product K_r x B?
//   K_r solv   is the residual kernel solvable?
//   local      does the pair still pass the local tests?
//
// Reading the output:
//   split=false                  -> arithmetic case; only Q8 is handled
//   direct=true                  -> needs K_r realisable over Q, linearly
//                                   disjoint from Q(phi)
//   split=true, direct=false     -> genuine semidirect residual; needs a
//                                   B-equivariant realisation of K_r
//   local=false                  -> the pair is dead anyway; the upper
//                                   bound should already have excluded it,
//                                   and if it has not, that is a bug

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
load "lib/disc/orbits.m";

IsDirectProductResidual := function(Gr, Kr)
    if #Kr eq 1 then return true; end if;
    for R in NormalSubgroups(Gr) do
        H := R`subgroup;
        if #H * #Kr eq #Gr and #(H meet Kr) eq 1 then
            return true;
        end if;
    end for;
    return false;
end function;

InspectGroup := procedure(n, i)
    G := TransitiveGroup(n, i);
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    T := Gpiphi(G, d);

    bM := 0; bT := 0;
    pairs := [];
    for ebp in T do
        // bpiphi returns TWO values: |Smin cap Ker(pi)| first, then the
        // orbit count.  The second one is b(pi,phi).
        numSmin, b := bpiphi(ebp, Smin);
        if numSmin eq 0 then continue; end if;
        Append(~pairs, <b, ebp>);
        if IsTrivialQuotientEbp(ebp) then bM := b; end if;
        if b gt bT then bT := b; end if;
    end for;

    printf "%oT%o  |G|=%o  d=%o  b_M=%o  b_T=%o\n", n, i, #G, d, bM, bT;
    if bM eq bT then
        printf "    (b_M = b_T, nothing to decide)\n";
        return;
    end if;

    for v in pairs do
        if v[1] le bM then continue; end if;
        ebp := v[2];
        ok := CertifyAdmissible(ebp, d);
        if ok then
            printf "    b=%o  |B|=%o  CERTIFIED\n", v[1], #ebp`B;
            continue;
        end if;
        ebp1, fullySplit := MaximalSplitReduction(ebp);
        Gr := ebp1`G;
        Kr := Kernel(ebp1`pi);
        isSplit  := IsSplitKernel(Gr, Kr);
        isDirect := IsDirectProductResidual(Gr, Kr);
        // What the tower had available AT the residual.  A non-empty list
        // here means the tower search stopped early -- a bug, not a missing
        // certificate.
        cands := NilpotentComplementedCandidates(Gr, Kr);
        printf "    b=%o  |B|=%o  UNCERT  G_r=%o (%o)  K_r=%o (%o)  "
             * "split=%o direct=%o Kr_solv=%o local=%o  cands=%o\n",
            v[1], #ebp`B,
            GroupName(Gr), #Gr, GroupName(Kr), #Kr,
            isSplit, isDirect, IsSolvable(Kr),
            PassesCheckedLocalTests(ebp),
            [ #M : M in cands ];
    end for;
end procedure;

// ---------------------------------------------------------------------
// Command line: n:=<degree>  idx:=<comma-separated T-numbers>
// Must stay at TOP LEVEL so the `assigned` tests see the CLI variables.
// ---------------------------------------------------------------------
if assigned n and assigned idx then
    deg := StringToInteger(n);
    for s in Split(idx, ",") do
        InspectGroup(deg, StringToInteger(s));
    end for;
else
    printf "usage: magma -b n:=15 idx:=76,77,83 inspect_stalled.m\n";
end if;

quit;
