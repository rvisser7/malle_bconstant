// =====================================================================
// why_no_candidates.m  --  dump the candidate table at a stalled residual
// =====================================================================
//
//   magma -b n:=20 idx:=554,662 why_no_candidates.m
//
// For every pair that CertifyAdmissible declines, prints the residual and
// then EVERY nontrivial proper normal subgroup M of the residual, with the
// three tests NilpotentComplementedCandidates applies:
//
//     inKr          M subset Ker(pi_r)  -- required
//     nilpotent     IsNilpotent(M)      -- required
//     complemented  IsSplitKernel(G_r, M) -- required
//
// A row with all three true that did NOT end up in cands means the bug is in
// NilpotentComplementedCandidates itself.  No such row means the residual is
// genuinely terminal and needs a certificate, not a tower fix.

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/known_residuals.m";
load "lib/q8_certificate.m";
load "lib/certify.m";
load "lib/local_tame.m";
load "lib/embedding_problems.m";
load "lib/disc/orbits.m";

DumpGroup := procedure(n, i)
    G := TransitiveGroup(n, i);
    a, Smin := MinIndex(G);
    d := LCM([ Order(s) : s in Smin ]);
    T := Gpiphi(G, d);

    bM := 0;
    pairs := [];
    for ebp in T do
        numSmin, b := bpiphi(ebp, Smin);
        if numSmin eq 0 then continue; end if;
        Append(~pairs, <b, ebp>);
        if IsTrivialQuotientEbp(ebp) then bM := b; end if;
    end for;

    for v in pairs do
        if v[1] le bM then continue; end if;
        ok := CertifyAdmissible(v[2], d);
        if ok then continue; end if;

        ebp1 := MaximalSplitReduction(v[2]);
        Gr := ebp1`G;
        Kr := Kernel(ebp1`pi);

        printf "%oT%o  b=%o  residual G_r=%o (%o)  K_r=%o (%o)\n",
            n, i, v[1], GroupName(Gr), #Gr, GroupName(Kr), #Kr;
        printf "  cands returned: %o\n",
            [ #M : M in NilpotentComplementedCandidates(Gr, Kr) ];
        printf "  normal subgroups of G_r:\n";

        for R in NormalSubgroups(Gr) do
            M := R`subgroup;
            if #M eq 1 or #M eq #Gr then continue; end if;
            inKr  := M subset Kr;
            nilp  := IsNilpotent(M);
            compl := IsSplitKernel(Gr, M);
            printf "    |M|=%-5o %-18o inKr=%-5o nilpotent=%-5o complemented=%o\n",
                #M, GroupName(M), inKr, nilp, compl;
        end for;
        printf "\n";
    end for;
end procedure;

if assigned n and assigned idx then
    deg := StringToInteger(n);
    for s in Split(idx, ",") do
        DumpGroup(deg, StringToInteger(s));
    end for;
else
    printf "usage: magma -b n:=20 idx:=554,662 why_no_candidates.m\n";
end if;

quit;
