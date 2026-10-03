// =====================================================================
// why_no_candidates.m  --  dump the candidate table at a stalled residual
// =====================================================================
//
//   magma -b n:=20 idx:=554,662 why_no_candidates.m
//
// For every pair that CertifyAdmissible declines, prints the residual and
// then EVERY nontrivial proper normal subgroup M of the residual, with the
// tests AdmissibleCandidates applies:
//
//     inKr          M subset Ker(pi_r)      -- required
//     GAR           IsGARLayer(M)           -- sufficient on its own (with
//                   inKr): GAR layers need no complement [MM99 IV.3.6]
//     allowed       LayerAllowed(G_r, M)    -- otherwise required: nilpotent
//                   (9.6.10), or odd order with no C_{p-1} quotient of
//                   (G_r/M)^ab for p | #M (9.5.8); nilpotent column shown too
//     complemented  IsSplitKernel(G_r, M)   -- required with "allowed"
//
// A row with inKr and (GAR, or allowed and complemented) that did NOT end
// up in cands means the bug is in AdmissibleCandidates itself.  No such row
// means the residual is genuinely terminal and needs a certificate, not a
// tower fix.

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
            [ #M : M in AdmissibleCandidates(Gr, Kr) ];
        printf "  normal subgroups of G_r:\n";

        for R in NormalSubgroups(Gr) do
            M := R`subgroup;
            if #M eq 1 or #M eq #Gr then continue; end if;
            inKr  := M subset Kr;
            nilp  := IsNilpotent(M);
            allow := LayerAllowed(Gr, M);
            compl := IsSplitKernel(Gr, M);
            gar   := IsGARLayer(M);
            printf "    |M|=%-5o %-18o inKr=%-5o nilpotent=%-5o allowed=%-5o complemented=%-5o GAR=%o\n",
                #M, GroupName(M), inKr, nilp, allow, compl, gar;
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
