// =====================================================================
// verdict_report.m  --  per-pair local verdicts for a single group
// =====================================================================
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering,
//                        i.e. load this LAST, like driver.m.
//
// diagnose_disc.m / diagnose_prp.m tell you THAT a group moves under the
// policy correction.  This tells you WHY: for every pair that could raise
// the upper bound, the verdict at every place, with the message, plus what
// the certificate chain made of the residual.
//
// Read it like this.  A pair whose sound verdict is UNK is a pair that the
// old code vetoed without proof; the place-by-place lines say which test
// and which prime.  If that place reports "p | #Ker(pi) so a wildly
// ramified lift is not excluded", the honest answer is that local
// solvability at p is open, and the cell stays \N until the wild case at p
// is decided.  If instead the residual is reported central and the verdict
// is UNK only because of a pro-p place, certificates/central.m would close
// the bracket the moment that place can be decided.

VerdictName := function(v)
    if v eq LocalVerdictYes then return "YES"; end if;
    if v eq LocalVerdictNo  then return "NO"; end if;
    return "UNK";
end function;

PlaceName := function(p)
    if p eq 0 then return "infinity"; end if;
    return Sprintf("p = %o", p);
end function;

ReportVerdicts := procedure(n, i)
    G := TransitiveGroup(n, i);
    d, a, nSmin, nPairs, bM, bT, pairs := EvaluatePairs(G);

    printf "%oT%o: |G| = %o, a = %o, #Smin = %o, d = %o\n", n, i, #G, a, nSmin, d;
    printf "  pairs = %o (evaluated %o), b_M = %o, b_T = %o\n", nPairs, #pairs, bM, bT;
    printf "  showing every pair with b(pi,phi) > b_M, i.e. every pair that\n";
    printf "  could raise the upper bound above b_M\n";

    shown := 0;
    for item in pairs do
        j := item[1]; ebp := item[2]; b := item[3];
        if b le bM then continue; end if;
        shown +:= 1;

        v, why_v, reports := LocalVerdictWithQuotients(ebp, DefaultLocalPolicy);
        vdirect := LocalVerdict(ebp, DefaultLocalPolicy);
        vlegacy := LocalVerdict(ebp, LegacyLocalPolicy);
        ok, why, ebp1 := CertifyAdmissible(ebp, d);

        printf "\n  pair %o: b(pi,phi) = %o, #B = %o, #Ker(pi) = %o\n",
               j, b, #ebp`B, #Kernel(ebp`pi);
        printf "    verdict: %o   (direct: %o, legacy: %o)\n",
               VerdictName(v), VerdictName(vdirect), VerdictName(vlegacy);
        if v ne vdirect then
            printf "      inherited: %o\n", why_v;
        end if;
        for r in reports do
            printf "      %o: %o -- %o\n", PlaceName(r[1]), VerdictName(r[2]), r[3];
        end for;
        printf "    residual: #G = %o, #Ker = %o, central = %o\n",
               #ebp1`G, #Kernel(ebp1`pi), IsCentralResidual(ebp1);
        printf "    certificate: %o\n", ok;
        printf "      %o\n", why;
    end for;

    if shown eq 0 then
        printf "\n  no pair exceeds b_M, so b_W = b_M = b_T is forced\n";
    end if;
end procedure;
