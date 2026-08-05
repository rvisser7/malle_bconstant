// =====================================================================
// Machine-readable driver
// =====================================================================
//
// Shared by compute_disc.m and compute_prp.m. Reads a list of transitive
// group indices and writes one pipe-delimited line per group, which
// scripts/run_prp.py parses.
//
// This replaces the driver that run_prp.py used to generate on the fly by
// text-slicing compute_all_fast.m at the marker "EvaluateDegreeBWBounds :=".
// It is a normal committed file now: greppable, diffable, editable.
//
// Requires (load first): fullcheck.m (and everything it needs)
//
// Command line, via one of the entry points:
//     magma -b n:=<degree> [idxfile:=<path>] [outfile:=<path>] compute_disc.m
//
//     idxfile : whitespace- or comma-separated group indices to compute.
//               If omitted, every transitive group of degree n is done.
//     outfile : results file; defaults to bconst_results_<degree>.txt

ComputeIndices := procedure(n, indices, outfile)
    Write(outfile, "index|b_M|b_T|BW_lower_split|BW_upper_local" : Overwrite := true);
    for i in indices do
        G := TransitiveGroup(n, i);
        R := FullCheck(G);
        line := Sprintf("%o|%o|%o|%o|%o", i, R`b_M, R`b_T,
                        R`BW_lower_split, R`BW_upper_local);
        Write(outfile, line);
        printf "  %oT%o: b_M=%o b_T=%o BW=[%o,%o]\n",
               n, i, R`b_M, R`b_T, R`BW_lower_split, R`BW_upper_local;
    end for;
end procedure;

// ---------------------------------------------------------------------
// Command line entry. Expects `n` to be assigned by the caller.
// ---------------------------------------------------------------------
RunFromCommandLine := procedure()
    n_int := StringToInteger(n);

    if assigned outfile then
        out := outfile;
    else
        out := Sprintf("bconst_results_%o.txt", n_int);
    end if;

    if assigned idxfile then
        raw := Read(idxfile);
        indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
    else
        indices := [1 .. NumberOfTransitiveGroups(n_int)];
    end if;

    ComputeIndices(n_int, indices, out);
end procedure;
