// =====================================================================
// Machine-readable driver
// =====================================================================
//
// Shared by compute_disc.m and compute_prp.m. Reads a list of transitive
// group indices and writes one pipe-delimited line per group, which
// run_parallel.py parses.
//
// This is the committed replacement for the driver that run_prp.py used to
// generate on the fly by text-slicing the source at the marker
// "EvaluateDegreeBWBounds :=" into compute_prp.m / compute_disc_gen.m.
// Those generated files no longer need to exist.
//
// Requires (load first): an orbits.m and a fullcheck.m for one ordering
//
// The command-line block lives at the bottom of each entry point, at TOP
// LEVEL rather than inside a procedure -- `assigned` does not behave the
// same way on command-line variables from inside a procedure body.
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
