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

// One line per group, written as soon as that group finishes, so that a
// chunk killed by a timeout still leaves every finished group on disk
// (run_parallel.py now reads partial output files):
//
//     index|b_M|b_T|BW_lower_split|BW_upper_local|seconds
//     index|ERROR|message
//
// A Magma error in one group is caught and recorded instead of abandoning
// the rest of the chunk.

CleanForField := function(s)
    out := "";
    for k := 1 to Minimum(#s, 300) do
        ch := s[k];
        if ch eq "|" or ch eq "\n" then out cat:= " ";
        else out cat:= ch; end if;
    end for;
    return out;
end function;

ComputeIndices := procedure(n, indices, outfile)
    Write(outfile, "index|b_M|b_T|BW_lower_split|BW_upper_local|seconds" : Overwrite := true);
    for i in indices do
        t0 := Cputime();
        failed := false;
        msg := "";
        try
            G := TransitiveGroup(n, i);
            R := FullCheck(G);
        catch err
            failed := true;
            msg := CleanForField(Sprint(err`Object));
        end try;

        if failed then
            Write(outfile, Sprintf("%o|ERROR|%o", i, msg));
            printf "  %oT%o: ERROR %o\n", n, i, msg;
            continue;
        end if;

        secs := Round(Cputime(t0));
        Write(outfile, Sprintf("%o|%o|%o|%o|%o|%o", i, R`b_M, R`b_T,
                               R`BW_lower_split, R`BW_upper_local, secs));
        printf "  %oT%o: b_M=%o b_T=%o BW=[%o,%o] (%os)\n",
               n, i, R`b_M, R`b_T, R`BW_lower_split, R`BW_upper_local, secs;
    end for;
end procedure;
