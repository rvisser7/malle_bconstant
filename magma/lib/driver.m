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
//     magma -b n:=<degree> [idxfile:=<path>] [outfile:=<path>] [knownlowerfile:=<path>] compute_disc.m
//
//     idxfile : whitespace- or comma-separated group indices to compute.
//               If omitted, every transitive group of degree n is done.
//     outfile : results file; defaults to bconst_results_<degree>.txt
//     knownlowerfile : optional verified witness hints index|b|b_M|b_T.

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


// Optional verified-witness hints, one line per group:
//
//     index|b_witness|b_M|b_T
//
// They are checked against Phase 1 inside FullCheck before they are allowed
// to prune Phase 2.  Keeping the format tiny makes this safe to generate from
// run_parallel.py and easy to inspect by hand.
ReadKnownLowers := function(path)
    rows := [* *];
    for ln in Split(Read(path), "\n") do
        if #ln eq 0 then continue; end if;
        fields := Split(ln, "|");
        if #fields ne 4 then
            error "bad known-lower row: " cat ln;
        end if;
        Append(~rows, < StringToInteger(fields[1]), StringToInteger(fields[2]),
                         StringToInteger(fields[3]), StringToInteger(fields[4]) >);
    end for;
    return rows;
end function;

KnownLowerForIndex := function(rows, i)
    if Type(rows) eq BoolElt then return false, 0, -1, -1; end if;
    for r in rows do
        if r[1] eq i then return true, r[2], r[3], r[4]; end if;
    end for;
    return false, 0, -1, -1;
end function;

ComputeIndices := procedure(n, indices, outfile : KnownLowers := false)
    Write(outfile, "index|b_M|b_T|BW_lower_split|BW_upper_local|seconds" : Overwrite := true);
    for i in indices do
        t0 := Cputime();
        failed := false;
        msg := "";
        try
            G := TransitiveGroup(n, i);
            hasKnown, knownLower, knownBM, knownBT := KnownLowerForIndex(KnownLowers, i);
            if hasKnown then
                R := FullCheck(G : KnownLower := knownLower, KnownBM := knownBM,
                                   KnownBT := knownBT);
            else
                R := FullCheck(G);
            end if;
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
