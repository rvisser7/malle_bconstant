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
// As soon as Phase 1 (b_M, b_T) is done, a provisional line
//
//     index|b_M|b_T|b_M|b_T|seconds|phase1
//
// is written first, so b_T is on disk even if Phase 2 later runs out of
// time. [b_M, b_T] is the trivial bracket for b_W. The final line, if
// Phase 2 finishes, comes later and supersedes it. With Phase1Only (CLI
// phase1only:=1) Phase 2 is skipped and only the provisional line is written.
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

ComputeIndices := procedure(n, indices, outfile : KnownLowers := false,
                             Phase1Only := false)
    Write(outfile, "index|b_M|b_T|BW_lower_split|BW_upper_local|seconds" : Overwrite := true);
    for i in indices do
        t0 := Cputime();
        failed := false;
        finished := false;
        msg := "";
        try
            G := TransitiveGroup(n, i);
            d, a, nSmin, nPairs, bM, bT, evaluated_pairs := EvaluatePairs(G);
            Write(outfile, Sprintf("%o|%o|%o|%o|%o|%o|phase1", i, bM, bT, bM, bT,
                                   Round(Cputime(t0))));
            printf "  %oT%o: b_M=%o b_T=%o (Phase 1, %os)\n",
                   n, i, bM, bT, Round(Cputime(t0));
            if not Phase1Only then
                P1 := < d, a, nSmin, nPairs, bM, bT, evaluated_pairs >;
                hasKnown, knownLower, knownBM, knownBT := KnownLowerForIndex(KnownLowers, i);
                if hasKnown then
                    R := FullCheck(G : KnownLower := knownLower, KnownBM := knownBM,
                                       KnownBT := knownBT, Phase1 := P1);
                else
                    R := FullCheck(G : Phase1 := P1);
                end if;
                finished := true;
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
        if not finished then continue; end if;

        secs := Round(Cputime(t0));
        Write(outfile, Sprintf("%o|%o|%o|%o|%o|%o", i, R`b_M, R`b_T,
                               R`BW_lower_split, R`BW_upper_local, secs));
        printf "  %oT%o: b_M=%o b_T=%o BW=[%o,%o] (%os)\n",
               n, i, R`b_M, R`b_T, R`BW_lower_split, R`BW_upper_local, secs;
    end for;
end procedure;
