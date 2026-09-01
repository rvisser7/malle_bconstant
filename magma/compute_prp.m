// =====================================================================
// Entry point: b-constants in the product-of-ramified-primes ordering
// =====================================================================
//
// Loads the library in dependency order, then runs the command-line block.
// The two entry points share four modules and differ in two: orbits.m and
// fullcheck.m are genuinely different code between the orderings.
//
// Load order matters. Magma resolves free identifiers in a function body at
// definition time, so Gpiphi and bpiphi must exist before fullcheck.m defines
// FullCheck.
//
// `load` resolves paths relative to the current directory, so run this from
// the magma/ directory (run_parallel.py sets cwd for you):
//
//     magma -b n:=12 idxfile:=idx.txt outfile:=out.txt compute_prp.m

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/known_residuals.m";
load "lib/q8_certificate.m";
load "lib/certify.m";
load "lib/local_tame.m";
load "lib/wild_prop.m";
load "lib/embedding_problems.m";
load "lib/prp/orbits.m";        // <-- ordering-dependent
load "lib/prp/fullcheck.m";     // <-- ordering-dependent
load "lib/driver.m";

// ---------------------------------------------------------------------
// Command line. Kept at TOP LEVEL, not wrapped in a procedure: `assigned`
// on a command-line variable is only reliable here.
// ---------------------------------------------------------------------
if assigned n then
    n_int := StringToInteger(n);
    if assigned outfile then out := outfile; else out := Sprintf("bconst_results_%o.txt", n_int); end if;
    if assigned idxfile then
        raw := Read(idxfile);
        indices := [ StringToInteger(t) : t in Split(raw, " ,\n\t\r") | t ne "" ];
    else
        indices := [1 .. NumberOfTransitiveGroups(n_int)];
    end if;
    ComputeIndices(n_int, indices, out);
else
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] [outfile:=path] compute_prp.m";
end if;
quit;
