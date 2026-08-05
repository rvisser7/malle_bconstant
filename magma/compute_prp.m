// =====================================================================
// Entry point: b-constants in the product-of-ramified-primes ordering
// =====================================================================
//
// Loads the library in dependency order and hands over to the driver.
// This file is deliberately tiny: the ONLY difference between the two
// orderings is which index file is loaded on the marked line below.
//
// Load order matters. Magma resolves free identifiers in a function body
// at definition time, so ind must exist before orbits.m defines MinIndex,
// and everything must exist before fullcheck.m defines FullCheck.
//
// `load` resolves paths relative to the current directory, so run this
// from the magma/ directory (run_prp.py sets cwd for you):
//
//     magma -b n:=12 idxfile:=idx.txt outfile:=out.txt compute_prp.m

load "lib/records.m";
load "lib/index_prp.m";          // <-- the only ordering-dependent line
load "lib/splitting.m";
load "lib/local_tame.m";
load "lib/embedding_problems.m";
load "lib/orbits.m";
load "lib/fullcheck.m";
load "lib/driver.m";

if assigned n then
    RunFromCommandLine();
else
    print "Error: no degree given. Use: magma -b n:=<degree> [idxfile:=<path>] [outfile:=<path>] compute_prp.m";
end if;
quit;
