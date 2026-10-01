// =====================================================================
// Entry point: b-constants in the discriminant ordering
// =====================================================================
//
// Loads the library in dependency order, then runs the command-line block.
// The two entry points differ in exactly two modules: lib/disc/orbits.m and
// lib/disc/fullcheck.m.  Everything else, including the b_W bracket in
// lib/bw_phase2.m, is shared.
//
// Load order matters. Magma resolves free identifiers in a function body at
// definition time, so each module must precede its users:
//   local_verdict  after local_tame and wild_prop
//   certificates/  after local_verdict (central.m consumes it)
//   certify        after every certificate module
//   bw_phase2      after certify, before fullcheck
//
// `load` resolves paths relative to the current directory, so run this from
// the magma/ directory (run_parallel.py sets cwd for you):
//
//     magma -b n:=12 idxfile:=idx.txt outfile:=out.txt compute_disc.m

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
load "lib/disc/orbits.m";        // <-- ordering-dependent
load "lib/bw_phase2.m";
load "lib/disc/fullcheck.m";     // <-- ordering-dependent
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
    print "Error: no degree. Use: magma -b n:=<degree> [idxfile:=path] [outfile:=path] compute_disc.m";
end if;
quit;
