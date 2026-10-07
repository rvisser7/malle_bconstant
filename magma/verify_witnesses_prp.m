// =====================================================================
// Entry point: verify witness fields, prp ordering
// =====================================================================
//
// Loads exactly the same library as compute_prp.m, then lib/witness_body.m.
// See data/witnesses/README.md.  Run from magma/:
//
//     magma -b verify_witnesses_prp.m
//     magma -b infile:=<path> outfile:=<path> verify_witnesses_prp.m
//
// Incremental: rows already in outfile are reused when the same (label,
// polynomial) is still offered, so only new or edited witnesses are verified.
//     magma -b force:=1 verify_witnesses_prp.m                  (verify everything again)
//     magma -b recheck:=26T34,34T34 verify_witnesses_prp.m      (re-verify these labels)
// Use force:=1 after changing the verifier itself (lib/witness_body.m).
//
// Defaults: ../data/witnesses/witnesses.txt -> ../data/witnesses/verified_prp.txt

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
load "lib/prp/orbits.m";        // <-- ordering-dependent
load "lib/bw_phase2.m";
load "lib/prp/fullcheck.m";     // <-- ordering-dependent
load "lib/driver.m";             // CleanForField
load "lib/witness_body.m";

if assigned infile then inf := infile; else inf := "../data/witnesses/witnesses.txt"; end if;
if assigned outfile then outf := outfile; else outf := "../data/witnesses/verified_prp.txt"; end if;
printf "Verifying witnesses in %o for the prp ordering -> %o\n", inf, outf;
rc := {};
if assigned recheck then
    rc := { WitnessStrip(x) : x in Split(recheck, ",") };
end if;
VerifyWitnessFile(inf, outf, "prp" : Force := assigned force, Recheck := rc);
quit;
