// =====================================================================
// Permutation index -- PRODUCT OF RAMIFIED PRIMES ordering
// =====================================================================
//
//   *** PLACEHOLDER -- NOT YET FILLED IN. See REPO_REVIEW.md section 3.2. ***
//
// This file is the counterpart of index_disc.m and is the only place the
// two orderings differ. Everything else in lib/ is shared.
//
// It must define exactly one thing, before orbits.m is loaded:
//
//     ind := function(g)   //  g a group element
//         ...
//     end function;        //  returns an integer
//
// MinIndex (in orbits.m) then builds Smin as the set of non-identity
// elements attaining the minimum of ind over G, and bpiphi works off that
// Smin. So changing ind is sufficient to change the ordering.
//
// I could not fill this in from the repository, because every Magma file
// currently committed uses the discriminant index
//
//     ind(g) = Degree(Parent(g)) - #cycles(g)
//
// including compute_all_fast.m, which run_prp.py names as the prp source.
// Since the _prp columns in data/ differ from the discriminant columns
// (10T1 is 1|1|1|0 against 3|3|3|0), whatever produced them is not the
// copy of compute_all_fast.m that is committed here.
//
// Please paste the real definition from your working copy. For the
// product-of-ramified-primes ordering I would expect something like
// ind(g) = 1 for every g ne Id(G), so that Smin is all of G minus the
// identity -- but do not take that from me, use what you actually ran.
//
// Once this file is correct, `magma -b n:=<d> compute_prp.m` and
// `magma -b n:=<d> compute_disc.m` are the two halves of the pipeline and
// nothing else needs to know which ordering is in play.

// ind := function(g)
//     ...
// end function;

error "lib/index_prp.m has not been filled in yet -- see the comments in this file.";
