# Local conditions for residual witnesses K(sqrt delta), K a fixed field of P
# (degree-30 O_5 family, Oct 2026).
#
# T = TransitiveGroup(n, t) acts with 2-blocks; Q = its block quotient
# = Gal(P/Q); H0 = the index-2 subgroup of T that must fix sqrt 5, given by
# its signature position (see wslib.gap_identify).  A field L with
# Gal(L/Q) = T exists over a given P only if every local embedding problem
# is solvable.  This prints, in terms of Q:
#
#   * real place: the classes of complex conjugation in Q that lift to an
#     involution of T;
#   * tame primes: the (inertia tau, p mod 8, p mod 3, Frobenius phi) with
#     phi tau phi^-1 = tau^p that have NO lift (th, sh) with
#     sh th sh^-1 = th^p.
#
# Elements of Q are labelled [order mod Z(Q), chi_1, chi_2, ...] where the
# chi_i (true = nontrivial) run over the quadratic characters of Q, the first
# one being the character cut out by H0 (i.e. "moves sqrt 5").  Use the
# labels to choose the base polynomial and the quadratic fields of P (signature,
# ramified primes and their residue classes, Frobenius at 5), cf. README.
#
#   gap -A -q block_local_conditions.g      (edit TARGETS below)
#
# Examples (Oct 2026): 24T3187 @1 (30T3440): complex conjugation must not be a
# transposition, Frob_5 of the S4 quartic must not be a transposition, and a
# prime with transposition inertia needs (5/p) = 1;  24T3118 @1 (30T3561):
# complex conjugation must not act only on sqrt c, and a prime p | c needs
# p = 1 mod 4 and Frob_p of the quartic not a transposition.
LoadPackage("transgrp");; LoadPackage("smallgrp");;
TARGETS := [[24, 3187, 1], [24, 3118, 1]];
PRIMES := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73];

Sig := function(S, n)
  return SortedList(List(ConjugacyClasses(S),
           c -> [SortedList(CycleLengths(Representative(c), [1..n])), Size(c)]));
end;

Report := function(n, t, pos)
  local T, idx2, sigs, srt, H0, best, bestsize, b, s, sys, a, Q, ZQ, qz, H0Q, chis, lab, bad, tau, p, phi, ok, x;
  T := TransitiveGroup(n, t);
  idx2 := Filtered(NormalSubgroups(T), N -> Index(T, N) = 2);
  sigs := List(idx2, S -> Sig(S, n)); srt := SortedList(sigs);
  H0 := idx2[Position(sigs, srt[pos])];
  # the 2-block system with the largest kernel
  best := fail; bestsize := 0;
  for b in Filtered(AllBlocks(T), b -> Length(b) = 2) do
    s := Size(Stabilizer(T, Orbit(T, Set(b), OnSets), OnTuplesSets));
    if s > bestsize then best := b; bestsize := s; fi;
  od;
  sys := Orbit(T, Set(best), OnSets);
  a := ActionHomomorphism(T, sys, OnSets); Q := Image(a);
  ZQ := Centre(Q); qz := NaturalHomomorphismByNormalSubgroup(Q, ZQ);
  H0Q := Image(a, H0);
  chis := Concatenation([H0Q], Filtered(NormalSubgroups(Q), M -> Index(Q, M) = 2 and M <> H0Q));
  lab := x -> Concatenation([Order(Image(qz, x))], List(chis, M -> not x in M));
  Print("\n", n, "T", t, " H0 at signature position ", pos, ": block kernel ", bestsize,
        ", Q = ", n / 2, "T", TransitiveIdentification(Q), " ", StructureDescription(Q),
        ", |Z(Q)| = ", Size(ZQ), "; labels [order mod Z(Q), chi(H0), other chi...]\n");
  Print("  real place, liftable complex conjugations: ",
        Set(List(Filtered(Elements(T), x -> Order(x) <= 2), x -> lab(Image(a, x)))), "\n");
  bad := [];
  for tau in List(ConjugacyClasses(Q), Representative) do
    if Order(tau) = 1 then continue; fi;
    for p in PRIMES do
      for phi in Elements(Q) do
        if phi * tau * phi^-1 <> tau^p then continue; fi;
        ok := ForAny(PreImages(a, tau), th -> ForAny(PreImages(a, phi), sh -> sh * th * sh^-1 = th^p));
        if not ok then AddSet(bad, [lab(tau), p mod 8, p mod 3, lab(phi)]); fi;
      od;
    od;
  od;
  Print("  tame obstructions [inertia, p mod 8, p mod 3, Frobenius]:\n");
  for x in bad do Print("    ", x, "\n"); od;
end;

for tg in TARGETS do Report(tg[1], tg[2], tg[3]); od;
QUIT;
