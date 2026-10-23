# Exact Galois groups of the fields L = K(sqrt c)(sqrt(d mu)) of
# search_twisted_kummer.py (degree-30 O_5 family, A5/S5/A6/S6 leaves, Oct 2026).
#
# K is a sextic with Galois group B (A5 = 6T12, S5 = 6T14, A6 = 6T15,
# S6 = 6T16), d in K with conjugates d_1..d_6, mu in Q(sqrt c).  Then
#
#   L  is contained in  M . C,  M = closure of K(sqrt d)  (group E inside the
#   wreath product W = C2 wr B on the 12 roots +-sqrt(d_i)),  C = Q(sqrt c, sqrt mu)
#   (cyclic quartic C4 if N(mu) in c Q*^2, or just Q(sqrt c) = C2 for mu = 1),
#
# and Gal(M C / Q) is the subgroup of W x C cut out by the coincidences of
# quadratic fields, expressed through three characters:
#   P = parity of the sign changes (it fixes sqrt N(d)),  S = sign of the
#   B-part (it fixes sqrt disc K),  K = moves sqrt c.
# A relation [a, b, k] means aP + bS + kK = 0, e.g.
#   N(d) in Q*^2         -> [1,0,0]      N(d) in disc Q*^2    -> [1,1,0]
#   N(d) in c Q*^2       -> [1,0,1]      N(d) in c disc Q*^2  -> [1,1,1]
#   disc K in c Q*^2     -> [0,1,1]      (B = A5, A6: S = 0, i.e. [0,1,0])
# The 24 roots of L are the classes {(s sqrt d_i, t sqrt mu'), (-s sqrt d_i, -t sqrt mu')};
# the action on them is Gal(L/Q).  For each configuration this prints the
# transitive identification and the signature position (wslib.gap_identify)
# of ker K = Gal(L/Q(sqrt c)).  This is exact, provided the d_i are as
# independent as the norm condition allows (generic d; the statistics of the
# search confirm the order).
#
#   gap -A -q twisted_fiber_groups.g
#
# Results used (c = 5, mu = (5 + sqrt 5)/2, so C = C4):
#   A5: [1,0,0] -> 24T7243 (30T4064),  [1,0,1] -> 24T7242 (30T4065)
#       (24T7242, 7243 and 7246 have identical cycle-type statistics)
#   S5: [1,0,0] -> 24T9662 (30T4336),  [1,1,0] -> 24T9665 (30T4337),
#       [1,1,1] -> 24T9659 (30T4338),  [1,0,1] -> 24T9656 (30T4340)
#   A6: [1,0,0] -> 24T12614 (30T4645), [1,0,1] -> 24T12613 (30T4647)
#   S6 with disc K in 5 Q*^2 ([0,1,1]): [1,0,0] -> 24T12616 (30T4651),
#       [1,0,1] -> 24T12615 (30T4649)
#   S6: [1,0,0] -> 24T14623 (30T4836), [1,1,0] -> 24T14626 (30T4838),
#       [1,1,1] -> 24T14620 (30T4837), [1,0,1] -> 24T14617 (30T4833)
# with ker K at signature position 1 in every case (= H0 of the 30T group).
LoadPackage("transgrp");; LoadPackage("smallgrp");;

Sig := function(S, n)
  return SortedList(List(ConjugacyClasses(S),
           c -> [SortedList(CycleLengths(Representative(c), [1..n])), Size(c)]));
end;

FiberGroup := function(B, ctype, rels)
  local n, flips, lifts, W, cgen, full, chi, sub, x, roots, i, m, act, hom;
  n := NrMovedPoints(B);
  flips := List([1..n], i -> (2*i-1, 2*i));
  lifts := List(GeneratorsOfGroup(B), g -> PermList(Concatenation(List([1..n], i -> [2*(i^g)-1, 2*(i^g)]))));
  W := Group(Concatenation(flips, lifts));
  if ctype = "C4" then cgen := (13,14,15,16); else cgen := (13,14); fi;   # 13 = sqrt mu, 14 = sqrt mubar, 15/16 = negatives
  full := Group(Concatenation(GeneratorsOfGroup(W), [cgen]));
  chi := function(g)                        # [P, S, K]
    local par, b;
    par := Number([1..n], i -> (2*i-1)^g mod 2 = 0) mod 2;
    b := PermList(List([1..n], i -> QuoInt((2*i-1)^g + 1, 2)));
    return [par, (1 - SignPerm(b)) / 2, (13^g - 13) mod 2];
  end;
  sub := full;
  for x in rels do
    sub := Kernel(GroupHomomorphismByImages(sub, CyclicGroup(IsPermGroup, 2), GeneratorsOfGroup(sub),
             List(GeneratorsOfGroup(sub), g -> (1,2)^((x * chi(g)) mod 2))));
  od;
  roots := [];
  if ctype = "C4" then
    for i in [1..2*n] do for m in [13..16] do
      AddSet(roots, Set([[i, m], [i + 2*(i mod 2) - 1, ((m - 13 + 2) mod 4) + 13]]));
    od; od;
  else
    for i in [1..2*n] do for m in [13, 14] do Add(roots, [[i, m]]); od; od;
  fi;
  act := function(cl, g) return Set(List(cl, p -> [p[1]^g, p[2]^g])); end;
  hom := ActionHomomorphism(sub, roots, act);
  return rec(G := sub, hom := hom, chi := chi);
end;

Report := function(name, B, ctype, rels)
  local r, Gp, t, kerK, T, srt, pos;
  r := FiberGroup(B, ctype, rels);
  Gp := Image(r.hom);
  if NrMovedPoints(Gp) <> 24 or not IsTransitive(Gp, [1..24]) then return; fi;
  t := TransitiveIdentification(Gp);
  kerK := Image(r.hom, Kernel(GroupHomomorphismByImages(r.G, CyclicGroup(IsPermGroup, 2), GeneratorsOfGroup(r.G),
             List(GeneratorsOfGroup(r.G), g -> (1,2)^(r.chi(g)[3])))));
  T := TransitiveGroup(24, t);
  srt := SortedList(List(Filtered(NormalSubgroups(T), N -> Index(T, N) = 2), N -> Sig(N, 24)));
  pos := Position(srt, Sig(kerK, 24));
  Print(name, " C = ", ctype, " relations ", rels, ": |G| = ", Size(Gp), ", 24T", t,
        ", ker K at signature position ", pos, ", |Z| = ", Size(Centre(Gp)), "\n");
end;

for rels in [[[0,1,0],[1,0,0]], [[0,1,0],[1,0,1]]] do Report("A5", TransitiveGroup(6, 12), "C4", rels); od;
for rels in [[[1,0,0]], [[1,1,0]], [[1,1,1]], [[1,0,1]]] do Report("S5", TransitiveGroup(6, 14), "C4", rels); od;
for rels in [[[0,1,0],[1,0,0]], [[0,1,0],[1,0,1]]] do Report("A6", TransitiveGroup(6, 15), "C4", rels); od;
for rels in [[[0,1,1],[1,0,0]], [[0,1,1],[1,0,1]]] do Report("S6", TransitiveGroup(6, 16), "C4", rels); od;
for rels in [[[1,0,0]], [[1,1,0]], [[1,1,1]], [[1,0,1]]] do Report("S6", TransitiveGroup(6, 16), "C4", rels); od;
QUIT;
