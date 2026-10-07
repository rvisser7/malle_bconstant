# Local liftability pre-checks for residual embedding problems.
#
# Every successful search in Oct 2026 was unblocked by a LOCAL condition on the
# base field (the real place for 20T550/20T612, the prime 5 for 20T498 and
# 20T879/20T884), never by enlarging the set S of allowed ramified primes.
# These helpers answer "which local data of the base field can possibly lift
# to H?" before any number-field computation is spent.
#
# Conventions.  H is the residual group (e.g. G/O_5(G)), q : H -> Q a quotient
# map onto the Galois group of the base field E (e.g. Q = H^ab when E is the
# maximal abelian subfield).  For a tame prime p with inertia image bI and
# Frobenius image bF in Q, a local lift exists iff there are X, Y in H with
# q(X) = bF, q(Y) = bI and X*Y*X^-1 = Y^p (Y then automatically has order
# prime to p).  At the real place complex conjugation c lifts iff some
# preimage of c has order <= 2.  Wild primes are not covered.
#
#   gap -q local_lift.g        (runs the examples at the bottom)

TameLiftable := function(H, q, bF, bI, p)
  local Ys, Xs;
  Ys := Filtered(Elements(H), y -> Image(q, y) = bI and Order(y) mod p <> 0);
  Xs := Filtered(Elements(H), x -> Image(q, x) = bF);
  return ForAny(Ys, Y -> ForAny(Xs, X -> X*Y*X^-1 = Y^p));
end;

RealLiftable := function(H, q, c)
  return ForAny(Elements(H), h -> Image(q, h) = c and h^2 = One(H));
end;

# Table of all (inertia, Frobenius) pairs in Q that lift, for one prime p.
TameTable := function(H, q, p)
  local Q, out, bI, bF;
  Q := Image(q); out := [];
  for bI in Elements(Q) do
    if bI = One(Q) then continue; fi;
    for bF in Elements(Q) do
      if TameLiftable(H, q, bF, bI, p) then Add(out, [bI, bF]); fi;
    od;
  od;
  return out;
end;

# Variant for residuals H whose 16-point representation has blocks of size 4
# (H -> S4 on blocks), used for 20T879/20T884: which cycle types of the
# Frobenius of the S4-quartic L at p allow a tame lift, when inertia at p acts
# only on sqrt(5) (i.e. lies outside H0 and is trivial on the blocks)?
FrobTypesAtSqrt5Prime := function(H, H0, p)
  local b4, act, ct, cts, Ys;
  b4 := First(AllBlocks(H), b -> Length(b) = 4);
  act := ActionHomomorphism(H, Orbit(H, Set(b4), OnSets), OnSets);
  ct := g -> SortedList(CycleLengths(Image(act, g), [1..4]));
  Ys := Filtered(Elements(H), y -> not y in H0 and ct(y) = [1,1,1,1] and Order(y) mod p <> 0);
  cts := [[1,1,1,1], [1,1,2], [2,2], [1,3], [4]];
  return List(cts, t -> [t, ForAny(Ys, Y -> ForAny(Elements(H),
                 X -> ct(X) = t and X*Y*X^-1 = Y^p))]);
end;

# ---- examples -------------------------------------------------------------
# 20T498: H = [32,8], E = H^ab = C4 x C2.  Real place: only the identity of
# H^ab lifts to an involution, so E (hence L) must be totally real.
H := SmallGroup(32, 8);
q := NaturalHomomorphismByNormalSubgroup(H, DerivedSubgroup(H));
Print("[32,8]: H^ab elements liftable at infinity: ",
      Filtered(Elements(Image(q)), c -> RealLiftable(H, q, c)), "\n");

# 20T879: H = 16T749, H0 = the index-2 subgroup [192,1493] fixing sqrt(5).
# Frobenius of L at 5 must be of type (1,1,1,1), (1,1,2) or (1,3).
H := TransitiveGroup(16, 749);
H0 := First(Filtered(NormalSubgroups(H), S -> Index(H, S) = 2), S -> IdGroup(S) = [192, 1493]);
Print("16T749 at p = 5: ", FrobTypesAtSqrt5Prime(H, H0, 5), "\n");
QUIT;
