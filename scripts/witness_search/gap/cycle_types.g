# Regenerate the cycle-type tables used by wslib.identify / wslib.sqrt5_subgroup.
#
#   gap -q -o 8g cycle_types.g
#
# Writes (into ../tables/):
#   cycle_types_deg16.txt      k|order|IdGroup|[[cycle type, class size], ...]
#                              for every 16Tk whose order is in ORDERS
#   index2_subgroups_deg16.txt k|IdGroup(S)|[[cycle type, class size], ...]
#                              for every index-2 subgroup S of 16Tk, k in SUBS_FOR
#
# The tables only drive the *search* (cheap candidate identification by
# Frobenius statistics).  Nothing in them is trusted: every witness found this
# way is re-proved by magma/verify_witnesses_<ordering>.m.

ORDERS := [32, 64, 192, 384];
SUBS_FOR := [40, 140, 148, 153, 160, 154, 174, 176, 740, 749, 759];

dir := "../tables/";
out := OutputTextFile(Concatenation(dir, "cycle_types_deg16.txt"), false);
SetPrintFormattingStatus(out, false);
for k in [1..NrTransitiveGroups(16)] do
  G := TransitiveGroup(16, k);
  if Size(G) in ORDERS then
    dist := List(ConjugacyClasses(G),
                 c -> [SortedList(CycleLengths(Representative(c), [1..16])), Size(c)]);
    AppendTo(out, k, "|", Size(G), "|", IdGroup(G), "|", dist, "\n");
  fi;
od;
CloseStream(out);

out := OutputTextFile(Concatenation(dir, "index2_subgroups_deg16.txt"), false);
SetPrintFormattingStatus(out, false);
for k in SUBS_FOR do
  G := TransitiveGroup(16, k);
  for S in Filtered(NormalSubgroups(G), S -> Index(G, S) = 2) do
    dist := List(ConjugacyClasses(S),
                 c -> [SortedList(CycleLengths(Representative(c), [1..16])), Size(c)]);
    AppendTo(out, k, "|", IdGroup(S), "|", dist, "\n");
  od;
od;
CloseStream(out);
QUIT;
