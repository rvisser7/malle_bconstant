# Cycle-type tables for degree-24 transitive groups (witness search, degree-30
# O_5 family: residuals acting on 24 = 6 blocks x 4 points).
#
#   gap -A -q -o 8g cycle_types_deg24.g
#
# Writes ../tables/cycle_types_deg24.txt and ../tables/index2_subgroups_deg24.txt
# in the same format as the degree-16 tables (see cycle_types.g).
LoadPackage("transgrp");; LoadPackage("smallgrp");;
ORDERS := [192, 384, 768, 1536];
# IdGroup is not available for order 768; those rows get [768, 0].
SafeId := G -> function() if IdGroupsAvailable(Size(G)) then return IdGroup(G); else return [Size(G), 0]; fi; end;
SUBS_FOR := [298, 301, 309, 310, 312, 791, 894, 898, 904, 908, 1575, 1582, 1585, 1588, 1593, 1594];
dir := "../tables/";
out := OutputTextFile(Concatenation(dir, "cycle_types_deg24.txt"), false);
SetPrintFormattingStatus(out, false);
for o in ORDERS do
  for G in AllTransitiveGroups(NrMovedPoints, 24, Size, o) do
    k := TransitiveIdentification(G);
    dist := List(ConjugacyClasses(G),
                 c -> [SortedList(CycleLengths(Representative(c), [1..24])), Size(c)]);
    AppendTo(out, k, "|", Size(G), "|", SafeId(G)(), "|", dist, "\n");
  od;
od;
CloseStream(out);
out := OutputTextFile(Concatenation(dir, "index2_subgroups_deg24.txt"), false);
SetPrintFormattingStatus(out, false);
for k in SUBS_FOR do
  G := TransitiveGroup(24, k);
  for S in Filtered(NormalSubgroups(G), S -> Index(G, S) = 2) do
    dist := List(ConjugacyClasses(S),
                 c -> [SortedList(CycleLengths(Representative(c), [1..24])), Size(c)]);
    AppendTo(out, k, "|", SafeId(S)(), "|", dist, "\n");
  od;
od;
CloseStream(out);
QUIT;
