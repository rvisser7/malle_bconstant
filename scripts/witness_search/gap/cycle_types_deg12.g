# Cycle-type table for all degree-12 transitive groups (witness search, degree-30
# O_5 family: residuals K6(sqrt delta) over sextic fields, e.g. 30T4059).
#
#   gap -A -q cycle_types_deg12.g
#
# Writes ../tables/cycle_types_deg12.txt in the format of the degree-16 table.
LoadPackage("transgrp");; LoadPackage("smallgrp");;
SafeId := G -> function() if IdGroupsAvailable(Size(G)) then return IdGroup(G); else return [Size(G), 0]; fi; end;
out := OutputTextFile("../tables/cycle_types_deg12.txt", false);
SetPrintFormattingStatus(out, false);
for k in [1 .. NrTransitiveGroups(12)] do
  G := TransitiveGroup(12, k);
  dist := List(ConjugacyClasses(G),
               c -> [SortedList(CycleLengths(Representative(c), [1..12])), Size(c)]);
  AppendTo(out, k, "|", Size(G), "|", SafeId(G)(), "|", dist, "\n");
od;
CloseStream(out);
QUIT;
