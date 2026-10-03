// =====================================================================
// tests/test_gar.m  --  the GAR table and GAR layers
// =====================================================================
//
//     magma -b tests/test_gar.m      (run from magma/)
//
// Checks IsGARSimpleOrder against [MM99] Ch. IV (Thm 4.3, Ex. 4.1, 4.2),
// in particular the entries that are NOT there (A6, L2(8), M23), and
// IsGARLayer on the socles of the groups that motivated the GAR layer rule:
//   15T95, 18T933  socle A5^3       -> GAR layer
//   18T937, 18T938 socle L2(8)^2    -> not (L2(8) is not on the list)

load "lib/records.m";
load "lib/splitting.m";
load "lib/split_tower.m";
load "lib/certificates/structural.m";

failures := 0;
Check := procedure(name, got, want, ~failures)
    printf "  %-48o %o (expected %o)\n", name, got, want;
    if got ne want then failures +:= 1; end if;
end procedure;

G := func< x | IsGARSimpleOrder(x) >;

Check("A5 (60)",                       G(60),        true,  ~failures);
Check("A6 (360): excluded, Thm 4.3(a)", G(360),       false, ~failures);
Check("A7 (2520)",                     G(2520),      true,  ~failures);
Check("L2(7) (168): (3/7) = -1",       G(168),       true,  ~failures);
Check("L2(8) (504): not L2(p)",        G(504),       false, ~failures);
Check("L2(11) (660): (2/11) = -1",     G(660),       true,  ~failures);
Check("L2(16) (4080): not on list",    G(4080),      false, ~failures);
Check("A8 = L3(4) order (20160)",      G(20160),     true,  ~failures);
Check("L3(3) (5616), Ex. 4.1",         G(5616),      true,  ~failures);
Check("U3(3) (6048), Thm 4.3(d)",      G(6048),      true,  ~failures);
Check("S4(3) (25920), Thm 4.3(e)",     G(25920),     true,  ~failures);
Check("M11 (7920)",                    G(7920),      true,  ~failures);
Check("M23 (10200960): excluded",      G(10200960),  false, ~failures);
Check("|O7(3)| = |S6(3)|: ambiguous",  G(4585351680), false, ~failures);

// Orders computed here must agree with the table (guards against typos).
Check("#PSL(3,3) in table",  G(#PSL(3,3)),  true, ~failures);
Check("#PSU(3,3) in table",  G(#PSU(3,3)),  true, ~failures);
Check("#PSp(4,3) in table",  G(#PSp(4,3)),  true, ~failures);
Check("#PSp(6,2) in table",  G(#PSp(6,2)),  true, ~failures);
Check("#PSL(3,5) in table",  G(#PSL(3,5)),  true, ~failures);

Check("HasGAROverQ(Alt(6))",          HasGAROverQ(Alt(6)), false, ~failures);
Check("HasGAROverQ(Alt(5))",          HasGAROverQ(Alt(5)), true,  ~failures);
Check("HasGAROverQ(PSL(2,8))",        HasGAROverQ(PSL(2,8)), false, ~failures);
Check("KnownRegularTableOverQ(Alt(6)) (Hilbert)",
      KnownRegularTableOverQ(Alt(6)), true, ~failures);

Check("IsGARLayer(A5 x A5)", IsGARLayer(DirectProduct(Alt(5), Alt(5))), true, ~failures);
Check("IsGARLayer(A5 x C2)", IsGARLayer(DirectProduct(Alt(5), CyclicGroup(2))), false, ~failures);
Check("IsGARLayer(S5): C2 factor", IsGARLayer(Sym(5)), false, ~failures);

for x in [ <15, 95, true>, <18, 933, true>, <18, 937, false>, <18, 938, false> ] do
    T := TransitiveGroup(x[1], x[2]);
    Check(Sprintf("IsGARLayer(Socle(%oT%o))", x[1], x[2]),
          IsGARLayer(Socle(T)), x[3], ~failures);
end for;

// The tower now accepts the socle of 15T95 without a complement check, and
// G/socle = C6 then splits: every pi for this group is fully split.
T := TransitiveGroup(15, 95);
assert #T eq 1296000;
cands := AdmissibleCandidates(T, DerivedSubgroup(T));
Check("15T95: socle is a tower candidate",
      exists{ M : M in cands | M eq Socle(T) }, true, ~failures);

printf "test_gar: %o failures\n", failures;
assert failures eq 0;
print "test_gar: PASS";
quit;
