# Tests

Run from `magma/`, not from here:

    magma -b tests/test_q8_witt.m
    magma -b tests/test_wreath.m
    magma -b tests/test_orbits_agree_disc.m
    magma -b tests/test_orbits_agree_prp.m
    magma -b tests/test_gpiphi_pruning.m
    magma -b tests/test_layer_allowed.m
    magma -b tests/test_gar.m
    magma -b tests/test_witness.m
    magma -b tests/run_disc_tests.m
    magma -b tests/run_prp_tests.m

`test_q8_witt.m` replaces a claim that used to live only in a comment.
`test_wreath.m` exercises structural shape (3), which two bugs had silently
disabled. `test_gpiphi_pruning.m` checks the pruned pair enumeration against
the old one. `test_layer_allowed.m` checks the split-tower layer rule
(nilpotent by NSW (9.6.10), or odd with the mu(K) condition of (9.5.8)).
`test_gar.m` checks the GAR table against [MM99] Ch. IV -- including the
entries that must be ABSENT (A6, L2(8), M23) -- and the GAR layer rule on
15T95 / 18T933 (socle A5^3, a GAR layer) and 18T937 / 18T938 (socle
L2(8)^2, not one). The two `run_*_tests.m` build their groups with `WreathProduct`
(not hard-coded indices: "20T27" was never C5 wr C4), assert `b_M` and `b_T`
exactly, and assert `b_W` exactly where it is proven (Wang Thm 1.3 with the
2-part corrected); otherwise only `b_M <= L <= U <= b_T`. Pass `slow:=1` to
include C5 wr C8 (disc), and C4 wr C4 and 15T95 = A5^3 : C6 (prp):

    magma -b slow:=1 tests/run_disc_tests.m

`../diagnose_disc.m` and `../diagnose_prp.m` are not tests: they measure how many
published cells the local-policy correction changes. Likewise
`../diagnose_intersection_*.m` (does README assumption 3 move any lower
bound?), `../diagnose_supplements_*.m` (what would the experimental
supplement certificate add?) and `../diagnose_marking_*.m` (could the one
unverified part of the p = 2 Demushkin marking in `wild_prop.m` move any
verdict?).

`test_witness.m` checks witness-field verification (`lib/witness_body.m`)
on two small fields with hand-known answers (6T5 = C3 wr C2 containing
Q(sqrt -3), and S3 with no cyclotomic part) and on a deliberately wrong label.
