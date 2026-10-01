# Tests

Run from `magma/`, not from here:

    magma -b tests/test_q8_witt.m
    magma -b tests/test_wreath.m
    magma -b tests/test_orbits_agree_disc.m
    magma -b tests/test_orbits_agree_prp.m
    magma -b tests/test_gpiphi_pruning.m
    magma -b tests/test_layer_allowed.m
    magma -b tests/run_disc_tests.m
    magma -b tests/run_prp_tests.m

`test_q8_witt.m` replaces a claim that used to live only in a comment.
`test_wreath.m` exercises structural shape (3), which two bugs had silently
disabled. `test_gpiphi_pruning.m` checks the pruned pair enumeration against
the old one. `test_layer_allowed.m` checks the split-tower layer rule
(nilpotent by NSW (9.6.10), or odd with the mu(K) condition of (9.5.8)). The two `run_*_tests.m` build their groups with `WreathProduct`
(not hard-coded indices: "20T27" was never C5 wr C4), assert `b_M` and `b_T`
exactly, and assert `b_W` exactly where it is proven (Wang Thm 1.3 with the
2-part corrected); otherwise only `b_M <= L <= U <= b_T`. Pass `slow:=1` to
include C5 wr C8 (disc) and C4 wr C4 (prp):

    magma -b slow:=1 tests/run_disc_tests.m

`../diagnose_disc.m` and `../diagnose_prp.m` are not tests: they measure how many
published cells the local-policy correction changes.
