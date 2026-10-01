# Tests

Run from `magma/`, not from here:

    magma -b tests/test_q8_witt.m
    magma -b tests/test_wreath.m
    magma -b tests/test_orbits_agree_disc.m
    magma -b tests/test_orbits_agree_prp.m
    magma -b tests/run_disc_tests.m
    magma -b tests/run_prp_tests.m

`test_q8_witt.m` replaces a claim that used to live only in a comment.
`test_wreath.m` exercises structural shape (3), which two bugs had silently
disabled. The two `run_*_tests.m` assert `b_M` and `b_T` against the worked
examples in arXiv:2502.04261 (Examples 1.1, 3.5, 3.6 and Lemmas 3.1, 3.7), and
assert only `b_M <= L <= U <= b_T` for the bracket, which is allowed to move.

`../diagnose_disc.m` and `../diagnose_prp.m` are not tests: they measure how many
published cells the local-policy correction changes.
