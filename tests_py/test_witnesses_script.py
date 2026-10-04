import unittest

from run_parallel import NULL
from scripts.witnesses import classify


class WitnessClassificationTests(unittest.TestCase):
    def test_every_classification_branch(self):
        cases = [
            ((NULL, NULL, NULL, NULL), (2, 1, 2, True, "x"), "not-computed"),
            (("1", "3", NULL, "4"), (2, 1, 2, True, "x"), "CONFLICT"),
            (("1", "3", NULL, "4"), (4, 1, 3, True, "x"), "CONFLICT"),
            (("2", "5", NULL, "4"), (2, 2, 5, True, "x"), "no-gain"),
            (("1", "5", "4", "3"), (3, 1, 5, True, "x"), "consistent"),
            (("1", "5", "3", "3"), (4, 1, 5, True, "x"), "CONFLICT"),
            (("1", "5", NULL, "4"), (5, 1, 5, True, "x"), "settles"),
            (("1", "5", NULL, "4"), (3, 1, 5, False, "x"), "raises"),
        ]
        for stored, witness, want in cases:
            with self.subTest(want=want):
                got, _ = classify(stored, witness)
                self.assertEqual(got, want)


if __name__ == "__main__":
    unittest.main()
