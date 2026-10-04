import os
import tempfile
import unittest

import run_parallel as rp


class BValuesTests(unittest.TestCase):
    def test_all_status_shapes(self):
        cases = [
            ((3, 3, 3, 3), ["3", "3", "3", "0"]),
            ((1, 4, 4, 4), ["1", "4", "4", "1"]),
            ((2, 7, 2, 2), ["2", "7", "2", "2"]),
            ((1, 7, 4, 4), ["1", "7", "4", "3"]),
            ((1, 7, 2, 6), ["1", "7", rp.NULL, "3"]),
            ((1, 7, 1, 5), ["1", "7", rp.NULL, "4"]),
            ((1, 7, 3, 7), ["1", "7", rp.NULL, "4"]),
        ]
        for args, want in cases:
            with self.subTest(args=args):
                self.assertEqual(rp.b_values(*args), want)


class DataIOTests(unittest.TestCase):
    def test_round_trip(self):
        header = "|".join(rp.COLUMNS)
        types = "|".join(["text"] + ["smallint"] * (len(rp.COLUMNS) - 1))
        rows = [
            ["3T1", "1", "1", "1", "0", "2", "2", "2", "0"],
            ["3T2", "1", "2", rp.NULL, "4", rp.NULL, rp.NULL, rp.NULL, rp.NULL],
        ]
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, "degree3.txt")
            rp.write_data(path, header, types, rows)
            got = rp.read_data(path)
        self.assertEqual(got, (header, types, rows))

    def test_bad_column_count_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, "bad.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("|".join(rp.COLUMNS) + "\n")
                fh.write("|".join(["text"] * len(rp.COLUMNS)) + "\n\n")
                fh.write("3T1|1|1\n")
            with self.assertRaises(ValueError):
                rp.read_data(path)


class CompareRowTests(unittest.TestCase):
    def test_status_four_is_placeholder(self):
        old = ["1", "4", rp.NULL, "4"]
        new = ["1", "4", "2", "3"]
        verdict, detail = rp.compare_row("X", old, new, ["b", "bT", "bW", "status"])
        self.assertEqual((verdict, detail), ("match", ""))

    def test_stored_exact_value_cannot_disappear(self):
        old = ["1", "4", "2", "3"]
        new = ["1", "4", rp.NULL, "3"]
        verdict, detail = rp.compare_row("X", old, new, ["b", "bT", "bW", "status"])
        self.assertEqual(verdict, "mismatch")
        self.assertIn("bW", detail)


class WitnessLoaderTests(unittest.TestCase):
    def _write_source(self, td, rows):
        path = os.path.join(td, "witnesses.txt")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("label|ordering|coefficients|source|notes\n")
            for row in rows:
                fh.write(row + "\n")
        return path

    def _write_verified(self, td, rows):
        path = os.path.join(td, "verified_disc.txt")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("label|b_witness|identification_exact|b_M|b_T|survivors|source|poly\n")
            for row in rows:
                fh.write(row + "\n")
        return path

    def test_largest_current_witness_is_kept(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_source(td, [
                "6T5|disc|[4,0,0,-2,0,0,1]|first|",
                "6T5|disc|[1,0,1]|second|",
            ])
            verified = self._write_verified(td, [
                "6T5|2|1|1|3|1|first|[4,0,0,-2,0,0,1]",
                "6T5|3|1|1|3|1|second|[1,0,1]",
            ])
            best, errors = rp.load_witnesses(verified)
        self.assertFalse(errors)
        self.assertEqual(best["6T5"][:3], (3, 1, 3))
        self.assertEqual(best["6T5"][4], "second")

    def test_stale_polynomial_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_source(td, ["6T5|disc|[1,0,1]|current|"])
            verified = self._write_verified(td, [
                "6T5|2|1|1|2|1|old|[4,0,0,-2,0,0,1]",
            ])
            best, errors = rp.load_witnesses(verified)
        self.assertNotIn("6T5", best)
        self.assertTrue(any("stale verified witness" in x for x in errors["6T5"]))

    def test_magma_wrapped_verified_row_is_accepted(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_source(td, [
                "20T105|disc|[1711,9889,19169,19024,28871,3012]|fixture|",
            ])
            path = os.path.join(td, "verified_disc.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("label|b_witness|identification_exact|b_M|b_T|survivors|source|poly\n")
                fh.write("20T105|3|1|2|3|1|fixture|[1711,9889,19169,\\\n")
                fh.write("19024,28871,3012]\n")
            best, errors = rp.load_witnesses(path)
        self.assertFalse(errors)
        self.assertEqual(best["20T105"][:3], (3, 2, 3))

    def test_legacy_verified_row_is_rejected_when_source_exists(self):
        with tempfile.TemporaryDirectory() as td:
            self._write_source(td, ["6T5|disc|[1,0,1]|current|"])
            path = os.path.join(td, "verified_disc.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("label|b_witness|exact|b_M|b_T|survivors|source\n")
                fh.write("6T5|2|1|1|2|1|legacy\n")
            best, errors = rp.load_witnesses(path)
        self.assertNotIn("6T5", best)
        self.assertTrue(any("legacy verified witness" in x for x in errors["6T5"]))

    def test_apply_witness_and_conflicts(self):
        witnesses = {"6T5": (2, 1, 2, True, "fixture")}
        lo, conflict = rp.apply_witness("6T5", 1, 2, 1, 2, witnesses)
        self.assertEqual(lo, 2)
        self.assertIsNone(conflict)

        _, conflict = rp.apply_witness("6T5", 1, 3, 1, 3, witnesses)
        self.assertIn("has b_M=1, b_T=2", conflict)

        too_big = {"6T5": (4, 1, 4, True, "fixture")}
        _, conflict = rp.apply_witness("6T5", 1, 4, 1, 3, too_big)
        self.assertIn("upper bound is 3", conflict)


if __name__ == "__main__":
    unittest.main()
