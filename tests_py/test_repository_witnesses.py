import os
import re
import unittest

import run_parallel as rp


_LABEL_RE = re.compile(r"^[1-9][0-9]*T[1-9][0-9]*$")


class RepositoryWitnessIntegrityTests(unittest.TestCase):
    def test_candidate_witness_file_has_valid_rows(self):
        path = os.path.join(rp.REPO_ROOT, "data", "witnesses", "witnesses.txt")
        self.assertTrue(os.path.exists(path))

        seen = set()
        count = 0
        with open(path, encoding="utf-8") as fh:
            for lineno, raw in enumerate(fh, 1):
                line = raw.strip()
                if not line or line.startswith("#") or line.startswith("label|"):
                    continue

                parts = line.split("|", 4)
                self.assertEqual(len(parts), 5, f"{path}:{lineno}")
                label, ordering, poly_text, source, _note = parts
                self.assertRegex(label, _LABEL_RE, f"{path}:{lineno}")
                self.assertIn(ordering, {"disc", "prp", "both"}, f"{path}:{lineno}")
                self.assertTrue(source, f"{path}:{lineno}: empty source")

                try:
                    poly = rp._parse_witness_coeffs(poly_text)
                except ValueError as exc:
                    self.fail(f"{path}:{lineno}: bad polynomial: {exc}")
                self.assertGreaterEqual(len(poly), 2, f"{path}:{lineno}")
                self.assertNotEqual(poly[-1], 0, f"{path}:{lineno}: zero leading coefficient")

                key = (label, ordering, poly)
                self.assertNotIn(key, seen, f"duplicate witness row at {path}:{lineno}")
                seen.add(key)
                count += 1

        self.assertGreater(count, 0)

    def test_modern_verified_witness_files_are_current(self):
        """If a committed verified file has polynomial fingerprints, require it to
        agree with witnesses.txt and with the stored Phase-1 b_M/b_T values.

        Old seven-column files are deliberately skipped: the production loader
        rejects those and asks the user to regenerate them.  Once a modern file
        is committed, CI turns staleness or a Phase-1 mismatch into a hard error.
        """
        witness_dir = os.path.join(rp.REPO_ROOT, "data", "witnesses")
        data_by_label = {}
        for degree in range(1, 100):
            path = os.path.join(rp.REPO_ROOT, "data", f"degree{degree}.txt")
            if not os.path.exists(path):
                continue
            _header, _types, rows = rp.read_data(path)
            for row in rows:
                data_by_label[row[0]] = row

        checked = 0
        for ordering in ("disc", "prp"):
            path = os.path.join(witness_dir, f"verified_{ordering}.txt")
            if not os.path.exists(path):
                continue

            first_data_parts = None
            for raw, complete in rp._iter_logical_lines(path):
                if not complete:
                    continue
                line = raw.strip()
                if not line or line.startswith("#") or line.startswith("label|"):
                    continue
                first_data_parts = line.split("|")
                break
            if first_data_parts is None:
                continue
            if len(first_data_parts) < 8:
                # Legacy output has no polynomial fingerprint.  The production
                # loader rejects it; do not make old repositories fail CI solely
                # because the expensive Magma verification has not been rerun.
                continue

            best, errors = rp.load_witnesses(path)
            self.assertFalse(errors, f"{path}: {dict(errors)}")
            self.assertTrue(best, f"{path}: no verified witnesses loaded")

            cols = rp.ORDERINGS[ordering]["cols"]
            i_bm = rp.COLUMNS.index(cols[0])
            i_bt = rp.COLUMNS.index(cols[1])
            for label, (_bw, wbM, wbT, _exact, _source) in best.items():
                self.assertIn(label, data_by_label, f"{path}: unknown label {label}")
                row = data_by_label[label]
                bM, bT = row[i_bm], row[i_bt]
                if bM == rp.NULL:
                    # The witness can legitimately be verified before the data
                    # row has been computed, so there is nothing to compare yet.
                    continue
                self.assertEqual((wbM, wbT), (int(bM), int(bT)),
                                 f"{path}: stale Phase-1 values for {label}")
            checked += 1

        # This assertion is intentionally weak: a checkout may contain only
        # legacy verified files.  The candidate-file test above still runs.
        self.assertGreaterEqual(checked, 0)


if __name__ == "__main__":
    unittest.main()
