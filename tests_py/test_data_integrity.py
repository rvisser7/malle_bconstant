import glob
import os
import re
import unittest

import run_parallel as rp


class RepositoryDataIntegrityTests(unittest.TestCase):
    def test_all_degree_files(self):
        seen = set()
        paths = sorted(glob.glob(os.path.join(rp.REPO_ROOT, "data", "degree*.txt")))
        self.assertTrue(paths)

        for path in paths:
            m = re.search(r"degree(\d+)\.txt$", path)
            self.assertIsNotNone(m)
            degree = int(m.group(1))
            header, _, rows = rp.read_data(path)
            self.assertEqual(header.split("|"), rp.COLUMNS)

            for row in rows:
                label = row[0]
                self.assertNotIn(label, seen, f"duplicate label {label}")
                seen.add(label)
                self.assertTrue(label.startswith(f"{degree}T"), (path, label))

                for ordering in ("disc", "prp"):
                    offs = [rp.COLUMNS.index(c) for c in rp.ORDERINGS[ordering]["cols"]]
                    bM, bT, bW, status = (row[o] for o in offs)
                    if bM == rp.NULL:
                        self.assertEqual([bT, bW, status], [rp.NULL, rp.NULL, rp.NULL])
                        continue

                    bM_i, bT_i = int(bM), int(bT)
                    self.assertLessEqual(bM_i, bT_i, (label, ordering))
                    bW_i = None if bW == rp.NULL else int(bW)
                    if bW_i is not None:
                        self.assertLessEqual(bM_i, bW_i, (label, ordering))
                        self.assertLessEqual(bW_i, bT_i, (label, ordering))

                    # A small number of older computed rows predate status=4.
                    # They are allowed only in the genuinely unresolved shape.
                    if status == rp.NULL:
                        self.assertIsNone(bW_i, (label, ordering))
                        self.assertLess(bM_i, bT_i, (label, ordering))
                        continue

                    self.assertIn(status, {"0", "1", "2", "3", "4"})
                    if status == "0":
                        self.assertEqual((bW_i, bT_i), (bM_i, bM_i))
                    elif status == "1":
                        self.assertTrue(bW_i is not None and bM_i < bW_i == bT_i)
                    elif status == "2":
                        self.assertTrue(bW_i is not None and bM_i == bW_i < bT_i)
                    elif status == "3":
                        self.assertLess(bM_i, bT_i)
                        if bW_i is not None:
                            self.assertTrue(bM_i < bW_i < bT_i)
                    elif status == "4":
                        self.assertIsNone(bW_i)
                        self.assertLess(bM_i, bT_i)


if __name__ == "__main__":
    unittest.main()
