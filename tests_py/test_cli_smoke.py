import os
import subprocess
import sys
import unittest

import run_parallel as rp


class CommandLineSmokeTests(unittest.TestCase):
    def _run_help(self, relative_path):
        proc = subprocess.run(
            [sys.executable, os.path.join(rp.REPO_ROOT, relative_path), "--help"],
            cwd=rp.REPO_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("usage:", proc.stdout.lower())

    def test_run_parallel_help(self):
        self._run_help("run_parallel.py")

    def test_witnesses_help(self):
        self._run_help(os.path.join("scripts", "witnesses.py"))


if __name__ == "__main__":
    unittest.main()
