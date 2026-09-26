"""demo_iteration.py 子进程回归。"""

import os
import subprocess
import sys
import time
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestIterationDemo(unittest.TestCase):
    def test_demo_runs_within_90_seconds_and_prints_certificates(self) -> None:
        start = time.monotonic()
        proc = subprocess.run(
            [sys.executable, "demo_iteration.py"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=90,
        )
        elapsed = time.monotonic() - start
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertLess(elapsed, 90.0)
        self.assertIn("≡0 (mod 2)", proc.stdout)
        self.assertIn("gcd(2,3)=1", proc.stdout)
        self.assertIn("dead.bottom=True", proc.stdout)
        self.assertIn("无合法同余点", proc.stdout)
        self.assertIn("整体局部转移包含检查：通过", proc.stdout)
        self.assertIn("ValidationError", proc.stdout)


if __name__ == "__main__":
    unittest.main()
