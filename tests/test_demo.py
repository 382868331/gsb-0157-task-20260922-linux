"""demo.py 子进程回归：真实计算、真实异常边界、在 8 秒预算内正常退出。"""

import os
import subprocess
import sys
import time
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestDemoProcess(unittest.TestCase):
    def test_demo_runs_and_prints_required_sections(self) -> None:
        start = time.monotonic()
        proc = subprocess.run(
            [sys.executable, "demo.py"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=8,
        )
        elapsed = time.monotonic() - start
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertLess(elapsed, 8.0)
        self.assertIn("PROVED", proc.stdout)
        self.assertIn("UNKNOWN", proc.stdout)
        self.assertIn("ValidationError", proc.stdout)
        self.assertIn("收窄改善", proc.stdout)
        # 不得包含预录/休眠痕迹
        self.assertNotIn("sleep", proc.stdout.lower())


if __name__ == "__main__":
    unittest.main()
