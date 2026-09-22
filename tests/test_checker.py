"""独立局部转移包含性检查器测试。

重点：
* 检查器与具体执行参考在源码层不依赖被测核心（不 import 核心模块）；
* 包含性由符号端点证明，伪造/过紧的证书必须被抓到；
* 不存在任何采样代码路径。
"""

import pathlib
import unittest

from interval_ai import analyze, check_analysis, check_block_transfer
from interval_ai.checker import PROOF_METHOD, compute_block_image

from tests.programs import (
    bounded_two_branch_program,
    correlated_loop_program,
    infinite_growth_program,
    two_back_edges_program,
    unreachable_branch_program,
)

ROOT = pathlib.Path(__file__).resolve().parents[1]


class TestIndependence(unittest.TestCase):
    def test_checker_does_not_import_core(self):
        src = (ROOT / "interval_ai" / "checker.py").read_text(encoding="utf-8")
        for forbidden in (
            "interval_ai.interval",
            "interval_ai.state",
            "interval_ai.semantics",
            "interval_ai.analyzer",
            "from .interval",
            "from .state",
            "from .semantics",
            "from .analyzer",
        ):
            self.assertNotIn(forbidden, src, f"checker 不得复用核心实现: {forbidden}")
        self.assertIn("from .cfg import", src)

    def test_reference_does_not_import_core(self):
        src = (ROOT / "interval_ai" / "reference.py").read_text(encoding="utf-8")
        for forbidden in (
            "interval_ai.interval",
            "interval_ai.state",
            "interval_ai.semantics",
            "interval_ai.analyzer",
            "interval_ai.checker",
            "from .interval",
            "from .state",
            "from .semantics",
            "from .analyzer",
            "from .checker",
        ):
            self.assertNotIn(forbidden, src, f"reference 不得复用核心实现: {forbidden}")

    def test_proof_is_symbolic_not_sampling(self):
        self.assertIn("symbolic", PROOF_METHOD)
        # 检查器源码中不得出现随机采样/枚举取值的设施
        src = (ROOT / "interval_ai" / "checker.py").read_text(encoding="utf-8")
        for banned in ("random", "sample(", "randrange", "randint", "fuzz"):
            self.assertNotIn(banned, src)


class TestLocalBlockTransfer(unittest.TestCase):
    def setUp(self):
        self.prog = bounded_two_branch_program()

    def _entry(self, x_iv, y_iv):
        return {"x": x_iv, "y": y_iv}

    def test_exact_claim_holds(self):
        # h: 入口 x∈[0,6], y∈[0,3]；x<=5 真边 x∈[0,5]，假边 x∈[6,6]
        report = check_block_transfer(
            self.prog,
            "h",
            self._entry((0, 6), (0, 3)),
            {
                "body": self._entry((0, 5), (0, 3)),
                "done": self._entry((6, 6), (0, 3)),
            },
        )
        self.assertTrue(report.holds, [i.detail for i in report.items if not i.holds])

    def test_over_approx_claim_holds(self):
        # 声称更宽的边状态仍然是可靠证书
        report = check_block_transfer(
            self.prog,
            "h",
            self._entry((0, 6), (0, 3)),
            {
                "body": self._entry((None, None), (None, None)),
                "done": self._entry((0, None), (None, None)),
            },
        )
        self.assertTrue(report.holds)

    def test_too_tight_claim_rejected(self):
        # 真边实际含 x=5，声称 [0,4] 必须被判定不包含
        report = check_block_transfer(
            self.prog,
            "h",
            self._entry((0, 6), (0, 3)),
            {
                "body": self._entry((0, 4), (0, 3)),
                "done": self._entry((6, 6), (0, 3)),
            },
        )
        self.assertFalse(report.holds)
        fails = report.failures()
        self.assertTrue(any("h->body" in f.location for f in fails))

    def test_falsely_claimed_unreachable_rejected(self):
        # 实际两边都可达；把真边声称为 None（不可达）必须失败
        report = check_block_transfer(
            self.prog,
            "h",
            self._entry((0, 6), (0, 3)),
            {"body": None, "done": self._entry((6, 6), (0, 3))},
        )
        self.assertFalse(report.holds)

    def test_unreachable_input_proves_both_edges_bottom(self):
        report = check_block_transfer(
            self.prog,
            "h",
            None,
            {"body": None, "done": None},
        )
        self.assertTrue(report.holds)

    def test_unreachable_input_any_claim_holds(self):
        # bottom 含于一切：不可达入口下，把边声称为任何（含可达）状态
        # 都不是不可靠的证书——这正是过近似的含义。
        report = check_block_transfer(
            self.prog,
            "h",
            None,
            {"body": self._entry((0, 5), (0, 3)), "done": None},
        )
        self.assertTrue(report.holds)

    def test_missing_claim_rejected(self):
        # 声称证书缺边则结构不完整
        report = check_block_transfer(
            self.prog, "h", self._entry((0, 6), (0, 3)), {"body": None}
        )
        self.assertFalse(report.holds)
        self.assertTrue(any(i.name == "edge_claim_present" for i in report.items))


class TestEndToEndCertificates(unittest.TestCase):
    def test_all_fixture_results_certified(self):
        for make in (
            bounded_two_branch_program,
            correlated_loop_program,
            infinite_growth_program,
            two_back_edges_program,
            unreachable_branch_program,
        ):
            with self.subTest(prog=make.__name__):
                prog = make()
                res = analyze(prog)
                report = check_analysis(prog, res)
                self.assertTrue(
                    report.holds,
                    f"{make.__name__}: " + "; ".join(f.detail for f in report.failures()),
                )
                self.assertIn("symbolic", report.proof_method)

    def test_tampered_invariant_rejected(self):
        # 手工构造一个被篡改的“结果”：把 done 块的入不变量改宽到漏掉下界，
        # 并谎称断言 proved —— 独立证书检查必须拒绝。
        from types import SimpleNamespace

        from interval_ai import State
        from interval_ai.interval import Interval

        prog = correlated_loop_program()
        good = analyze(prog)

        tampered_in = dict(good.in_states)
        tampered_in["done"] = State(
            tuple(
                Interval(None, 11) if v == "x" else Interval(0, 11)
                for v in prog.variables
            )
        )
        fake = SimpleNamespace(
            in_states=tampered_in,
            edge_states=good.edge_states,
            status_of=good.status_of,
        )
        report = check_analysis(prog, fake)
        self.assertFalse(report.holds)

    def test_compute_block_image_is_exact_for_affine_subset(self):
        # 独立公式自验：x=0,y=0 进入 body(x+=1,y+=1) 后精确为 (1,1)
        prog = correlated_loop_program()
        img = compute_block_image(
            prog.block_map["body"],
            {"x": (0, 10), "y": (0, 10)},
            prog,
        )
        self.assertEqual(img.exit_env, {"x": (1, 11), "y": (1, 11)})
        self.assertEqual(img.edges["h"], {"x": (1, 11), "y": (1, 11)})


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
