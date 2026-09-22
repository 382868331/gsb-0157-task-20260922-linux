"""引擎行为测试：有界/无界循环、不可达分支、收窄改善、两个回边。

期望区间均为手算后硬编码，不调用引擎生成期望值。
"""

import unittest

from interval_ai import analyze, Interval, check_local_soundness
from interval_ai.engine import MAX_NARROWING_ROUNDS

from tests._programs import (
    bounded_count_program,
    copy_program,
    two_backedges_program,
    unbounded_growth_program,
    unreachable_branch_program,
)


class TestBoundedCount(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = bounded_count_program(4)
        self.res = analyze(self.cfg)

    def test_widen_point_and_termination(self) -> None:
        self.assertEqual(self.res.widen_points, ("head",))
        # 第三次扩张起加宽：init->[0,0](1), [0,1](2 join), +inf(3 widen),
        # 再传播一轮到稳定；收窄至少发生 1 轮
        self.assertGreaterEqual(self.res.ascending_rounds, 3)
        self.assertLessEqual(self.res.narrowing_rounds, MAX_NARROWING_ROUNDS)

    def test_final_invariants(self) -> None:
        self.assertEqual(self.res.block_in["head"].get("i"), Interval(0, 5))
        self.assertEqual(self.res.block_in["body"].get("i"), Interval(0, 4))
        self.assertEqual(self.res.block_in["exit"].get("i"), Interval(5, 5))

    def test_narrowing_actually_refines(self) -> None:
        # 收窄前退出支只能证明 [5, +inf)，收窄后精确到 [5, 5]
        self.assertEqual(
            self.res.post_widening_in["exit"].get("i"), Interval(5, None)
        )
        self.assertEqual(self.res.block_in["exit"].get("i"), Interval(5, 5))
        self.assertTrue(self.res.narrowing_refined)

    def test_asserts_proved(self) -> None:
        verdicts = {(a.block, a.index): a.verdict for a in self.res.asserts}
        self.assertEqual(verdicts[("body", 0)], "proved")
        self.assertEqual(verdicts[("exit", 0)], "proved")

    def test_independent_soundness(self) -> None:
        report = check_local_soundness(self.res)
        self.assertTrue(report.ok, report.violations)


class TestUnboundedGrowth(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(unbounded_growth_program())

    def test_head_is_unbounded_above(self) -> None:
        self.assertEqual(self.res.block_in["head"].get("i"), Interval(0, None))

    def test_exit_unreachable(self) -> None:
        self.assertTrue(self.res.block_in["exit"].bottom)

    def test_assert_verdicts(self) -> None:
        # 第一条 assert i>=0（上端无穷）可证；第二条 assert i<=5 不可证
        lows = {a.statement.lower: a.verdict for a in self.res.asserts}
        uppers = {a.statement.upper: a.verdict for a in self.res.asserts}
        self.assertEqual(lows[0], "proved")
        self.assertEqual(uppers[5], "unknown")

    def test_soundness(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestUnreachableBranch(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(unreachable_branch_program())

    def test_dead_block_is_bottom(self) -> None:
        self.assertTrue(self.res.block_in["dead"].bottom)
        self.assertTrue(self.res.block_out["dead"].bottom)

    def test_dead_assert_is_vacuously_proved(self) -> None:
        st = next(a for a in self.res.asserts if a.block == "dead")
        self.assertEqual(st.verdict, "proved")
        self.assertTrue(st.vacuous)

    def test_live_branch_exact(self) -> None:
        self.assertEqual(self.res.block_in["cont"].get("x"), Interval(0, 0))

    def test_soundness(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestTwoBackedges(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(two_backedges_program())

    def test_single_widen_head_with_two_back_edges(self) -> None:
        from interval_ai.engine import _dfs_back_edges_and_order

        self.assertEqual(self.res.widen_points, ("head",))
        back_edges, _ = _dfs_back_edges_and_order(self.res.cfg)
        self.assertEqual({dst for _, dst in back_edges}, {"head"})
        self.assertEqual(
            sorted(src for src, dst in back_edges), ["step1", "step2"]
        )
        # 两个步进块都把控制流送回 head：这就是头的两个回边来源
        self.assertEqual(self.res.cfg.blocks["step1"].successors, ("head",))
        self.assertEqual(self.res.cfg.blocks["step2"].successors, ("head",))

    def test_invariant_covers_both_increments(self) -> None:
        # +1 与 +2 两个回边都贡献凸包：头上界到 11（9+2）
        self.assertEqual(self.res.block_in["head"].get("i"), Interval(0, 11))

    def test_assert_proved_and_sound(self) -> None:
        self.assertEqual(self.res.asserts[0].verdict, "proved")
        self.assertTrue(check_local_soundness(self.res).ok)


class TestCopyAndNegativeConst(unittest.TestCase):
    def test_copy_chain(self) -> None:
        res = analyze(copy_program())
        blk = res.block_in["start"]
        self.assertEqual(blk.get("a"), Interval.top())  # 入状态未赋值
        out = res.block_out["start"]
        self.assertEqual(out.get("a"), Interval(3, 3))
        self.assertEqual(out.get("b"), Interval(3, 3))
        self.assertEqual(out.get("c"), Interval(2, 2))
        self.assertEqual(res.asserts[0].verdict, "proved")
        self.assertTrue(check_local_soundness(res).ok)


if __name__ == "__main__":
    unittest.main()
