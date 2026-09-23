"""差界矩阵域（DBM）与归约积的单元测试。

期望值全部手算（差界边编号、Floyd-Warshall 闭包结果硬编码），不调用
引擎或被测分析生成期望；只用最朴素的矩阵构造搭初态。
"""

import unittest

from interval_ai import Interval
from interval_ai.dbm import (
    DiffState,
    ProductState,
    _closure,
    _fresh_matrix,
)
from interval_ai.cfg import (
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
    Guard,
)


VARS = ("x", "y", "z")


def _top(vars_=VARS) -> ProductState:
    return ProductState.from_intervals(tuple(vars_), {v: Interval.top() for v in vars_})


class TestClosureBasics(unittest.TestCase):
    def test_fresh_matrix_only_diagonal(self) -> None:
        m = _fresh_matrix(3)  # Z, x, y
        self.assertEqual(m[0][0], 0)
        self.assertEqual(m[1][1], 0)
        self.assertIsNone(m[1][2])
        self.assertIsNone(m[2][1])

    def test_transitive_path_closes(self) -> None:
        # x - y <= 1 即 M[x][y]=1（x 节点1, y 节点2）；y - z <= 1 即 M[2][3]=1
        m = [list(r) for r in _fresh_matrix(4)]
        m[1][2] = 1
        m[2][3] = 1
        closed = _closure(tuple(tuple(r) for r in m))
        # 闭包推出 x - z <= 2
        self.assertEqual(closed[1][3], 2)

    def test_negative_cycle_detected(self) -> None:
        # x - y <= 0 与 y - x <= -1 矛盾（x <= y <= x-1）
        m = [list(r) for r in _fresh_matrix(3)]
        m[1][2] = 0
        m[2][1] = -1
        self.assertIsNone(_closure(tuple(tuple(r) for r in m)))


class TestAssignments(unittest.TestCase):
    def test_const_fixes_zero_edges_only(self) -> None:
        s = _top(("x", "y")).assign_const("y", 3)
        self.assertEqual(s.get("y"), Interval(3, 3))
        self.assertEqual(s.get("x"), Interval.top())
        self.assertIsNone(s.as_diff_state().bound("y", "x"))

    def test_copy_gives_two_zero_bounds(self) -> None:
        s = _top(("x", "y")).assign_copy("y", "x")
        d = s.as_diff_state()
        self.assertEqual(d.bound("y", "x"), 0)
        self.assertEqual(d.bound("x", "y"), 0)

    def test_add_constant_bounds(self) -> None:
        s = _top(("x", "y")).assign_add("y", "x", 1)
        d = s.as_diff_state()
        self.assertEqual(d.bound("y", "x"), 1)
        self.assertEqual(d.bound("x", "y"), -1)
        self.assertEqual(d.entails("y", "x", 1), True)
        self.assertEqual(d.entails("y", "x", 0), False)

    def test_self_increment_keeps_offset_to_third_var(self) -> None:
        # y = x; x = x + 1 => y = x_old = x_new - 1
        s = _top(("x", "y")).assign_copy("y", "x").assign_add("x", "x", 1)
        d = s.as_diff_state()
        self.assertEqual(d.bound("y", "x"), -1)
        self.assertEqual(d.bound("x", "y"), 1)
        self.assertEqual(d.entails("y", "x", -2), False)

    def test_reassign_forgets_old_relation(self) -> None:
        # y = x; x = 10：y 与新 x 之间不再有 y==x，但经零节点 y-x<=-7
        s = (
            _top(("x", "y"))
            .assign_const("x", 3)
            .assign_copy("y", "x")
            .assign_const("x", 10)
        )
        d = s.as_diff_state()
        # 经零节点：y<=3 且 x>=10，故 y - x <= 3 - 10 = -7（精确）
        self.assertEqual(d.bound("y", "x"), -7)
        self.assertEqual(d.bound("x", "y"), 7)
        # 但不蕴含更强的 -8
        self.assertFalse(d.entails("y", "x", -8))


class TestAssumeAndReduction(unittest.TestCase):
    def test_assume_adds_bound_and_projects(self) -> None:
        s = _top(("x", "y")).assume_diff("x", "y", 1)
        self.assertEqual(s.as_diff_state().bound("x", "y"), 1)

    def test_contradictory_assume_goes_bottom(self) -> None:
        s = _top(("x", "y")).assume_diff("x", "y", 0)
        s = s.assume_diff("y", "x", -1)
        self.assertTrue(s.bottom)

    def test_interval_flows_into_relation(self) -> None:
        # assume y - x <= 0; 守卫 x <= 5 的真支 => y <= 5（区间单独得不到）
        s = _top(("x", "y")).assume_diff("y", "x", 0)
        t = s.restrict_interval("x", Interval(None, 5))
        self.assertEqual(t.get("y"), Interval(None, 5))
        self.assertEqual(t.as_diff_state().bound("y", "x"), 0)

    def test_interval_flows_back_both_directions(self) -> None:
        # x - y <= 0 且 x >= 4 => y >= 4
        s = _top(("x", "y")).assume_diff("x", "y", 0)
        t = s.restrict_interval("x", Interval(4, None))
        self.assertEqual(t.get("y"), Interval(4, None))

    def test_guard_complement_branches(self) -> None:
        s = _top(("x",))
        g = Guard("x", "<=", 5)
        self.assertEqual(s.apply_guard(g, True).get("x"), Interval(None, 5))
        self.assertEqual(s.apply_guard(g, False).get("x"), Interval(6, None))

    def test_infeasible_guard_restrict_is_bottom(self) -> None:
        s = _top(("x",)).restrict_interval("x", Interval(0, 0))
        self.assertTrue(s.apply_guard(Guard("x", ">=", 1), True).bottom)


class TestJoinWidenNarrow(unittest.TestCase):
    def _states(self):
        a = _top(("x", "y")).assume_diff("x", "y", 0)
        b = _top(("x", "y")).assume_diff("x", "y", 2)
        return a, b

    def test_join_takes_weaker_edge(self) -> None:
        a, b = self._states()
        self.assertEqual(a.join(b).as_diff_state().bound("x", "y"), 2)

    def test_join_with_top_drops_edge(self) -> None:
        a, _ = self._states()
        self.assertIsNone(a.join(_top(("x", "y"))).as_diff_state().bound("x", "y"))

    def test_bottom_identity(self) -> None:
        a, _ = self._states()
        bot = ProductState.bottom_of(("x", "y"))
        self.assertEqual(a.join(bot), a)
        self.assertTrue(bot.join(a).bottom is False)

    def test_subseteq_on_diff_bounds(self) -> None:
        a, b = self._states()
        # x-y<=0 蕴含 x-y<=2，反之不然
        self.assertTrue(a.subseteq(b))
        self.assertFalse(b.subseteq(a))

    def test_widen_pushes_weakened_edge_to_infinity(self) -> None:
        # 旧值边 0，凸包后变 1，且 x 是被加宽变量 => 边推到 +∞
        old = _top(("x", "y")).assume_diff("x", "y", 0)
        new = _top(("x", "y")).assume_diff("x", "y", 1)
        wide = old.widen_selective(old.join(new), frozenset({"x"}))
        self.assertIsNone(wide.as_diff_state().bound("x", "y"))

    def test_widen_selective_keeps_unmodified_var_edge(self) -> None:
        # 该循环不修改变量：边取精确凸包值 1，不推无穷
        old = _top(("x", "y")).assume_diff("x", "y", 0)
        new = _top(("x", "y")).assume_diff("x", "y", 1)
        kept = old.widen_selective(old.join(new), frozenset())
        self.assertEqual(kept.as_diff_state().bound("x", "y"), 1)

    def test_narrow_replaces_infinite_edge(self) -> None:
        # top 自身加宽后仍是 top（所有边 +∞）；收窄用新方程的有限界替换
        wide = _top(("x", "y"))
        refined = _top(("x", "y")).assume_diff("x", "y", 3)
        nar = wide.narrow_selective(refined, frozenset({"x"}))
        self.assertEqual(nar.as_diff_state().bound("x", "y"), 3)


class TestFromIntervals(unittest.TestCase):
    def test_entry_bounds_become_zero_edges(self) -> None:
        s = ProductState.from_intervals(
            ("x",), {"x": Interval(2, 5)}
        )
        self.assertEqual(s.get("x"), Interval(2, 5))
        # 对角线（x - x <= 0）恒为 0
        self.assertEqual(s.as_diff_state().bound("x", "x"), 0)

    def test_diff_state_text_and_view(self) -> None:
        s = _top(("x", "y")).assume_diff("x", "y", 4)
        txt = s.as_diff_state().text
        self.assertIn("x-y<=4", txt)
        d = s.as_diff_state().to_dict()
        self.assertFalse(d["bottom"])
        self.assertEqual(d["bounds"]["x-y"], 4)

    def test_bottom_view(self) -> None:
        b = ProductState.bottom_of(("x",))
        self.assertTrue(b.as_diff_state().bottom)
        self.assertTrue(b.as_abstract_state().bottom)


if __name__ == "__main__":
    unittest.main()
