"""差分约束域（DBM）单元测试。

所有期望矩阵/界均为手算硬编码，不调用引擎、不调用关系转移生成期望值；
判定一律是符号界比较，不枚举整数值。
"""

import unittest

from interval_ai import DiffState, Interval
from interval_ai.diffs import _close, _top_matrix  # type: ignore


def M(state: DiffState) -> tuple[tuple[int | None, ...], ...]:
    return state.matrix


class TestDBMConstruction(unittest.TestCase):
    def test_top_is_zero_diagonal(self) -> None:
        d = DiffState.top_of(("x", "y"))
        self.assertEqual(d.zero, 2)
        for i in range(3):
            for j in range(3):
                self.assertEqual(M(d)[i][j], 0 if i == j else None)

    def test_bottom(self) -> None:
        d = DiffState.bottom_of(("x",))
        self.assertTrue(d.bottom)
        with self.assertRaises(ValueError):
            d.bound_of("x", None)
        self.assertTrue(d.implies("x", None, -10**6))  # 底空真

    def test_from_intervals_indices_and_projection(self) -> None:
        # x in [0,4], y == 1（变量顺序 x,y，零节点下标 2）
        d = DiffState.from_intervals(
            ("x", "y"), {"x": Interval(0, 4), "y": Interval(1, 1)}
        )
        # x - 0 <= 4, 0 - x <= 0, y - 0 <= 1, 0 - y <= -1
        self.assertEqual(M(d)[0][2], 4)
        self.assertEqual(M(d)[2][0], 0)
        self.assertEqual(M(d)[1][2], 1)
        self.assertEqual(M(d)[2][1], -1)
        self.assertEqual(d.interval_of("x"), Interval(0, 4))
        self.assertEqual(d.interval_of("y"), Interval(1, 1))

    def test_closure_deduces_difference_bounds(self) -> None:
        # x <= 4, y >= 1（0-y <= -1）⇒ 路 x->0->y 给出 x-y <= 3；
        # y <= 1, x >= 0 ⇒ y-x <= 1
        d = DiffState.from_intervals(
            ("x", "y"), {"x": Interval(0, 4), "y": Interval(1, 1)}
        )
        self.assertEqual(d.bound_of("x", "y"), 3)
        self.assertEqual(d.bound_of("y", "x"), 1)


class TestDBMAssume(unittest.TestCase):
    def test_assume_strengthens_and_closes(self) -> None:
        # x,y 无约束；加入 x-y<=2 与 y<=5：闭包应推出 x<=7
        d = DiffState.top_of(("x", "y"))
        d = d.assume("x", "y", 2)
        d = d.assume("y", None, 5)
        self.assertEqual(d.bound_of("x", None), 7)
        self.assertTrue(d.implies("x", None, 7))
        self.assertFalse(d.implies("x", None, 6))

    def test_assume_lower_via_zero_node(self) -> None:
        d = DiffState.top_of(("x",)).assume_lower("x", 3)  # x >= 3
        self.assertEqual(d.interval_of("x"), Interval(3, None))
        d2 = d.assume("x", None, 3)  # 再夹 x <= 3 ⇒ x == 3
        self.assertEqual(d2.interval_of("x"), Interval(3, 3))

    def test_contradiction_becomes_bottom(self) -> None:
        # x - y <= 1 且 y - x <= -2（即 x - y >= 2）矛盾
        d = DiffState.top_of(("x", "y"))
        d = d.assume("x", "y", 1)
        d = d.assume("y", "x", -2)
        self.assertTrue(d.bottom)

    def test_redundant_assume_is_noop(self) -> None:
        d = DiffState.top_of(("x",)).assume("x", None, 5)
        same = d.assume("x", None, 9)
        self.assertIs(same, d)


class TestDBMAssignments(unittest.TestCase):
    def setUp(self) -> None:
        # x in [0,4], y == 1
        self.d = DiffState.from_intervals(
            ("x", "y"), {"x": Interval(0, 4), "y": Interval(1, 1)}
        )

    def test_assign_const_forgets_old_relations(self) -> None:
        # y := 10：旧的 y==1（x-y<=3）必须失效；闭包通过零节点重新推出
        # 新 y 与 x 的关系：x<=4 且 y==10 ⇒ x-y<=-6，y-x<=10。
        d = self.d.assign_const("y", 10)
        self.assertEqual(d.interval_of("y"), Interval(10, 10))
        self.assertEqual(d.bound_of("x", "y"), -6)
        self.assertEqual(d.bound_of("y", "x"), 10)
        # x 的单变量界保留
        self.assertEqual(d.interval_of("x"), Interval(0, 4))

    def test_assign_const_unconstrained_var_drops_old_relation(self) -> None:
        # 旧关系只在"旧 y"与 x 之间成立、无法经零节点重建时必须消失：
        # 仅有 x-y<=1（x,y 均无单边界），y := 10 后 x 重新无界，x-y 无约束。
        d = DiffState.top_of(("x", "y")).assume("x", "y", 1)
        d = d.assign_const("y", 10)
        self.assertEqual(d.interval_of("y"), Interval(10, 10))
        self.assertIsNone(d.bound_of("x", "y"))
        self.assertTrue(d.interval_of("x").is_top)

    def test_assign_copy_creates_equality(self) -> None:
        d = self.d.assign_copy("y", "x")  # y = x
        self.assertEqual(d.bound_of("x", "y"), 0)
        self.assertEqual(d.bound_of("y", "x"), 0)
        self.assertEqual(d.interval_of("y"), Interval(0, 4))

    def test_assign_add_creates_offset_equality(self) -> None:
        d = self.d.assign_add("y", "x", 1)  # y = x + 1
        self.assertEqual(d.bound_of("y", "x"), 1)
        self.assertEqual(d.bound_of("x", "y"), -1)
        self.assertEqual(d.interval_of("y"), Interval(1, 5))

    def test_self_increment_keeps_offset_with_third_var(self) -> None:
        # x in [0,4], y == 1；x := x + 1 后：x in [1,5]，且 y - x <= 0、
        # x - y <= 4（新 x 与未改动的 y 之间的旧关系经保存行列正确传播）
        d = self.d.assign_add("x", "x", 1)
        self.assertEqual(d.interval_of("x"), Interval(1, 5))
        self.assertEqual(d.interval_of("y"), Interval(1, 1))
        self.assertEqual(d.bound_of("y", "x"), 0)
        self.assertEqual(d.bound_of("x", "y"), 4)

    def test_self_increment_exact_relation_preserved(self) -> None:
        # y == x 精确相等，各自 +1 后仍精确相等（循环不变量核心场景）
        d = DiffState.top_of(("x", "y"))
        d = d.assign_const("x", 0).assign_copy("y", "x")
        d = d.assign_add("x", "x", 1).assign_add("y", "y", 1)
        self.assertEqual(d.bound_of("x", "y"), 0)
        self.assertEqual(d.bound_of("y", "x"), 0)
        self.assertEqual(d.interval_of("x"), Interval(1, 1))


class TestDBMJoinOrderWiden(unittest.TestCase):
    def test_join_is_pointwise_max(self) -> None:
        # A: y = x（双向界 0）；B: y = x + 1（y-x<=1, x-y<=-1）
        a = DiffState.top_of(("x", "y")).assign_const("x", 7).assign_copy("y", "x")
        b = (
            DiffState.top_of(("x", "y"))
            .assign_const("x", 7)
            .assign_add("y", "x", 1)
        )
        j = a.join(b)
        self.assertEqual(j.bound_of("y", "x"), 1)   # max(0, 1)
        self.assertEqual(j.bound_of("x", "y"), 0)   # max(0, -1)
        self.assertTrue(j.implies("x", "y", 0))
        self.assertFalse(j.implies("x", "y", -1))

    def test_join_with_bottom(self) -> None:
        d = DiffState.top_of(("x",))
        bot = DiffState.bottom_of(("x",))
        self.assertEqual(d.join(bot), d)
        self.assertEqual(bot.join(d), d)

    def test_subseteq_order(self) -> None:
        tight = DiffState.top_of(("x", "y")).assume("x", "y", 1)
        loose = DiffState.top_of(("x", "y")).assume("x", "y", 3)
        self.assertTrue(tight.subseteq(loose))
        self.assertFalse(loose.subseteq(tight))
        self.assertTrue(DiffState.bottom_of(("x", "y")).subseteq(tight))

    def test_widen_drops_broken_bounds_to_infinity(self) -> None:
        # a: x-y<=0, y<=0；b: x-y<=1, y<=0。
        # 只加宽被修改量 x：x-y、x-0 都被放松 -> +∞；y-0 与 x 无关，精确保留 0。
        a = DiffState.top_of(("x", "y")).assume("x", "y", 0).assume("y", None, 0)
        b = DiffState.top_of(("x", "y")).assume("x", "y", 1).assume("y", None, 0)
        w = a.widen_selective(b, {"x"})
        self.assertIsNone(w.bound_of("x", "y"))
        self.assertIsNone(w.bound_of("x", None))
        self.assertEqual(w.bound_of("y", None), 0)

    def test_narrow_recovers_finite_bound(self) -> None:
        top = DiffState.top_of(("x", "y")).assume("x", "y", 0)
        # 手工构造一个 x-y 已被加宽为 +∞ 的状态
        rows = [list(r) for r in M(top)]
        rows[0][1] = None
        wide = DiffState(("x", "y"), tuple(tuple(r) for r in rows))
        cand = DiffState.top_of(("x", "y")).assume("x", "y", 2)
        n = wide.narrow_selective(cand, {"x", "y"})
        self.assertEqual(n.bound_of("x", "y"), 2)


class TestRawClosure(unittest.TestCase):
    def test_raw_close_detects_negative_cycle(self) -> None:
        # 2 节点（x, 零节点）：x-0<=1 且 0-x<=-2 ⇒ 负环（x<=1 且 x>=2）
        rows = [[0, 1], [-2, 0]]
        self.assertIsNone(_close(rows))

    def test_raw_top_matrix_shape(self) -> None:
        t = _top_matrix(3)
        self.assertEqual(len(t), 3)
        self.assertEqual([r[0] for r in t], [0, None, None])


if __name__ == "__main__":
    unittest.main()
