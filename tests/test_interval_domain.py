"""区间域单元测试：端点、格运算、widening/narrowing 性质。"""

import unittest

from interval_ai.interval import Interval
from interval_ai.errors import InvalidOperandError


class TestIntervalBasics(unittest.TestCase):
    def test_repr_and_eq(self):
        self.assertEqual(Interval(0, 1), Interval(0, 1))
        self.assertNotEqual(Interval(0, 1), Interval(0, 2))
        self.assertEqual(Interval.top(), Interval(None, None))
        self.assertEqual(repr(Interval(None, 3)), "[-inf, 3]")
        self.assertEqual(Interval.of(5), Interval(5, 5))

    def test_invalid_construction(self):
        with self.assertRaises(InvalidOperandError):
            Interval(3, 2)
        with self.assertRaises(InvalidOperandError):
            Interval(1.0, 2)
        with self.assertRaises(InvalidOperandError):
            Interval(True, 2)
        with self.assertRaises(InvalidOperandError):
            Interval(1, float("nan"))
        with self.assertRaises(InvalidOperandError):
            Interval(1, float("inf"))

    def test_of_rejects_bad_numbers(self):
        for bad in (1.0, True, False, float("nan"), float("-inf"), "7", None):
            with self.assertRaises(InvalidOperandError):
                Interval.of(bad)

    def test_big_integers_exact(self):
        big = 10**100
        iv = Interval(0, big).add_const(-big)
        self.assertEqual(iv, Interval(-big, 0))  # 任意精度，无溢出/舍入


class TestLattice(unittest.TestCase):
    def test_subset(self):
        self.assertTrue(Interval(1, 2) <= Interval(0, 3))
        self.assertTrue(Interval(0, 3) <= Interval.top())
        self.assertTrue(Interval.top() <= Interval.top())
        self.assertFalse(Interval(0, 3) <= Interval(1, 3))
        self.assertFalse(Interval(0, 3) <= Interval(0, 2))
        self.assertFalse(Interval(1, 2) <= Interval(10, 20))

    def test_hull(self):
        self.assertEqual(Interval.hull(Interval(0, 1), Interval(5, 9)), Interval(0, 9))
        self.assertEqual(
            Interval.hull(Interval(0, 1), Interval(None, -3)), Interval(None, 1)
        )
        self.assertEqual(
            Interval.hull(Interval.top(), Interval(0, 0)), Interval.top()
        )

    def test_meet_and_restrict(self):
        self.assertEqual(Interval(0, 5).meet(Interval(3, 9)), Interval(3, 5))
        self.assertIsNone(Interval(0, 5).meet(Interval(6, 9)))
        self.assertEqual(Interval(0, 5).restrict_le(3), Interval(0, 3))
        self.assertIsNone(Interval(0, 5).restrict_le(-1))
        self.assertEqual(Interval(0, 5).restrict_ge(3), Interval(3, 5))
        self.assertIsNone(Interval(0, 5).restrict_ge(6))
        self.assertEqual(Interval.top().restrict_le(3), Interval(None, 3))
        self.assertEqual(Interval.top().restrict_ge(3), Interval(3, None))

    def test_add_const_infinite(self):
        self.assertEqual(Interval.top().add_const(-7), Interval.top())
        self.assertEqual(Interval(None, 3).add_const(10), Interval(None, 13))


class TestWidenNarrow(unittest.TestCase):
    def test_widen_pushes_moving_endpoint_to_infinity(self):
        # 上界在上升链中变大 -> 立即 +inf；下界不动
        self.assertEqual(
            Interval.widen(Interval(0, 2), Interval(0, 3)), Interval(0, None)
        )
        # 下界变小 -> -inf
        self.assertEqual(
            Interval.widen(Interval(0, 5), Interval(-1, 5)), Interval(None, 5)
        )
        # 未变大的有限端保持
        self.assertEqual(
            Interval.widen(Interval(0, 5), Interval(1, 5)), Interval(0, 5)
        )
        # 已经是无穷则保持
        self.assertEqual(
            Interval.widen(Interval(0, None), Interval(0, None)), Interval(0, None)
        )

    def test_widen_covers_both_operands(self):
        # 可靠性：prev ⊆ widen(prev,nxt) 且 nxt ⊆ widen(prev,nxt)（在 nxt⊇prev 链上）
        pairs = [
            (Interval(0, 2), Interval(0, 3)),
            (Interval(0, 5), Interval(-1, 5)),
            (Interval(-2, 2), Interval(-3, 9)),
        ]
        for prev, nxt in pairs:
            w = Interval.widen(prev, nxt)
            self.assertTrue(prev <= w, f"{prev} 不含于 {w}")
            self.assertTrue(nxt <= w, f"{nxt} 不含于 {w}")

    def test_widen_terminates_chain(self):
        # 任意长度上升链，widening 迭代必然到达不动点
        cur = Interval(0, 0)
        bound = 0
        for _ in range(10_000):
            bound += 1
            nxt = Interval.hull(cur, Interval(0, bound))
            w = Interval.widen(cur, nxt)
            if w == cur:
                break
            cur = w
        self.assertEqual(cur, Interval(0, None))

    def test_narrow_recovers_finite_bound(self):
        widened = Interval(0, None)
        tighter = Interval(0, 11)  # 下一轮 F 的像
        n = Interval.narrow(widened, tighter)
        self.assertEqual(n, Interval(0, 11))
        # 有限端点绝不被 narrowing 改动（下降链可靠性）
        n2 = Interval.narrow(Interval(0, 11), Interval(2, 11))
        self.assertEqual(n2, Interval(0, 11))

    def test_narrow_ordering(self):
        prev, nxt = Interval(0, None), Interval(0, 11)
        n = Interval.narrow(prev, nxt)
        self.assertTrue(nxt <= n <= prev)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
