"""区间域单元测试（端点为手算期望值，不经过引擎）。"""

import unittest

from interval_ai import Interval
from interval_ai.errors import ValidationError


class TestIntervalDomain(unittest.TestCase):
    def test_text_and_factories(self) -> None:
        self.assertEqual(Interval.top().text, "[-inf, +inf]")
        self.assertEqual(Interval.singleton(3).text, "[3, 3]")
        self.assertEqual(Interval.at_most(5).text, "[-inf, 5]")
        self.assertEqual(Interval.at_least(-2).text, "[-2, +inf]")

    def test_subseteq_symbolic(self) -> None:
        cases = [
            (Interval(1, 2), Interval(0, 3), True),
            (Interval(0, 3), Interval(1, 2), False),
            (Interval(1, None), Interval(0, None), True),
            (Interval(0, None), Interval(1, None), False),
            (Interval(None, 2), Interval(None, 3), True),
            (Interval.top(), Interval(0, 1), False),
            (Interval(0, 1), Interval.top(), True),
        ]
        for a, b, expected in cases:
            with self.subTest(a=a.text, b=b.text):
                self.assertIs(a.subseteq(b), expected)

    def test_join_is_hull(self) -> None:
        self.assertEqual(Interval(1, 2).join(Interval(5, 9)), Interval(1, 9))
        self.assertEqual(Interval(1, None).join(Interval(-3, 2)), Interval(-3, None))
        self.assertEqual(Interval(None, 0).join(Interval(1, None)), Interval.top())

    def test_intersect(self) -> None:
        self.assertEqual(Interval(1, 5).intersect(Interval(3, 9)), Interval(3, 5))
        self.assertEqual(Interval(1, 5).intersect(Interval(6, 9)), None)
        self.assertEqual(
            Interval(None, 5).intersect(Interval(2, None)), Interval(2, 5)
        )

    def test_add_shifts_with_infinity(self) -> None:
        self.assertEqual(Interval(1, 2).add(-4), Interval(-3, -2))
        self.assertEqual(Interval.at_least(3).add(7), Interval.at_least(10))
        self.assertEqual(Interval.top().add(-10**100), Interval.top())

    def test_widen_standard(self) -> None:
        # 凸包序列 [0,0] ⊆ [0,1] ⊆ [0,2]：上端被突破 -> +inf
        self.assertEqual(
            Interval(0, 1).widen(Interval(0, 1).join(Interval(0, 2))),
            Interval(0, None),
        )
        # 下端被突破 -> -inf
        self.assertEqual(
            Interval(8, 10).widen(Interval(8, 10).join(Interval(7, 10))),
            Interval(None, 10),
        )
        # 已是无穷的端点保持无穷
        self.assertEqual(Interval(0, None).widen(Interval(0, None)), Interval(0, None))

    def test_narrow_replaces_only_infinite_bounds(self) -> None:
        self.assertEqual(
            Interval(0, None).narrow(Interval(0, 10)), Interval(0, 10)
        )
        self.assertEqual(
            Interval(None, 10).narrow(Interval(0, 10)), Interval(0, 10)
        )
        # 有限端点不被收窄改动
        self.assertEqual(
            Interval(0, 10).narrow(Interval(-5, 20)), Interval(0, 10)
        )

    def test_rejects_bad_endpoints(self) -> None:
        with self.assertRaises(ValidationError):
            Interval(True, 3)
        with self.assertRaises(ValidationError):
            Interval(float("nan"), 3)
        with self.assertRaises(ValidationError):
            Interval(0, float("inf"))
        with self.assertRaises(ValidationError):
            Interval(5, 4)
        with self.assertRaises(ValidationError):
            Interval.singleton(1.0)  # 非整数浮点也拒绝


if __name__ == "__main__":
    unittest.main()
