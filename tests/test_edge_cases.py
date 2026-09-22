"""补充边界场景：入口即循环头、嵌套循环、确定性、>= 假支与多变量独立性。"""

import unittest

from interval_ai import (
    AssertRange,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    Interval,
    analyze,
    check_local_soundness,
)


class TestEntryIsLoopHead(unittest.TestCase):
    """入口块自身被回边指向（entry_bounds 限定入口区间）。"""

    def test_entry_head_with_initial_bounds(self) -> None:
        cfg = CFG(
            variables=("i",),
            blocks={
                "head": Block("head", (), ("body", "done"), Guard("i", "<=", 9)),
                "body": Block(
                    "body",
                    (AssignAdd("i", "i", 1), AssertRange("i", 1, 10)),
                    ("head",),
                ),
                "done": Block("done", (AssertRange("i", 10, 10),), ()),
            },
            entry="head",
            entry_bounds={"i": Interval(0, 0)},
        )
        res = analyze(cfg)
        self.assertEqual(res.block_in["head"].get("i"), Interval(0, 10))
        self.assertEqual(res.block_in["done"].get("i"), Interval(10, 10))
        self.assertTrue(all(a.verdict == "proved" for a in res.asserts))
        self.assertTrue(check_local_soundness(res).ok)


class TestNestedLoops(unittest.TestCase):
    """嵌套循环：外层 i in 0..2，内层每次把 j 从 0 加到 3。"""

    def test_nested_loop_invariants(self) -> None:
        cfg = CFG(
            variables=("i", "j"),
            blocks={
                "init": Block(
                    "init",
                    (AssignConst("i", 0), AssignConst("j", 0)),
                    ("oh",),
                ),
                "oh": Block("oh", (), ("setj", "end"), Guard("i", "<=", 2)),
                "setj": Block("setj", (AssignConst("j", 0),), ("ih",)),
                "ih": Block("ih", (), ("ibody", "obody"), Guard("j", "<=", 2)),
                "ibody": Block(
                    "ibody", (AssignAdd("j", "j", 1),), ("ih",)
                ),
                "obody": Block(
                    "obody",
                    (
                        AssertRange("j", 3, 3),
                        AssignAdd("i", "i", 1),
                        AssignConst("j", 0),
                    ),
                    ("oh",),
                ),
                "end": Block("end", (AssertRange("i", 3, 3),), ()),
            },
            entry="init",
        )
        res = analyze(cfg)
        self.assertEqual(tuple(res.widen_points), ("oh", "ih"))
        self.assertEqual(res.block_in["end"].get("i"), Interval(3, 3))
        # 外层出口处内层循环已把 j 收到 3
        self.assertEqual(res.block_in["end"].get("j"), Interval(0, 0))
        self.assertTrue(all(a.verdict == "proved" for a in res.asserts))
        self.assertTrue(check_local_soundness(res).ok)


class TestGeFalseBranch(unittest.TestCase):
    def test_ge_complement_is_minus_one(self) -> None:
        # x = c; if (x >= c+1) 不可达
        cfg = CFG(
            variables=("x",),
            blocks={
                "s": Block("s", (AssignConst("x", 5),), ("g",)),
                "g": Block("g", (), ("t", "f"), Guard("x", ">=", 6)),
                "t": Block("t", (), ()),
                "f": Block("f", (AssertRange("x", 5, 5),), ()),
            },
            entry="s",
        )
        res = analyze(cfg)
        self.assertTrue(res.block_in["t"].bottom)
        self.assertEqual(res.block_in["f"].get("x"), Interval(5, 5))
        self.assertTrue(check_local_soundness(res).ok)


class TestDeterminism(unittest.TestCase):
    def test_repeated_runs_identical(self) -> None:
        from tests._programs import two_backedges_program

        cfg = two_backedges_program()
        r1 = analyze(cfg)
        r2 = analyze(cfg)
        self.assertEqual(r1.block_in, r2.block_in)
        self.assertEqual(r1.block_out, r2.block_out)
        self.assertEqual(
            (r1.ascending_rounds, r1.narrowing_rounds),
            (r2.ascending_rounds, r2.narrowing_rounds),
        )
        self.assertEqual([a.to_dict() for a in r1.asserts],
                         [a.to_dict() for a in r2.asserts])


class TestUnrelatedVariableUnchanged(unittest.TestCase):
    def test_assignment_does_not_widen_others(self) -> None:
        cfg = CFG(
            variables=("a", "b"),
            blocks={
                "s": Block(
                    "s",
                    (
                        AssignConst("a", 1),
                        AssertRange("a", 1, 1),
                        AssertRange("b", 0, 0),
                    ),
                    (),
                ),
            },
            entry="s",
            entry_bounds={"a": Interval.top(), "b": Interval(0, 0)},
        )
        res = analyze(cfg)
        # b 保持入口区间不被 a 的赋值影响
        self.assertEqual(res.block_in["s"].get("b"), Interval(0, 0))
        self.assertEqual(res.block_in["s"].get("a"), Interval.top())
        verdicts = {a.statement.target: a.verdict for a in res.asserts}
        self.assertEqual(verdicts["a"], "proved")
        self.assertEqual(verdicts["b"], "proved")


if __name__ == "__main__":
    unittest.main()
