"""区间 + 同余联合域的增量测试。"""

import unittest

from interval_ai import (
    AbstractState,
    AssignAdd,
    AssignConst,
    AssignMul,
    Block,
    CFG,
    Congruence,
    Guard,
    Interval,
    analyze,
    check_edge_guard,
    check_local_soundness,
    run_bounded,
)
from interval_ai.errors import ValidationError


def step_two_program() -> CFG:
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 4)),
            "body": Block("body", (AssignAdd("i", "i", 2),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def different_steps_program() -> CFG:
    return CFG(
        variables=("i", "j"),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 9)),
            "fork": Block("fork", (), ("step2", "step3"), Guard("j", ">=", 0)),
            "body": Block("body", (), ("fork",)),
            "step2": Block("step2", (AssignAdd("i", "i", 2),), ("head",)),
            "step3": Block("step3", (AssignAdd("i", "i", 3),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def negative_start_program() -> CFG:
    return CFG(
        variables=("x", "y"),
        blocks={
            "init": Block(
                "init",
                (AssignConst("y", 0), AssignConst("x", -3), AssignMul("y", "x", -2)),
                ("head",),
            ),
            "head": Block("head", (), ("body", "dead"), Guard("x", ">=", -4)),
            "body": Block("body", (AssignAdd("x", "x", 2),), ("head",)),
            "dead": Block("dead", (), ()),
        },
        entry="init",
    )


class TestCongruenceDomain(unittest.TestCase):
    def test_normalization_and_negative_affine(self) -> None:
        self.assertEqual(Congruence(2, -1), Congruence(2, 1))
        self.assertEqual(Congruence.exact(-3).affine(1, 2), Congruence.exact(-1))
        self.assertEqual(Congruence(4, 3).affine(-2, 1), Congruence(8, 3))
        self.assertEqual(Congruence(4, 3).affine(0, -7), Congruence.exact(-7))

    def test_join_uses_gcd_of_steps_and_offsets(self) -> None:
        self.assertEqual(Congruence(4, 1).join(Congruence(4, 3)), Congruence(2, 1))
        self.assertEqual(Congruence(2, 0).join(Congruence(3, 0)), Congruence.top())
        self.assertEqual(Congruence.exact(2).join(Congruence.exact(2)), Congruence.exact(2))

    def test_intersection_and_emptiness(self) -> None:
        self.assertEqual(Congruence(4, 1).intersect(Congruence(6, 3)), Congruence(12, 9))
        self.assertIsNone(Congruence(2, 0).intersect(Congruence(2, 1)))
        self.assertTrue(Interval(0, 4).contains_int(3))
        state = AbstractState(
            ("i",),
            {"i": Interval.top()},
            residues={"i": Congruence.top()},
        ).restrict("i", Interval(0, 0), Congruence(2, 1))
        self.assertTrue(state.bottom)

    def test_invalid_congruence(self) -> None:
        with self.assertRaises(ValidationError):
            Congruence(-2, 0)
        with self.assertRaises(ValidationError):
            Congruence(True, 0)
        with self.assertRaises(ValidationError):
            AssignMul("i", "i", True)


class TestAnalysisWithCongruences(unittest.TestCase):
    def test_step_two_loop_keeps_even_counter(self) -> None:
        res = analyze(step_two_program())
        self.assertEqual(res.block_in["head"].get("i"), Interval(0, 6))
        self.assertEqual(res.block_in["head"].get_congruence("i"), Congruence(2, 0))
        self.assertEqual(res.block_in["body"].get("i"), Interval(0, 4))
        self.assertEqual(res.block_in["body"].get_congruence("i"), Congruence(2, 0))
        self.assertEqual(res.block_in["exit"].get("i"), Interval(5, 6))
        self.assertEqual(res.block_in["exit"].get_congruence("i"), Congruence(2, 0))
        self.assertTrue(check_local_soundness(res).ok)

    def test_different_path_steps_join_to_top_congruence(self) -> None:
        res = analyze(different_steps_program())
        self.assertEqual(res.block_in["head"].get_congruence("i"), Congruence.top())
        self.assertEqual(res.block_in["exit"].get("i"), Interval(10, 12))
        self.assertEqual(res.block_in["exit"].get_congruence("i"), Congruence.top())
        self.assertTrue(check_local_soundness(res).ok)

    def test_negative_start_negative_multiplier_and_dead_edge(self) -> None:
        res = analyze(negative_start_program())
        self.assertEqual(res.block_in["head"].get("x"), Interval(-3, None))
        self.assertEqual(res.block_in["head"].get_congruence("x"), Congruence(2, 1))
        self.assertEqual(res.block_in["body"].get("x"), Interval(-3, None))
        self.assertTrue(res.block_in["dead"].bottom)
        self.assertEqual(res.block_out["init"].get_congruence("y"), Congruence.exact(6))
        self.assertTrue(check_local_soundness(res).ok)

    def test_entry_precondition_without_congruence_point_is_bottom(self) -> None:
        cfg = CFG(
            variables=("i",),
            blocks={"b": Block("b", (), ())},
            entry="b",
            entry_bounds={"i": Interval(0, 0)},
            entry_congruences={"i": Congruence(2, 1)},
        )
        res = analyze(cfg)
        self.assertTrue(res.block_in["b"].bottom)
        self.assertTrue(check_local_soundness(res).ok)

    def test_independent_edge_check_catches_missing_odd_points(self) -> None:
        res = analyze(step_two_program())
        body_out = res.block_out["body"]
        target_in = res.block_in["head"]
        self.assertTrue(
            check_edge_guard(Guard("i", "<=", 100), True, body_out, target_in).ok
        )
        bad = target_in.assign("i", Interval(4, 6), Congruence(2, 0))
        report = check_edge_guard(Guard("i", "<=", 100), True, body_out, bad)
        self.assertFalse(report.ok)

    def test_concrete_execution_supplements_invariant(self) -> None:
        cfg = step_two_program()
        concrete = run_bounded(cfg, [{"i": 0}])
        self.assertFalse(concrete.truncated)
        res = analyze(cfg)
        for name in concrete.reachable:
            for store in concrete.in_stores[name]:
                value = store["i"]
                self.assertTrue(res.block_in[name].get("i").contains_int(value))
                self.assertTrue(res.block_in[name].get_congruence("i").contains_int(value))


if __name__ == "__main__":
    unittest.main()
