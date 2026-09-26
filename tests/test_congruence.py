"""同余分量、独立转移包含与关键控制流场景测试。"""

import unittest
from dataclasses import replace

from interval_ai import (
    AbstractState,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssignMul,
    Block,
    CFG,
    Congruence,
    Guard,
    Interval,
    analyze,
    check_edge_guard,
    check_local_soundness,
    check_transfer_step,
    run_bounded,
    ValidationError,
    transfer_statement,
)


class TestCongruenceDomain(unittest.TestCase):
    def test_invalid_congruence_is_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            Congruence(-2, 0)
        with self.assertRaises(ValidationError):
            Congruence(2, True)
        with self.assertRaises(ValidationError):
            AssignMul("x", "x", False)

    def test_incompatible_entry_congruence_is_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(
                variables=("x",),
                blocks={"b": Block("b", (), ())},
                entry="b",
                entry_bounds={"x": Interval(1, 1)},
                entry_congruences={"x": Congruence(2, 0)},
            )

    def test_normalization_negative_arithmetic_and_exact(self) -> None:
        self.assertEqual(Congruence(0, -9), Congruence.exact(-9))
        self.assertEqual(Congruence(4, -1), Congruence(4, 3))
        self.assertEqual(Congruence(2, 1).shift(-4), Congruence(2, 1))
        self.assertEqual(Congruence.exact(-3).scale(-2), Congruence.exact(6))
        self.assertEqual(Congruence(4, 3).scale(-2), Congruence(2, 2))

    def test_join_is_gcd_not_one_sided(self) -> None:
        self.assertEqual(Congruence(6, 3).join(Congruence(10, 1)), Congruence(2, 1))
        self.assertEqual(Congruence(2, 0).join(Congruence(3, 1)), Congruence.arbitrary())
        self.assertEqual(Congruence.exact(2).join(Congruence.exact(8)), Congruence(6, 2))

    def test_interval_legal_point_and_emptiness(self) -> None:
        self.assertTrue(Congruence(2, 0).has_point_within(1, 3))
        self.assertFalse(Congruence(2, 0).has_point_within(1, 1))
        state = AbstractState(
            ("x",),
            {"x": Interval(1, 1)},
            residues={"x": Congruence(2, 0)},
        )
        self.assertTrue(state.bottom)

    def test_constant_multiplication_transfer(self) -> None:
        before = AbstractState(
            ("x",),
            {"x": Interval(-5, 5)},
            residues={"x": Congruence(4, 3)},
        )
        stmt = AssignMul("x", "x", -2)
        after = transfer_statement(before, stmt)
        self.assertEqual(after.get("x"), Interval(-10, 10))
        self.assertEqual(after.get_congruence("x"), Congruence(2, 0))
        self.assertTrue(check_transfer_step(stmt, before, after).ok)


def _even_counter_cfg(start: int = 0) -> CFG:
    body_lower = start if start <= 9 else None
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", start),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", None, None, Congruence(2, start & 1)),),
                ("body", "exit"),
                Guard("i", "<=", 9),
            ),
            "body": Block(
                "body",
                (
                    AssertRange("i", body_lower, 9, Congruence(2, start & 1)),
                    AssignAdd("i", "i", 2),
                ),
                ("head",),
            ),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def _different_step_paths_cfg(steps: tuple[int, int] = (2, 4)) -> CFG:
    return CFG(
        variables=("i", "p"),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", None, None, Congruence.even()),),
                ("fork", "exit"),
                Guard("i", "<=", 9),
            ),
            "fork": Block("fork", (), ("s2", "s4"), Guard("p", ">=", 0)),
            "s2": Block("s2", (AssignAdd("i", "i", steps[0]),), ("head",)),
            "s4": Block("s4", (AssignAdd("i", "i", steps[1]),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


class TestCongruencePropagation(unittest.TestCase):
    def test_step_two_excludes_odd_points(self) -> None:
        result = analyze(_even_counter_cfg(0))
        self.assertEqual(result.block_in["head"].get_congruence("i"), Congruence.even())
        self.assertEqual(result.block_in["body"].get("i"), Interval(0, 9))
        self.assertTrue(result.block_in["exit"].get_congruence("i").subseteq(Congruence.even()))
        self.assertTrue(all(a.verdict == "proved" for a in result.asserts))
        self.assertTrue(check_local_soundness(result).ok)

    def test_negative_start_keeps_canonical_odd_residue(self) -> None:
        result = analyze(_even_counter_cfg(-3))
        self.assertEqual(result.block_in["head"].get_congruence("i"), Congruence(2, 1))
        self.assertEqual(result.block_in["body"].get("i"), Interval(-3, 9))
        self.assertTrue(check_local_soundness(result).ok)

    def test_two_paths_with_different_steps_join_to_common_restriction(self) -> None:
        result = analyze(_different_step_paths_cfg())
        self.assertEqual(result.block_in["head"].get_congruence("i"), Congruence.even())
        self.assertTrue(result.block_in["exit"].get_congruence("i").subseteq(Congruence.even()))
        self.assertTrue(check_local_soundness(result).ok)

    def test_coprime_steps_have_no_shared_period(self) -> None:
        result = analyze(_different_step_paths_cfg((2, 3)))
        self.assertEqual(result.block_in["head"].get_congruence("i"), Congruence.arbitrary())
        self.assertTrue(check_local_soundness(result).ok)

    def test_branch_with_no_legal_congruence_point_is_bottom(self) -> None:
        cfg = CFG(
            variables=("i",),
            blocks={
                "init": Block("init", (AssignConst("i", 0),), ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 9)),
                "body": Block("body", (AssignAdd("i", "i", 2),), ("head",)),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        result = analyze(cfg)
        # exit 的区间外壳为 [10,11]，但只有偶数点可达；伪造奇数边状态必须失败。
        even_out = result.block_out["head"]
        odd_state = even_out.assign("i", Interval(11, 11))
        report = check_edge_guard(Guard("i", "<=", 9), False, even_out, odd_state)
        self.assertFalse(report.ok)

    def test_loop_body_that_is_never_entered_is_bottom(self) -> None:
        cfg = _even_counter_cfg(10)
        result = analyze(cfg)
        self.assertTrue(result.block_in["body"].bottom)
        self.assertTrue(result.block_out["body"].bottom)
        self.assertEqual(result.block_in["exit"].get("i"), Interval(10, 10))
        self.assertEqual(result.block_in["exit"].get_congruence("i"), Congruence.exact(10))
        self.assertTrue(check_local_soundness(result).ok)

    def test_tampered_congruence_is_caught_independently(self) -> None:
        result = analyze(_even_counter_cfg(0))
        bad_ins = dict(result.block_in)
        bad_ins["exit"] = bad_ins["exit"].assign_value(
            "i",
            result.block_in["exit"].get("i"),
            Congruence.arbitrary(),
        )
        report = check_local_soundness(replace(result, block_in=bad_ins))
        self.assertFalse(report.ok)

    def test_bounded_concrete_execution_is_supplement(self) -> None:
        cfg = _even_counter_cfg(0)
        concrete = run_bounded(cfg, [{"i": 0}], max_visited_states=100)
        self.assertFalse(concrete.truncated)
        result = analyze(cfg)
        for name in concrete.reachable:
            for value in [store["i"] for store in concrete.in_stores[name]]:
                self.assertTrue(result.block_in[name].get_congruence("i").contains_int(value))


if __name__ == "__main__":
    unittest.main()
