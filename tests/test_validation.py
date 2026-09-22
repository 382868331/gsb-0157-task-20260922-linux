"""输入校验与错误语义测试。

覆盖：NaN/Infinity 拒绝、bool 拒绝、结构错误可定位、规模上限、
构造失败无半成品、预算耗尽与 unknown 分离。
"""

import math
import unittest

from interval_ai import (
    AddConst,
    AnalyzerBudgetExhausted,
    AssertRange,
    Assign,
    Block,
    Cond,
    ConcreteBudgetExhausted,
    DuplicateIdError,
    InconsistentGraphError,
    InvalidOperandError,
    Jump,
    LimitExceededError,
    MAX_BLOCKS,
    MAX_VARIABLES,
    Program,
    ProgramStructureError,
    analyze,
    execute_concrete,
)


class TestNumericRejection(unittest.TestCase):
    def test_float_nan_inf_rejected_everywhere(self):
        bad_floats = (
            float("nan"),
            float("inf"),
            float("-inf"),
            1.5,
            1.0,  # 即使数值等于整数也拒绝：本库只认真 int
            -0.0,
        )
        for bad in bad_floats:
            with self.subTest(bad=bad):
                with self.assertRaises(InvalidOperandError):
                    Assign("x", bad)
                with self.assertRaises(InvalidOperandError):
                    AddConst("x", bad)
                with self.assertRaises(InvalidOperandError):
                    AssertRange("x", 0, bad, "a")
                with self.assertRaises(InvalidOperandError):
                    Cond("x", "<=", bad, "b1", "b2")

    def test_bool_rejected_as_integer(self):
        for bad in (True, False):
            with self.subTest(bad=bad):
                with self.assertRaises(InvalidOperandError):
                    Assign("x", bad)
                with self.assertRaises(InvalidOperandError):
                    AddConst("x", bad)
                with self.assertRaises(InvalidOperandError):
                    AssertRange("x", bad, 1, "a")

    def test_error_is_localizable(self):
        try:
            AddConst("x", math.nan)
        except InvalidOperandError as e:
            self.assertIsNotNone(e.where)
            self.assertIn("AddConst", e.where)
        else:  # pragma: no cover
            self.fail("应当抛 InvalidOperandError")


class TestStructureValidation(unittest.TestCase):
    def _minimal_kwargs(self, **over):
        kw = dict(
            variables=("x",),
            blocks=(Block("b0", (Assign("x", 0),), None),),
            entry="b0",
        )
        kw.update(over)
        return kw

    def test_empty_variables_or_blocks(self):
        with self.assertRaises(ProgramStructureError):
            Program((), (Block("b0", (), None)), "b0")
        with self.assertRaises(ProgramStructureError):
            Program(("x",), (), "b0")

    def test_duplicate_variable_and_block(self):
        with self.assertRaises(DuplicateIdError):
            Program(("x", "x"), (Block("b0", (), None),), "b0")
        with self.assertRaises(DuplicateIdError):
            Program(
                ("x",),
                (Block("b0", (), None), Block("b0", (), None)),
                "b0",
            )

    def test_duplicate_assert_id(self):
        with self.assertRaises(DuplicateIdError):
            Program(
                ("x",),
                (
                    Block(
                        "b0",
                        (
                            AssertRange("x", 0, 1, "dup"),
                            AssertRange("x", 0, 1, "dup"),
                        ),
                        None,
                    ),
                ),
                "b0",
            )

    def test_missing_entry(self):
        with self.assertRaises(InconsistentGraphError):
            Program(("x",), (Block("b0", (), None),), "ghost")

    def test_edge_to_nowhere(self):
        with self.assertRaises(InconsistentGraphError):
            Program(
                ("x",),
                (Block("b0", (Assign("x", 0),), Jump("ghost")),),
                "b0",
            )

    def test_unknown_variable_reference(self):
        with self.assertRaises(InconsistentGraphError):
            Program(
                ("x",),
                (Block("b0", (Assign("z", 1),), None),),
                "b0",
            )
        with self.assertRaises(InconsistentGraphError):
            Program(
                ("x",),
                (Block("b0", (), Cond("z", "<=", 1, "b0", "b0")),),
                "b0",
            )

    def test_bad_op(self):
        with self.assertRaises(ProgramStructureError):
            Cond("x", "<", 1, "b0", "b0")

    def test_assert_lo_gt_hi(self):
        with self.assertRaises(InvalidOperandError):
            AssertRange("x", 5, 4, "a")

    def test_entry_state_length_and_types(self):
        blocks = (Block("b0", (), None),)
        with self.assertRaises(ProgramStructureError):
            Program(("x", "y"), blocks, "b0", entry_state=(1,))
        with self.assertRaises(InvalidOperandError):
            Program(("x",), blocks, "b0", entry_state=(True,))
        with self.assertRaises(InvalidOperandError):
            Program(("x",), blocks, "b0", entry_state=(float("inf"),))

    def test_failure_leaves_no_partial_object(self):
        # 构造抛错 => 调用方根本拿不到对象；不存在“部分变更”的 Program 实例。
        from interval_ai.errors import IntervalAIError

        prog = None
        with self.assertRaises(IntervalAIError):
            prog = Program(("x",), (Block("b0", (Assign("x", float("nan")),), None),), "b0")
        self.assertIsNone(prog)


class TestLimits(unittest.TestCase):
    def test_variable_limit_boundary(self):
        # 恰好 20 个变量合法
        vs = tuple(f"v{i}" for i in range(MAX_VARIABLES))
        p = Program(vs, (Block("b0", (Assign(vs[0], 0),), None),), "b0")
        self.assertEqual(len(p.variables), MAX_VARIABLES)
        # 21 个拒绝
        with self.assertRaises(LimitExceededError):
            Program(tuple(f"w{i}" for i in range(MAX_VARIABLES + 1)),
                    (Block("b0", (), None),), "b0")

    def test_block_limit_boundary(self):
        vs = ("x",)
        blocks_ok = [Block(f"b{i}", (), Jump(f"b{i+1}")) for i in range(MAX_BLOCKS - 1)]
        blocks_ok.append(Block(f"b{MAX_BLOCKS-1}", (), None))
        p = Program(vs, tuple(blocks_ok), "b0")
        self.assertEqual(len(p.blocks), MAX_BLOCKS)

        blocks_bad = [Block(f"b{i}", (), None) for i in range(MAX_BLOCKS + 1)]
        with self.assertRaises(LimitExceededError):
            Program(vs, tuple(blocks_bad), "b0")


class TestBudgetSemantics(unittest.TestCase):
    def test_budget_exhausted_is_not_unknown(self):
        # 无界程序给足预算：结论 unknown 合法返回，不抛异常
        from tests.programs import infinite_growth_program

        res = analyze(infinite_growth_program())
        self.assertEqual(res.status_of("a_dead"), "proved")  # 不可达空真

        # 预算过小：抛预算异常，与 unknown 严格区分
        with self.assertRaises(AnalyzerBudgetExhausted):
            analyze(infinite_growth_program(), max_rounds=2)

    def test_concrete_reference_budget_on_unbounded(self):
        from tests.programs import infinite_growth_program

        with self.assertRaises(ConcreteBudgetExhausted):
            execute_concrete(infinite_growth_program(), max_steps=1000)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
