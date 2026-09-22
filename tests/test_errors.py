"""错误语义、输入上限、预算与"失败不留部分变更"测试。"""

import unittest

from interval_ai import (
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    Interval,
    ValidationError,
    BudgetExhaustedError,
    IntervalAIError,
    analyze,
)
from interval_ai.errors import require_int

from tests._programs import bounded_count_program


class TestNumericValidation(unittest.TestCase):
    def test_accepts_plain_int(self) -> None:
        self.assertEqual(require_int(-7, "p"), -7)
        self.assertEqual(require_int(0, "p"), 0)

    def test_rejects_bool(self) -> None:
        for v in (True, False):
            with self.subTest(v=v):
                with self.assertRaises(ValidationError) as cm:
                    require_int(v, "param.x")
                self.assertIn("param.x", str(cm.exception))

    def test_rejects_nan_and_infinity(self) -> None:
        with self.assertRaises(ValidationError) as cm:
            require_int(float("nan"), "p")
        self.assertIn("NaN", str(cm.exception))
        with self.assertRaises(ValidationError) as cm:
            require_int(float("inf"), "p")
        self.assertIn("Infinity", str(cm.exception))
        with self.assertRaises(ValidationError):
            require_int(float("-inf"), "p")

    def test_rejects_non_integer_float_and_str(self) -> None:
        with self.assertRaises(ValidationError):
            require_int(1.5, "p")
        with self.assertRaises(ValidationError):
            require_int("3", "p")

    def test_statement_constants_validated(self) -> None:
        with self.assertRaises(ValidationError):
            AssignConst("x", True)
        with self.assertRaises(ValidationError):
            AssignAdd("x", "y", float("nan"))


class TestCFGValidation(unittest.TestCase):
    def _one_block(self, **kw) -> dict:
        return dict(
            variables=("x",),
            blocks={"b": Block("b", (), ())},
            entry="b",
        ) | kw

    def test_basic_valid(self) -> None:
        cfg = CFG(**self._one_block())
        self.assertEqual(cfg.entry, "b")

    def test_empty_variables(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(variables=()))

    def test_duplicate_variable(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(variables=("x", "x")))

    def test_too_many_variables(self) -> None:
        names = tuple(f"v{i}" for i in range(21))
        with self.assertRaises(ValidationError) as cm:
            CFG(
                variables=names,
                blocks={"b": Block("b", (), ())},
                entry="b",
            )
        self.assertIn("20", str(cm.exception))

    def test_too_many_blocks(self) -> None:
        blocks = {f"b{i}": Block(f"b{i}", (), ("b0",)) for i in range(41)}
        with self.assertRaises(ValidationError):
            CFG(variables=("x",), blocks=blocks, entry="b0")

    def test_unknown_target_and_source(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (AssignConst("z", 1),), ())}
            ))
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (AssignAdd("x", "z", 1),), ())}
            ))

    def test_unknown_successor_and_entry(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (), ("ghost",))}
            ))
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(entry="ghost"))

    def test_guard_shape(self) -> None:
        with self.assertRaises(ValidationError):
            Guard("x", "<", 3)
        # 有守卫必须两个后继
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (), ("b",), Guard("x", "<=", 3))}
            ))
        # 两个后继必须有守卫
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (), ("b", "b"))}
            ))

    def test_unknown_guard_variable(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"b": Block("b", (), ("b", "b"), Guard("z", "<=", 3))}
            ))

    def test_unknown_entry_bound_variable(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(entry_bounds={"z": Interval(0, 1)}))

    def test_block_key_mismatch(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(**self._one_block(
                blocks={"other": Block("b", (), ())}
            ))

    def test_locations_are_reported(self) -> None:
        try:
            CFG(**self._one_block(
                blocks={"b": Block("b", (AssignConst("z", 1),), ())}
            ))
        except ValidationError as exc:
            self.assertIsNotNone(exc.location)
            self.assertIn("stmts[0]", exc.location)
        else:
            self.fail("应当抛 ValidationError")

    def test_all_errors_derive_from_base(self) -> None:
        self.assertTrue(issubclass(ValidationError, IntervalAIError))
        self.assertTrue(issubclass(BudgetExhaustedError, IntervalAIError))


class TestBudgetSeparation(unittest.TestCase):
    def test_budget_exhaustion_is_not_unknown(self) -> None:
        cfg = bounded_count_program(4)
        with self.assertRaises(BudgetExhaustedError) as cm:
            analyze(cfg, ascending_budget=1)
        # 预算异常携带部分结果，但明确不是已验证不动点
        self.assertIn("block_in", cm.exception.partial)
        # 预算足够时正常返回；无法证明以 unknown 数据表示，而非异常
        res = analyze(cfg)
        self.assertIsInstance(res.asserts, list)

    def test_failed_analysis_leaves_no_partial_mutation(self) -> None:
        cfg = bounded_count_program(4)
        before = tuple((n, b.statements, b.successors) for n, b in cfg.blocks.items())
        with self.assertRaises(BudgetExhaustedError):
            analyze(cfg, ascending_budget=1)
        after = tuple((n, b.statements, b.successors) for n, b in cfg.blocks.items())
        self.assertEqual(before, after)

    def test_bad_budget_argument(self) -> None:
        cfg = bounded_count_program(4)
        with self.assertRaises((TypeError, ValueError)):
            analyze(cfg, ascending_budget=0)
        with self.assertRaises(TypeError):
            analyze(cfg, ascending_budget=True)


if __name__ == "__main__":
    unittest.main()
