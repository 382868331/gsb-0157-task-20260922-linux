"""独立局部包含性检查器测试。

重点：
* 检查器独立于被测核心（AST 级别验证不导入 transfer/engine）；
* 证明是符号端点比较，对无穷区间与大整数边界同样有效，不做任何枚举；
* 能抓出"边界差一""错误加宽"这类采样难以稳定命中的不健全结果。
"""

import ast
import pathlib
import unittest
from dataclasses import replace

from interval_ai import (
    AbstractState,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssertRange,
    Block,
    CFG,
    Guard,
    Interval,
    analyze,
    check_edge_guard,
    check_local_soundness,
    check_transfer_step,
    transfer_statement,
)

CHECKER_SRC = pathlib.Path(__file__).resolve().parents[1] / "interval_ai" / "checker.py"


class TestCheckerIndependence(unittest.TestCase):
    def test_checker_does_not_import_core(self) -> None:
        tree = ast.parse(CHECKER_SRC.read_text(encoding="utf-8"))
        imported: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module)
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
        self.assertNotIn("interval_ai.transfer", imported)
        self.assertNotIn("interval_ai.engine", imported)
        self.assertNotIn(".transfer", imported)
        self.assertNotIn(".engine", imported)

    def test_no_enumeration_calls(self) -> None:
        # 检查器源码里不得出现 range(...) 枚举/采样调用
        src = CHECKER_SRC.read_text(encoding="utf-8")
        tree = ast.parse(src)
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                self.assertNotEqual(node.func.id, "range")


def _state2() -> AbstractState:
    return AbstractState(("x", "y"), {"x": Interval(0, 10), "y": Interval.top()})


class TestSingleStepChecker(unittest.TestCase):
    def test_assign_const_exact(self) -> None:
        before = _state2()
        after = transfer_statement(before, AssignConst("x", 3))
        report = check_transfer_step(AssignConst("x", 3), before, after)
        self.assertTrue(report.ok, report.violations)

    def test_assign_add_off_by_one_is_caught(self) -> None:
        # 正确像应为 [1, 11]；伪造一个"差一"结果 [1, 10]，必须被符号检查抓到。
        before = _state2()
        tampered = before.assign("x", Interval(1, 10))
        report = check_transfer_step(AssignAdd("x", "x", 1), before, tampered)
        self.assertFalse(report.ok)

    def test_infinite_interval_symbolic_not_enumerated(self) -> None:
        before = AbstractState(("x",), {"x": Interval(0, None)})
        stmt = AssignAdd("x", "x", 1)
        after = transfer_statement(before, stmt)  # [1, +inf)
        report = check_transfer_step(stmt, before, after)
        self.assertTrue(report.ok)
        # 上界被错误截成有限大数也必须被抓到（采样几乎不可能命中边界）
        bad = before.assign("x", Interval(1, 10**50))
        self.assertFalse(check_transfer_step(stmt, before, bad).ok)

    def test_copy_preserves_infinite_bound(self) -> None:
        before = AbstractState(("x", "y"), {"x": Interval(None, 7), "y": Interval.top()})
        stmt = AssignCopy("y", "x")
        after = transfer_statement(before, stmt)
        self.assertTrue(check_transfer_step(stmt, before, after).ok)

    def test_edge_guard_complement(self) -> None:
        out = AbstractState(("x",), {"x": Interval.top()})
        guard = Guard("x", "<=", 5)
        true_in = AbstractState(("x",), {"x": Interval(None, 5)})
        false_in = AbstractState(("x",), {"x": Interval(6, None)})
        self.assertTrue(check_edge_guard(guard, True, out, true_in).ok)
        self.assertTrue(check_edge_guard(guard, False, out, false_in).ok)
        # 假支漏掉 x=6：给成 [7, +inf) 必须失败
        too_narrow = AbstractState(("x",), {"x": Interval(7, None)})
        self.assertFalse(check_edge_guard(guard, False, out, too_narrow).ok)


class TestWholeResultSoundness(unittest.TestCase):
    def _cfg(self) -> CFG:
        return CFG(
            variables=("i",),
            blocks={
                "init": Block("init", (AssignConst("i", 0),), ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 4)),
                "body": Block("body", (AssignAdd("i", "i", 1),), ("head",)),
                "exit": Block("exit", (AssertRange("i", 5, 5),), ()),
            },
            entry="init",
        )

    def test_valid_result_passes(self) -> None:
        res = analyze(self._cfg())
        self.assertTrue(check_local_soundness(res).ok)

    def test_tampered_invariant_is_caught(self) -> None:
        res = analyze(self._cfg())
        bad_ins = dict(res.block_in)
        # 把 exit 的入不变量从 [5,5] 篡改成 [0,5]（边过滤包含被破坏）
        bad_ins["exit"] = bad_ins["exit"].assign("i", Interval(0, 5))
        bad = replace(res, block_in=bad_ins)
        report = check_local_soundness(bad)
        self.assertFalse(report.ok)
        self.assertTrue(any("exit" in v for v in report.violations))

    def test_false_proved_is_caught(self) -> None:
        res = analyze(self._cfg())
        # 篡改成一个 observed 不满足 required 却标 proved 的断言
        bad_assert = replace(res.asserts[0], verdict="proved",
                             observed=Interval(0, 100))
        bad = replace(res, asserts=[bad_assert])
        report = check_local_soundness(bad)
        self.assertFalse(report.ok)

    def test_entry_bounds_contained(self) -> None:
        cfg = CFG(
            variables=("i",),
            blocks={"b": Block("b", (AssertRange("i", 0, 5),), ())},
            entry="b",
            entry_bounds={"i": Interval(0, 5)},
        )
        res = analyze(cfg)
        self.assertTrue(check_local_soundness(res).ok)


if __name__ == "__main__":
    unittest.main()
