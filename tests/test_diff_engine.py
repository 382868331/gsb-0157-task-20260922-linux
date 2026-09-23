"""关系域（区间 × 差界矩阵）引擎行为测试。

期望值来源严格独立于被测核心：
* 差界/区间结论手算后硬编码；
* 有界程序用 :func:`run_bounded` 独立具体枚举做覆盖性与断言对照；
* 健全性由独立符号检查器 :func:`check_local_soundness` 复核；
* 检查器本身与具体执行器都不 import 被测核心（另有 AST/模块测试）。
"""

import ast
import pathlib
import unittest
from dataclasses import replace

from interval_ai import (
    AssertDiff,
    AssignConst,
    AssumeDiff,
    Block,
    CFG,
    Interval,
    ValidationError,
    analyze,
    check_local_soundness,
    run_bounded,
)
from interval_ai.dbm import DiffState

from tests._programs import (
    diff_contradiction_program,
    diff_copy_guard_program,
    diff_loop_initial_store,
    diff_loop_program,
    diff_merge_program,
    diff_outer_invariant_program,
    diff_transitive_chain_program,
)


class TestCopyGuardExchange(unittest.TestCase):
    """y=x 后守卫 x<=0 真支：区间单独得不到的 y<=0 由关系域推出。"""

    def setUp(self) -> None:
        self.res = analyze(diff_copy_guard_program())

    def test_interval_alone_cannot_do_this(self) -> None:
        # 真支 y 被精确收到 (-inf, 0]
        self.assertEqual(self.res.block_in["t"].get("y"), Interval(None, 0))
        # 假支 x>=1，且 y==x，故 y>=1
        self.assertEqual(self.res.block_in["f"].get("y"), Interval(1, None))

    def test_diff_asserts(self) -> None:
        verdicts = [(a.statement.const, a.verdict, a.observed_bound)
                    for a in self.res.diff_asserts]
        self.assertEqual(verdicts, [(0, "proved", 0), (1, "proved", 0)])

    def test_range_assert_uses_relation_refinement(self) -> None:
        # assert y <= 0 在真支可证（仅靠区间 y 原本是 top）
        self.assertEqual(
            [a.verdict for a in self.res.asserts if a.block == "t"], ["proved"]
        )

    def test_sound(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestTransitiveChain(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(diff_transitive_chain_program())

    def test_closure_bound(self) -> None:
        # 差界由块内两条 assume 引入：块入为 top，块出（assume 之后）闭包
        self.assertIsNone(self.res.diff_at("b").bound("x", "z"))
        d = self.res.diff_out["b"]
        self.assertEqual(d.bound("x", "y"), 1)
        self.assertEqual(d.bound("y", "z"), 1)
        self.assertEqual(d.bound("x", "z"), 2)  # 传递闭包

    def test_assert_verdicts(self) -> None:
        self.assertEqual(
            [a.verdict for a in self.res.diff_asserts], ["proved", "unknown"]
        )

    def test_sound(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestContradictionCutsPath(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(diff_contradiction_program())

    def test_block_out_is_bottom(self) -> None:
        self.assertFalse(self.res.block_in["b"].bottom)  # 块入仍可达
        self.assertTrue(self.res.block_out["b"].bottom)  # 矛盾假设后截断

    def test_asserts_vacuous_after_cut(self) -> None:
        # 矛盾假设之后的断言位于不可达点：空真 proved 且 vacuous
        for a in self.res.asserts:
            self.assertEqual(a.verdict, "proved")
            self.assertTrue(a.vacuous)
        for a in self.res.diff_asserts:
            self.assertEqual(a.verdict, "proved")
            self.assertTrue(a.vacuous)

    def test_sound(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestMergeTakesWeakerBound(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(diff_merge_program())

    def test_merged_bound(self) -> None:
        # 一支 x-y<=0、另一支 x-y<=2；合流凸包为 <=2，两支都可达
        self.assertEqual(self.res.diff_at("m").bound("x", "y"), 2)
        self.assertFalse(self.res.block_in["a"].bottom)
        self.assertFalse(self.res.block_in["b2"].bottom)

    def test_assert_verdicts(self) -> None:
        self.assertEqual(
            [a.verdict for a in self.res.diff_asserts], ["proved", "unknown"]
        )

    def test_sound(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestRelationalLoop(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = diff_loop_program()
        self.res = analyze(self.cfg)

    def test_loop_invariant_preserved(self) -> None:
        # body 处 y - x == 2（加宽/收窄后关系不丢）
        body = self.res.diff_at("body")
        self.assertEqual(body.bound("y", "x"), 2)
        self.assertEqual(body.bound("x", "y"), -2)

    def test_exit_exact(self) -> None:
        self.assertEqual(self.res.block_in["exit"].get("x"), Interval(4, 4))
        self.assertEqual(self.res.block_in["exit"].get("y"), Interval(6, 6))
        self.assertEqual(self.res.diff_at("exit").bound("y", "x"), 2)

    def test_all_proved_and_sound(self) -> None:
        self.assertTrue(all(a.verdict == "proved" for a in self.res.asserts))
        self.assertTrue(all(a.verdict == "proved" for a in self.res.diff_asserts))
        self.assertTrue(check_local_soundness(self.res).ok)
        self.assertFalse(self.res.relation_truncated)

    def test_concrete_enumeration_cross_check(self) -> None:
        concrete = run_bounded(self.cfg, [diff_loop_initial_store()])
        self.assertFalse(concrete.truncated)
        self.assertEqual(concrete.assert_violations, [])
        # 每个可达块每变量的具体 min/max 被抽象区间覆盖
        for name in concrete.reachable:
            for var in self.cfg.variables:
                lo = concrete.var_min[name][var]
                hi = concrete.var_max[name][var]
                iv = self.res.block_in[name].get(var)
                self.assertTrue(
                    iv.contains_int(lo) and iv.contains_int(hi),
                    f"{name}.{var}: 具体[{lo},{hi}] 不被 {iv.text} 覆盖",
                )
        # body 具体值对 (x,y) 恒满足 y-x==2（独立枚举验证关系不变量）
        for store in concrete.in_stores["body"]:
            self.assertEqual(store["y"] - store["x"], 2)


class TestOuterVarNotWidened(unittest.TestCase):
    def test_exact_relation_survives_loop(self) -> None:
        res = analyze(diff_outer_invariant_program())
        # y==x 在 init 建立；循环只改 i，选择性加宽必须在循环头/体/出口
        # 全程保住这条差界（这是纯区间域给不出的跨迭代关系）。
        self.assertEqual(res.diff_at("head").bound("y", "x"), 0)
        self.assertEqual(res.diff_at("head").bound("x", "y"), 0)
        self.assertEqual(res.diff_at("body").bound("y", "x"), 0)
        self.assertEqual(res.diff_at("exit").bound("y", "x"), 0)
        # 外层 x 在循环内不改，保持精确 [7,7] 不被加宽
        self.assertEqual(res.block_in["head"].get("x"), Interval(7, 7))
        self.assertEqual(res.block_in["exit"].get("y"), Interval(7, 7))
        self.assertTrue(
            all(a.verdict == "proved" for a in res.diff_asserts)
        )
        self.assertTrue(check_local_soundness(res).ok)


class TestRelationBudget(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = diff_loop_program()

    def test_budget_one_truncates(self) -> None:
        res = analyze(self.cfg, relation_budget=1)
        self.assertTrue(res.relation_truncated)
        self.assertEqual(res.relation_rounds, 1)
        self.assertIsNone(res.diff_in)
        self.assertIsNone(res.diff_out)
        # 未收敛：差分断言一律 unknown（不冒充证明）
        self.assertTrue(all(a.verdict == "unknown" for a in res.diff_asserts))
        # 区间结果仍是合法的纯区间分析，检查器通过
        self.assertTrue(check_local_soundness(res).ok)
        d = res.to_dict()
        self.assertTrue(d["relation_truncated"])
        self.assertIsNone(d["diff_blocks"])

    def test_sufficient_budget_converges(self) -> None:
        res = analyze(self.cfg, relation_budget=1000)
        self.assertFalse(res.relation_truncated)
        self.assertTrue(all(a.verdict == "proved" for a in res.diff_asserts))

    def test_bad_budget_arguments(self) -> None:
        with self.assertRaises((TypeError, ValueError)):
            analyze(self.cfg, relation_budget=0)
        with self.assertRaises(TypeError):
            analyze(self.cfg, relation_budget=True)
        with self.assertRaises(TypeError):
            analyze(self.cfg, relation_budget=3.0)

    def test_truncated_proved_is_rejected_by_checker(self) -> None:
        res = analyze(self.cfg, relation_budget=1)
        # 即便伪造一个 proved，截断检查也必须抓到
        fake = replace(
            res,
            diff_asserts=[
                replace(res.diff_asserts[0], verdict="proved", observed_bound=2)
            ],
        )
        self.assertFalse(check_local_soundness(fake).ok)


class TestDiffValidation(unittest.TestCase):
    def _cfg(self, stmt, variables=("x", "y")):
        return CFG(
            variables=variables,
            blocks={"b": Block("b", (stmt,), ())},
            entry="b",
        )

    def test_five_variables_rejected(self) -> None:
        with self.assertRaises(ValidationError) as cm:
            self._cfg(AssumeDiff("a", "b", 1), variables=tuple("abcde"))
        self.assertIn("4", str(cm.exception))

    def test_four_variables_accepted(self) -> None:
        cfg = CFG(
            variables=tuple("abcd"),
            blocks={"b": Block(
                "b", (AssumeDiff("a", "b", 1), AssertDiff("c", "d", 0)), ()
            )},
            entry="b",
        )
        res = analyze(cfg)
        self.assertTrue(check_local_soundness(res).ok)

    def test_twenty_variables_still_ok_without_diff(self) -> None:
        # 纯区间程序仍允许 20 个变量（旧契约不缩）
        names = tuple(f"v{i}" for i in range(20))
        cfg = CFG(
            variables=names,
            blocks={"b": Block("b", (), ())},
            entry="b",
        )
        self.assertFalse(cfg.uses_diff_domain)
        analyze(cfg)

    def test_unknown_operands(self) -> None:
        with self.assertRaises(ValidationError):
            self._cfg(AssumeDiff("z", "y", 1))
        with self.assertRaises(ValidationError):
            self._cfg(AssertDiff("x", "z", 1))

    def test_same_variable_operands_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            self._cfg(AssumeDiff("x", "x", 1))
        with self.assertRaises(ValidationError):
            self._cfg(AssertDiff("x", "x", -1))

    def test_non_string_operand_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            self._cfg(AssumeDiff(1, "y", 1))

    def test_bool_constant_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            AssumeDiff("x", "y", True)
        with self.assertRaises(ValidationError):
            AssertDiff("x", "y", False)

    def test_bad_constant_float_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            AssumeDiff("x", "y", 1.5)

    def test_location_points_to_operand(self) -> None:
        try:
            self._cfg(AssumeDiff("z", "y", 1))
        except ValidationError as exc:
            self.assertIsNotNone(exc.location)
            self.assertIn("a", exc.location)
        else:
            self.fail("应当抛 ValidationError")


class TestDiffDeterminism(unittest.TestCase):
    def test_repeated_runs_identical(self) -> None:
        cfg = diff_loop_program()
        r1, r2 = analyze(cfg), analyze(cfg)
        self.assertEqual(r1.block_in, r2.block_in)
        self.assertEqual(
            [a.to_dict() for a in r1.diff_asserts],
            [a.to_dict() for a in r2.diff_asserts],
        )
        self.assertEqual(r1.relation_rounds, r2.relation_rounds)


class TestCheckerIndependenceForDBM(unittest.TestCase):
    def test_checker_does_not_import_dbm_or_engine(self) -> None:
        src = (
            pathlib.Path(__file__).resolve().parents[1]
            / "interval_ai" / "checker.py"
        )
        tree = ast.parse(src.read_text(encoding="utf-8"))
        imported: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module)
        self.assertNotIn("interval_ai.dbm", imported)
        self.assertNotIn("interval_ai.engine", imported)
        self.assertNotIn("interval_ai.transfer", imported)


class TestTamperedDiffInvariantCaught(unittest.TestCase):
    def _cfg(self):
        return CFG(
            variables=("x", "y"),
            blocks={
                "b": Block("b", (AssumeDiff("x", "y", 0),), ("b2",)),
                "b2": Block("b2", (AssertDiff("x", "y", 0),), ()),
            },
            entry="b",
        )

    def test_relaxed_successor_invariant_caught(self) -> None:
        res = analyze(self._cfg())
        n = 3
        topm = tuple(
            tuple(0 if i == j else None for j in range(n)) for i in range(n)
        )
        bad_in = dict(res.diff_in)
        bad_in["b2"] = DiffState(res.cfg.variable_tuple, topm, False)
        bad = replace(res, diff_in=bad_in)
        self.assertFalse(check_local_soundness(bad).ok)

    def test_false_diff_proved_caught(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={"b": Block(
                "b", (AssumeDiff("x", "y", 2), AssertDiff("x", "y", 1)), ()
            )},
            entry="b",
        )
        res = analyze(cfg)
        bad = replace(
            res,
            diff_asserts=[
                replace(res.diff_asserts[0], verdict="proved", observed_bound=0)
            ],
        )
        self.assertFalse(check_local_soundness(bad).ok)


if __name__ == "__main__":
    unittest.main()
