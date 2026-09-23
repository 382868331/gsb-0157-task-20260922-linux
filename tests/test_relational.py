"""区间 × 差分约束简约积引擎测试。

期望值全部手算硬编码（常量程序逐块推导 / Floyd–Warshall 手算），不调用被测
实现生成期望；同时用：

* 独立符号检查器 :func:`check_local_soundness` 复核每个结果；
* 独立具体执行器 :func:`run_bounded` 对有界程序做覆盖性对照。
"""

import unittest

from interval_ai import (
    AssertDiff,
    AssumeDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    Block,
    CFG,
    Guard,
    Interval,
    BudgetExhaustedError,
    ValidationError,
    analyze,
    check_local_soundness,
    run_bounded,
)


def _diff_map(result):
    return {(a.block, a.index): (a.verdict, a.observed_bound, a.vacuous)
            for a in result.diff_asserts}


def _range_map(result):
    return {(a.block, a.index): (a.verdict, a.vacuous) for a in result.asserts}


class TestStraightLine(unittest.TestCase):
    def _cfg(self) -> CFG:
        # x := 2; y := x + 3；断言 y - x <= 3 / x - y <= -3 均可证，
        # 而 y - x <= 2 不可证。
        return CFG(
            variables=("x", "y"),
            blocks={
                "s": Block(
                    "s",
                    (
                        AssignConst("x", 2),
                        AssignAdd("y", "x", 3),
                        AssertDiff("y", "x", 3),
                        AssertDiff("x", "y", -3),
                        AssertDiff("y", "x", 2),
                    ),
                    (),
                ),
            },
            entry="s",
        )

    def test_difference_asserts(self) -> None:
        r = analyze(self._cfg())
        d = _diff_map(r)
        self.assertEqual(d[("s", 2)], ("proved", 3, False))
        self.assertEqual(d[("s", 3)], ("proved", -3, False))
        self.assertEqual(d[("s", 4)], ("unknown", 3, False))
        self.assertTrue(check_local_soundness(r).ok)

    def test_zero_node_form_is_single_variable_bound(self) -> None:
        # x := 7；AssertDiff(x, None, 7) 即 x <= 7；AssertDiff(x, None, 6) 失败
        cfg = CFG(
            variables=("x",),
            blocks={
                "s": Block(
                    "s",
                    (AssignConst("x", 7), AssertDiff("x", None, 7),
                     AssertDiff("x", None, 6)),
                    (),
                ),
            },
            entry="s",
        )
        r = analyze(cfg)
        d = _diff_map(r)
        self.assertEqual(d[("s", 1)], ("proved", 7, False))
        self.assertEqual(d[("s", 2)], ("unknown", 7, False))
        self.assertTrue(check_local_soundness(r).ok)


class TestAssumePrunesAndRefines(unittest.TestCase):
    def test_contradictory_assume_makes_suffix_unreachable(self) -> None:
        # x - y <= 1 与 y - x <= -2（x - y >= 2）矛盾：同块后续断言空真，
        # 后继块不可达。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block(
                    "s",
                    (AssumeDiff("x", "y", 1), AssumeDiff("y", "x", -2),
                     AssertRange("x", 0, 0)),
                    ("e",),
                ),
                "e": Block("e", (AssertRange("x", 0, 0),), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertTrue(r.block_in["e"].bottom)
        self.assertEqual(_range_map(r)[("s", 2)], ("proved", True))
        self.assertEqual(_range_map(r)[("e", 0)], ("proved", True))
        self.assertTrue(check_local_soundness(r).ok)

    def test_interval_refined_by_diff_then_guard(self) -> None:
        # 区间单独无法表达的跨变量收窄：
        # x,y 初始均无界；assume x - y <= 0；分支守卫 y <= 3 为真 ⇒ x <= 3。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block("s", (AssumeDiff("x", "y", 0),), ("g",)),
                "g": Block("g", (), ("t", "f"), Guard("y", "<=", 3)),
                "t": Block("t", (AssertRange("x", None, 3),
                                 AssertDiff("x", "y", 0)), ()),
                "f": Block("f", (AssertDiff("x", "y", 0),), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        # 经 DBM 简约，真支 x 的区间被精确收窄到 (-inf, 3]
        self.assertEqual(r.block_in["t"].get("x"), Interval(None, 3))
        self.assertEqual(r.block_in["t"].get("y"), Interval(None, 3))
        self.assertEqual(_range_map(r)[("t", 0)], ("proved", False))
        self.assertEqual(_diff_map(r)[("t", 1)], ("proved", 0, False))
        # 假支 y >= 4 ⇒ x <= y 不给出 x 的有限上界；y 下界精确
        self.assertEqual(r.block_in["f"].get("y"), Interval(4, None))
        self.assertEqual(_diff_map(r)[("f", 0)], ("proved", 0, False))
        self.assertTrue(check_local_soundness(r).ok)


class TestBranchMerge(unittest.TestCase):
    def test_difference_survives_merge(self) -> None:
        # x := 0；if (j >= 0) { y := 0 } else { y := 1 }；合流后：
        # 区间只知 y in [0,1]，但两支都满足 x - y <= 0（界 0 与 -1 的合流=0）。
        cfg = CFG(
            variables=("x", "y", "j"),
            blocks={
                "s": Block("s", (AssignConst("x", 0),), ("g",)),
                "g": Block("g", (), ("a", "b"), Guard("j", ">=", 0)),
                "a": Block("a", (AssignConst("y", 0),), ("m",)),
                "b": Block("b", (AssignConst("y", 1),), ("m",)),
                "m": Block(
                    "m",
                    (AssertRange("y", 0, 1), AssertDiff("x", "y", 0),
                     AssertDiff("x", "y", -1)),
                    (),
                ),
            },
            entry="s",
        )
        r = analyze(cfg)
        d = _diff_map(r)
        self.assertEqual(d[("m", 1)], ("proved", 0, False))
        # 更强的 x - y <= -1 在 y=0 支不成立，只能 unknown
        self.assertEqual(d[("m", 2)], ("unknown", 0, False))
        self.assertTrue(check_local_soundness(r).ok)

    def test_merge_with_unreachable_branch_is_exact(self) -> None:
        # x := 0；if (x >= 5) 死支 else 活支；合流点关系不被死支污染。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block(
                    "s", (AssignConst("x", 0), AssignConst("y", 0)), ("g",)
                ),
                "g": Block("g", (), ("dead", "live"), Guard("x", ">=", 5)),
                "dead": Block("dead", (), ("m",)),
                "live": Block("live", (), ("m",)),
                "m": Block("m", (AssertDiff("x", "y", 0),), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertTrue(r.block_in["dead"].bottom)
        self.assertEqual(_diff_map(r)[("m", 0)], ("proved", 0, False))
        self.assertTrue(check_local_soundness(r).ok)


class TestLoopRelation(unittest.TestCase):
    def _cfg(self) -> CFG:
        # x := 0; y := 1; while (x <= 4) {
        #   assert y - x <= 1; assert x - y <= -1; x++; y++
        # }
        return CFG(
            variables=("x", "y"),
            blocks={
                "init": Block(
                    "init", (AssignConst("x", 0), AssignConst("y", 1)), ("head",)
                ),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (
                        AssertDiff("y", "x", 1),
                        AssertDiff("x", "y", -1),
                        AssignAdd("x", "x", 1),
                        AssignAdd("y", "y", 1),
                    ),
                    ("head",),
                ),
                "exit": Block(
                    "exit",
                    (AssertDiff("y", "x", 1), AssertDiff("x", "y", -1),
                     AssertRange("x", 5, 5), AssertRange("y", 6, 6)),
                    (),
                ),
            },
            entry="init",
        )

    def setUp(self) -> None:
        self.r = analyze(self._cfg())

    def test_converged_with_single_widen_point(self) -> None:
        self.assertTrue(self.r.relational_converged)
        self.assertEqual(self.r.widen_points, ("head",))
        self.assertLessEqual(self.r.narrowing_rounds, 8)

    def test_interval_invariants_hand_computed(self) -> None:
        self.assertEqual(self.r.block_in["head"].get("x"), Interval(0, 5))
        self.assertEqual(self.r.block_in["head"].get("y"), Interval(1, 6))
        self.assertEqual(self.r.block_in["body"].get("x"), Interval(0, 4))
        self.assertEqual(self.r.block_in["exit"].get("x"), Interval(5, 5))
        self.assertEqual(self.r.block_in["exit"].get("y"), Interval(6, 6))

    def test_offset_relation_survives_widening(self) -> None:
        head = self.r.diff_state_at("head")
        self.assertEqual(head.bound_of("y", "x"), 1)
        self.assertEqual(head.bound_of("x", "y"), -1)

    def test_loop_asserts_and_exit_asserts_proved(self) -> None:
        d = _diff_map(self.r)
        self.assertEqual(d[("body", 0)][0], "proved")
        self.assertEqual(d[("body", 1)][0], "proved")
        self.assertEqual(d[("exit", 0)][0], "proved")
        self.assertEqual(d[("exit", 1)][0], "proved")

    def test_soundness_and_concrete_coverage(self) -> None:
        self.assertTrue(check_local_soundness(self.r).ok)
        concrete = run_bounded(self._cfg(), [{"x": 0, "y": 1}])
        self.assertFalse(concrete.truncated)
        self.assertEqual(concrete.var_min["body"]["x"], 0)
        self.assertEqual(concrete.var_max["body"]["y"], 5)
        self.assertEqual(concrete.assert_violations, [])
        self.assertEqual(concrete.diff_violations, [])

    def test_loop_counter_relation_unknown_when_offset_grows(self) -> None:
        # 循环里 y 每轮 +2、x 每轮 +1：差值发散，加宽后 y-x 上界 +∞，
        # assert y - x <= 1 只能 unknown（区间同样无法证明）。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0), AssignConst("y", 0)),
                              ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (AssertDiff("y", "x", 1), AssignAdd("x", "x", 1),
                     AssignAdd("y", "y", 2)),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        r = analyze(cfg)
        self.assertTrue(r.relational_converged)
        self.assertEqual(_diff_map(r)[("body", 0)][0], "unknown")
        self.assertIsNone(_diff_map(r)[("body", 0)][1])
        self.assertTrue(check_local_soundness(r).ok)


class TestNonConvergenceFallback(unittest.TestCase):
    def test_loop_budget_exhausted_gives_unknown_not_error(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0), AssignConst("y", 1)),
                              ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (AssertDiff("y", "x", 1),
                     AssignAdd("x", "x", 1), AssignAdd("y", "y", 1)),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        r = analyze(cfg, loop_budget=1)
        self.assertFalse(r.relational_converged)
        self.assertEqual(r.relational_budget, 1)
        # 非空真的差分断言一律 unknown
        self.assertEqual(_diff_map(r)[("body", 0)], ("unknown", None, False))
        # 取不到关系不变量（明确报错，而不是给出半成品）
        with self.assertRaises(ValueError):
            r.diff_state_at("body")
        # 区间结论照常给出，独立检查器认可回退结果
        self.assertEqual(r.block_in["exit"].get("x"), Interval(5, 5))
        self.assertTrue(check_local_soundness(r).ok)

    def test_fallback_to_dict_is_well_formed(self) -> None:
        cfg = CFG(
            variables=("x",),
            blocks={"b": Block("b", (AssertDiff("x", None, 0),), ())},
            entry="b",
        )
        r = analyze(cfg, loop_budget=1)
        self.assertFalse(r.relational_converged)
        d = r.to_dict()  # 未收敛时不得因缺失 diff 状态而崩溃
        self.assertFalse(d["relational"]["converged"])
        self.assertNotIn("diff_blocks", d["relational"])
        self.assertEqual(
            d["relational"]["diff_asserts"][0]["verdict"], "unknown"
        )

    def test_ascending_budget_still_hard_error(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0),), ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body", (AssignAdd("x", "x", 1),),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        # 该程序实际不含差分语句；防御性预算耗尽仍是硬错误（旧语义不变）
        with self.assertRaises(BudgetExhaustedError):
            analyze(cfg, ascending_budget=1)

    def test_bad_budget_arguments(self) -> None:
        cfg = CFG(
            variables=("x",),
            blocks={"b": Block("b", (AssertDiff("x", None, 0),), ())},
            entry="b",
        )
        with self.assertRaises(ValueError):
            analyze(cfg, loop_budget=0)
        with self.assertRaises(TypeError):
            analyze(cfg, loop_budget=True)
        with self.assertRaises(ValueError):
            analyze(cfg, ascending_budget=0)


class TestValidation(unittest.TestCase):
    def test_diff_requires_at_most_four_variables(self) -> None:
        # 5 个变量 + 差分语句：构造期拒绝
        with self.assertRaises(ValidationError) as cm:
            CFG(
                variables=tuple("abcde"),
                blocks={
                    "b": Block("b", (AssumeDiff("a", "b", 0),), ()),
                },
                entry="b",
            )
        self.assertIn("4", str(cm.exception))
        # 不含差分语句时仍允许最多 20 个变量（旧契约不变）
        CFG(
            variables=tuple(f"v{i}" for i in range(5)),
            blocks={"b": Block("b", (), ())},
            entry="b",
        )

    def test_four_variables_accepted(self) -> None:
        # 4 个程序变量（DBM 5×5，含零节点）：a-b<=0、c-d<=-2 各自可证；
        # 彼此无关联的 d-a 即便常数很大也推不出来，必须 unknown。
        cfg = CFG(
            variables=tuple("abcd"),
            blocks={
                "b": Block(
                    "b",
                    (AssumeDiff("a", "b", 0), AssumeDiff("c", "d", -2),
                     AssertDiff("a", "b", 0),
                     AssertDiff("c", "d", -2),
                     AssertDiff("d", "a", 10**20)),
                    (),
                ),
            },
            entry="b",
        )
        r = analyze(cfg)
        self.assertTrue(r.relational_converged)
        d = _diff_map(r)
        self.assertEqual(d[("b", 2)], ("proved", 0, False))
        self.assertEqual(d[("b", 3)], ("proved", -2, False))
        self.assertEqual(d[("b", 4)], ("unknown", None, False))
        self.assertTrue(check_local_soundness(r).ok)

    def test_same_variable_left_right_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            AssumeDiff("x", "x", 0)
        with self.assertRaises(ValidationError):
            AssertDiff("x", "x", -1)

    def test_bool_constant_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            AssumeDiff("x", "y", True)

    def test_undeclared_variables_rejected(self) -> None:
        with self.assertRaises(ValidationError):
            CFG(
                variables=("x",),
                blocks={"b": Block("b", (AssumeDiff("z", "x", 0),), ())},
                entry="b",
            )
        with self.assertRaises(ValidationError):
            CFG(
                variables=("x",),
                blocks={"b": Block("b", (AssertDiff("x", "z", 0),), ())},
                entry="b",
            )

    def test_zero_node_on_either_side_validation(self) -> None:
        # left=None 表示左端取零节点（x >= -c 形式），合法：
        cfg = CFG(
            variables=("x",),
            blocks={
                "b": Block(
                    "b",
                    (AssumeDiff(None, "x", -2), AssertDiff(None, "x", -2)),
                    (),
                ),
            },
            entry="b",
        )
        r = analyze(cfg)
        # -x <= -2 ⇔ x >= 2：下界精确为 2
        self.assertEqual(r.block_out["b"].get("x"), Interval(2, None))
        self.assertEqual(_diff_map(r)[("b", 1)], ("proved", -2, False))
        self.assertTrue(check_local_soundness(r).ok)
        # 两端同时为零节点没有意义：拒绝
        with self.assertRaises(ValidationError):
            AssumeDiff(None, None, 0)
        with self.assertRaises(ValidationError):
            AssertDiff(None, None, 1)


class TestLegacyBehavior(unittest.TestCase):
    def test_programs_without_diff_are_not_relational(self) -> None:
        from tests._programs import bounded_count_program

        r = analyze(bounded_count_program(4))
        self.assertFalse(r.relational_enabled)
        self.assertEqual(r.diff_asserts, [])
        self.assertEqual(r.block_in_diff, {})
        with self.assertRaises(ValueError):
            r.diff_state_at("head")
        # to_dict 不携带 relational 段
        self.assertNotIn("relational", r.to_dict())

    def test_relational_result_dict_shape(self) -> None:
        cfg = CFG(
            variables=("x",),
            blocks={"b": Block("b", (AssertDiff("x", None, 0),), ())},
            entry="b",
            entry_bounds={"x": Interval(0, 0)},
        )
        r = analyze(cfg)
        d = r.to_dict()["relational"]
        self.assertEqual(d["converged"], True)
        self.assertEqual(d["loop_budget"], r.relational_budget)
        self.assertEqual(d["diff_asserts"][0]["verdict"], "proved")
        self.assertIn("diff_blocks", d)

    def test_determinism(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0), AssignConst("y", 0)),
                              ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (AssertDiff("y", "x", 0),
                     AssignAdd("x", "x", 1), AssignAdd("y", "y", 1)),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        r1, r2 = analyze(cfg), analyze(cfg)
        self.assertEqual(r1.block_in, r2.block_in)
        self.assertEqual(r1.block_in_diff, r2.block_in_diff)
        self.assertEqual([a.to_dict() for a in r1.diff_asserts],
                         [a.to_dict() for a in r2.diff_asserts])


class TestMoreEdges(unittest.TestCase):
    def test_entry_is_loop_head_with_relation(self) -> None:
        # 入口即循环头：x=y=0；while (x<=3){x++;y++}；出口 x==y==4，
        # y-x<=0 在循环头、出口都保持（entry_bounds 提供初始相等）。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "head": Block(
                    "head", (AssertDiff("y", "x", 0),),
                    ("body", "done"), Guard("x", "<=", 3),
                ),
                "body": Block(
                    "body",
                    (AssignAdd("x", "x", 1), AssignAdd("y", "y", 1)),
                    ("head",),
                ),
                "done": Block(
                    "done",
                    (AssertRange("x", 4, 4), AssertRange("y", 4, 4),
                     AssertDiff("y", "x", 0)),
                    (),
                ),
            },
            entry="head",
            entry_bounds={"x": Interval(0, 0), "y": Interval(0, 0)},
        )
        r = analyze(cfg)
        self.assertTrue(r.relational_converged)
        self.assertEqual(r.block_in["done"].get("x"), Interval(4, 4))
        self.assertEqual(r.diff_state_at("head").bound_of("y", "x"), 0)
        self.assertEqual(_diff_map(r)[("done", 2)][0], "proved")
        self.assertTrue(check_local_soundness(r).ok)

    def test_negative_constant_add_relation(self) -> None:
        # x := 5; y := x - 2：y - x <= -2 且 x - y <= 2 都可证。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block(
                    "s",
                    (AssignConst("x", 5), AssignAdd("y", "x", -2),
                     AssertDiff("y", "x", -2), AssertDiff("x", "y", 2)),
                    (),
                ),
            },
            entry="s",
        )
        r = analyze(cfg)
        d = _diff_map(r)
        self.assertEqual(d[("s", 2)], ("proved", -2, False))
        self.assertEqual(d[("s", 3)], ("proved", 2, False))
        self.assertEqual(r.block_out["s"].get("y"), Interval(3, 3))
        self.assertTrue(check_local_soundness(r).ok)

    def test_assume_with_zero_node_binds_interval(self) -> None:
        # assume x <= 2（right=None）；随后守卫 x >= 2：真支恰为 x == 2
        # （上界来自假设、下界来自守卫补集），假支为 x <= 1，两支均可行。
        cfg = CFG(
            variables=("x",),
            blocks={
                "s": Block("s", (AssumeDiff("x", None, 2),), ("g",)),
                "g": Block("g", (), ("t", "f"), Guard("x", ">=", 2)),
                "t": Block("t", (AssertRange("x", 2, 2),), ()),
                "f": Block("f", (AssertRange("x", None, 1),), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertEqual(r.block_in["t"].get("x"), Interval(2, 2))
        self.assertEqual(r.block_in["f"].get("x"), Interval(None, 1))
        self.assertTrue(all(a.verdict == "proved" for a in r.asserts))
        self.assertTrue(check_local_soundness(r).ok)

    def test_two_sided_assume_chain_makes_guard_branch_dead(self) -> None:
        # 先用两个单边假设把 x 夹成 x == 2：x<=2 与 x>=2（0-x<=-2）；
        # 此时守卫 x>=2 的假支 x<=1 不可达。
        cfg = CFG(
            variables=("x",),
            blocks={
                "s": Block(
                    "s",
                    (AssumeDiff("x", None, 2), AssumeDiff(None, "x", -2)),
                    ("g",),
                ),
                "g": Block("g", (), ("t", "f"), Guard("x", ">=", 2)),
                "t": Block("t", (AssertRange("x", 2, 2),), ()),
                "f": Block("f", (AssertRange("x", 0, 0),), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertEqual(r.block_in["t"].get("x"), Interval(2, 2))
        self.assertTrue(r.block_in["f"].bottom)
        self.assertTrue(check_local_soundness(r).ok)

    def test_copy_from_unconstrained_then_guard_on_copy(self) -> None:
        # y := x（x 无界）；守卫 y <= 3 真支：x <= 3 必须由关系域推出。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block("s", (AssignCopy("y", "x"),), ("g",)),
                "g": Block("g", (), ("t", "f"), Guard("y", "<=", 3)),
                "t": Block("t", (AssertRange("x", None, 3),
                                 AssertDiff("x", "y", 0)), ()),
                "f": Block("f", (AssertRange("x", 4, None),
                                 AssertDiff("y", "x", 0)), ()),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertEqual(r.block_in["t"].get("x"), Interval(None, 3))
        self.assertEqual(r.block_in["f"].get("x"), Interval(4, None))
        self.assertTrue(all(a.verdict == "proved" for a in r.asserts))
        self.assertTrue(all(a.verdict == "proved" for a in r.diff_asserts))
        self.assertTrue(check_local_soundness(r).ok)


def _rel_cfg() -> CFG:
    # 直线小程序：x := 0; y := x + 1；AssertDiff y-x<=1。
    return CFG(
        variables=("x", "y"),
        blocks={
            "s": Block(
                "s",
                (AssignConst("x", 0), AssignAdd("y", "x", 1),
                 AssertDiff("y", "x", 1)),
                (),
            ),
        },
        entry="s",
    )


class TestCheckerCatchesTampering(unittest.TestCase):
    def test_false_diff_proved_is_caught(self) -> None:
        from dataclasses import replace

        # y := x + 1 后 y-x 的真实界是 1；断言 y-x<=0 本应 unknown，
        # 篡改成 proved 必须被独立检查器抓到。
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block(
                    "s",
                    (AssignConst("x", 0), AssignAdd("y", "x", 1),
                     AssertDiff("y", "x", 0)),
                    (),
                ),
            },
            entry="s",
        )
        r = analyze(cfg)
        self.assertEqual(r.diff_asserts[0].verdict, "unknown")
        bad_assert = replace(r.diff_asserts[0], verdict="proved")
        bad = replace(r, diff_asserts=[bad_assert])
        report = check_local_soundness(bad)
        self.assertFalse(report.ok)
        self.assertTrue(any("diff-assert" in v for v in report.violations))

    def test_vacuous_diff_assert_at_reachable_point_caught(self) -> None:
        from dataclasses import replace

        r = analyze(_rel_cfg())
        bad_assert = replace(r.diff_asserts[0], vacuous=True)
        bad = replace(r, diff_asserts=[bad_assert])
        self.assertFalse(check_local_soundness(bad).ok)

    def test_wrong_observed_bound_is_caught(self) -> None:
        from dataclasses import replace

        r = analyze(_rel_cfg())
        bad_assert = replace(r.diff_asserts[0], observed_bound=42)
        bad = replace(r, diff_asserts=[bad_assert])
        self.assertFalse(check_local_soundness(bad).ok)

    def test_weakened_diff_invariant_is_caught(self) -> None:
        # 把 s 出状态的 DBM 界 y-x<=1 篡改成更松的 +∞：块转移相等性被破坏。
        r = analyze(_rel_cfg())
        out = r.block_out_diff["s"]
        rows = [list(row) for row in out.matrix]
        yi = out.variables.index("y")
        xi = out.variables.index("x")
        rows[yi][xi] = None
        weakened = type(out)(out.variables, tuple(tuple(row) for row in rows))
        bad_outs = dict(r.block_out_diff)
        bad_outs["s"] = weakened
        from dataclasses import replace
        bad = replace(r, block_out_diff=bad_outs)
        report = check_local_soundness(bad)
        self.assertFalse(report.ok)

    def test_fallback_non_proved_diff_assert_caught(self) -> None:
        from dataclasses import replace

        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0), AssignConst("y", 1)),
                              ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (AssertDiff("y", "x", 1),
                     AssignAdd("x", "x", 1), AssignAdd("y", "y", 1)),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        r = analyze(cfg, loop_budget=1)
        self.assertFalse(r.relational_converged)
        # 未收敛却把差分断言标 proved（非空真）：必须被抓
        bad_assert = replace(r.diff_asserts[0], verdict="proved")
        bad = replace(r, diff_asserts=[bad_assert])
        self.assertFalse(check_local_soundness(bad).ok)


class TestConcreteDiffSemantics(unittest.TestCase):
    """独立具体执行器的差分语义对照（期望值取自具体整数，不取自已核心）。"""

    def test_assume_prunes_concrete_paths(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block("s", (AssumeDiff("x", "y", 0),), ("e",)),
                "e": Block("e", (AssertDiff("x", "y", 0),), ()),
            },
            entry="s",
        )
        # 满足 x<=y 的具体初值：两断言都不违反
        rep = run_bounded(cfg, [{"x": 2, "y": 3}])
        self.assertFalse(rep.truncated)
        self.assertEqual(rep.diff_violations, [])
        self.assertIn("e", rep.reachable)
        # 违反假设的初值：在 s 处被剪枝，e 不可达
        rep2 = run_bounded(cfg, [{"x": 5, "y": 0}])
        self.assertNotIn("e", rep2.reachable)

    def test_assert_diff_violation_recorded(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "s": Block("s", (AssignConst("x", 3), AssignConst("y", 0),
                                 AssertDiff("x", "y", 2)), ()),
            },
            entry="s",
        )
        rep = run_bounded(cfg, [{"x": 0, "y": 0}])
        # 3 - 0 = 3 > 2：记录一条差分断言违反
        self.assertEqual(len(rep.diff_violations), 1)
        self.assertEqual(rep.diff_violations[0][:2], ("s", 2))
        # 抽象分析对同一程序只能给 unknown
        r = analyze(cfg)
        self.assertEqual(_diff_map(r)[("s", 2)][0], "unknown")
        self.assertTrue(check_local_soundness(r).ok)

    def test_concrete_agrees_with_proved_loop_invariant(self) -> None:
        cfg = CFG(
            variables=("x", "y"),
            blocks={
                "init": Block("init", (AssignConst("x", 0), AssignConst("y", 1)),
                              ("head",)),
                "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
                "body": Block(
                    "body",
                    (AssertDiff("y", "x", 1),
                     AssignAdd("x", "x", 1), AssignAdd("y", "y", 1)),
                    ("head",),
                ),
                "exit": Block("exit", (), ()),
            },
            entry="init",
        )
        rep = run_bounded(cfg, [{"x": 0, "y": 1}])
        self.assertFalse(rep.truncated)
        # 具体枚举中 y - x 的最大差值必须 <= 抽象所证的常数 1
        worst = max(
            s["y"] - s["x"] for s in rep.in_stores["body"]
        )
        self.assertLessEqual(worst, 1)
        self.assertEqual(rep.diff_violations, [])


if __name__ == "__main__":
    unittest.main()
