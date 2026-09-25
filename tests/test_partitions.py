"""有限路径分区测试。

覆盖（对应题面四项要求）：

* 两分支分别设置不同区间后再判断 -> 普通 unknown、分区 proved（提升）；
* 循环内条件翻转 -> 标签只记最近一次真假，退出分区拿到最后一次结果；
* 不可达分支 -> 分区整支消失、断言空真；
* 强制合并 -> 按标签顺序、凸包守恒、只丢标签不删状态、事件给出位置。

另含：标签原语、输入校验、cap=1 与普通模式等价、独立检查器对分区结果
的符号复核（含三类篡改必须被抓）。证明一律来自符号端点包含；
:func:`run_bounded` 的具体枚举只作覆盖性反例对照，不参与证明。
"""

import unittest
from dataclasses import replace

from interval_ai import (
    AbstractState,
    AssertRange,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    Interval,
    Label,
    MergeEvent,
    PartitionedState,
    TRUE,
    FALSE,
    UNKNOWN,
    MAX_PARTITION_POINTS,
    DEFAULT_MAX_PARTITIONS,
    ValidationError,
    analyze,
    check_local_soundness,
    run_bounded,
)
from interval_ai.partitions import coarsen_members, fine_grid


# -- 确定性程序夹具 ------------------------------------------------------------


def correlation_program(looser_assert: bool = False) -> CFG:
    """x∈[0,10]; if(x<=3){y=0}else{y=10}; if(y>=5){assert x>=4 (或 x>=8)}.

    普通区间在 join 处把 (x,y) 关联丢掉：hot 块只能给 x∈[0,10]；
    分区记住第一条件真假后，hot（y>=5）只可能来自第一条件假支 x∈[4,10]。
    """
    bound = 8 if looser_assert else 4
    return CFG(
        variables=("x", "y"),
        blocks={
            "fork1": Block("fork1", (), ("then1", "else1"), Guard("x", "<=", 3)),
            "then1": Block("then1", (AssignConst("y", 0),), ("fork2",)),
            "else1": Block("else1", (AssignConst("y", 10),), ("fork2",)),
            "fork2": Block("fork2", (), ("hot", "skip"), Guard("y", ">=", 5)),
            "hot": Block("hot", (AssertRange("x", bound, None),), ()),
            "skip": Block("skip", (), ()),
        },
        entry="fork1",
        entry_bounds={"x": Interval(0, 10)},
    )


def loop_flip_program() -> CFG:
    """x=0; while(x<=4){ if(x>=3) flag=100 else flag=0; x++ }; assert flag==100.

    内条件随迭代翻转：x=0,1,2 为假，x=3,4 为真。退出循环来自最后一次
    迭代（x=4 为真），故 flag=100；标签必须可覆写才能推出。
    """
    return CFG(
        variables=("x", "flag"),
        blocks={
            "init": Block(
                "init", (AssignConst("x", 0), AssignConst("flag", 0)), ("head",)
            ),
            "head": Block("head", (), ("inner", "exit"), Guard("x", "<=", 4)),
            "inner": Block("inner", (), ("hi", "lo"), Guard("x", ">=", 3)),
            "hi": Block("hi", (AssignConst("flag", 100),), ("step",)),
            "lo": Block("lo", (AssignConst("flag", 0),), ("step",)),
            "step": Block("step", (AssignAdd("x", "x", 1),), ("head",)),
            "exit": Block("exit", (AssertRange("flag", 100, 100),), ()),
        },
        entry="init",
    )


def three_guard_tree() -> CFG:
    """三个串行独立守卫，全开区间入口；汇合块可达 2^3 中实际 4 个细标签。"""
    return CFG(
        variables=("x",),
        blocks={
            "g1": Block("g1", (), ("a1", "b1"), Guard("x", "<=", 1)),
            "a1": Block("a1", (), ("g2",)),
            "b1": Block("b1", (), ("g2",)),
            "g2": Block("g2", (), ("a2", "b2"), Guard("x", "<=", 2)),
            "a2": Block("a2", (), ("g3",)),
            "b2": Block("b2", (), ("g3",)),
            "g3": Block("g3", (), ("a3", "b3"), Guard("x", "<=", 3)),
            "a3": Block("a3", (), ("join",)),
            "b3": Block("b3", (), ("join",)),
            "join": Block("join", (), ()),
        },
        entry="g1",
        entry_bounds={"x": Interval(0, 10)},
    )


# -- 标签原语 ------------------------------------------------------------------


class TestLabelPrimitives(unittest.TestCase):
    def test_initial_and_update_overwrite(self) -> None:
        lab = Label.initial(2)
        self.assertEqual(lab.values, (UNKNOWN, UNKNOWN))
        lab = lab.update(0, TRUE)
        self.assertEqual(lab.values, (TRUE, UNKNOWN))
        # 最近一次覆写：TRUE -> FALSE，旧真假不固定
        lab = lab.update(0, FALSE)
        self.assertEqual(lab.values, (FALSE, UNKNOWN))
        lab = lab.update(1, TRUE)
        self.assertEqual(lab.values, (FALSE, TRUE))

    def test_frozen_slot_is_not_resplit(self) -> None:
        lab = Label((UNKNOWN, FALSE), frozenset({0}))
        again = lab.update(0, TRUE)  # 冻结槽不被经过条件重新分裂
        self.assertEqual(again, lab)
        # 未冻结槽照常覆写
        self.assertEqual(lab.update(1, TRUE).values, (UNKNOWN, TRUE))

    def test_generalize_conflict_freezes(self) -> None:
        a = Label((TRUE, TRUE), frozenset())
        b = Label((FALSE, TRUE), frozenset())
        g = a.generalize(b)
        self.assertEqual(g.values, (UNKNOWN, TRUE))
        self.assertEqual(g.frozen, frozenset({0}))

    def test_generalize_with_unknown_is_not_conflict(self) -> None:
        # 未经过(?) 与 T 汇合：语义是"一条路径已知 T、另一条未知"，
        # 按题面"未经过单独标 unknown"，汇合冲突槽抹 UNKNOWN 冻结（保守）。
        a = Label((TRUE,), frozenset())
        b = Label((UNKNOWN,), frozenset())
        g = a.generalize(b)
        self.assertEqual(g.values, (UNKNOWN,))
        self.assertEqual(g.frozen, frozenset({0}))

    def test_gamma_and_covers(self) -> None:
        self.assertEqual(len(fine_grid(3)), 27)
        coarse = Label((UNKNOWN, TRUE), frozenset({0}))
        gamma = coarse.fine_members()
        self.assertEqual(len(gamma), 3)  # 冻结槽 3 种，另一槽固定 T
        for values in ((UNKNOWN, TRUE), (FALSE, TRUE), (TRUE, TRUE)):
            self.assertIn(Label(values, frozenset()), gamma)
            self.assertTrue(coarse.covers_fine(Label(values, frozenset())))
        self.assertFalse(coarse.covers_fine(Label((TRUE, FALSE), frozenset())))

    def test_frozen_requires_unknown_value(self) -> None:
        with self.assertRaises(TypeError):
            Label((TRUE,), frozenset({0}))

    def test_order_key_total_order(self) -> None:
        labels = [Label((TRUE,)), Label((FALSE,)), Label((UNKNOWN,))]
        ordered = sorted(labels, key=lambda l: l.order_key)
        self.assertEqual([l.values[0] for l in ordered], [UNKNOWN, FALSE, TRUE])


# -- 提升：两支设不同区间再判断 ------------------------------------------------


class TestTwoBranchCorrelation(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = correlation_program()
        self.plain = analyze(self.cfg)
        self.part = analyze(self.cfg, track_guards=("fork1",))

    def test_plain_cannot_prove(self) -> None:
        # 普通凸包把关联丢掉：hot 块 x 回到 [0,10]，x>=4 证不出
        self.assertEqual(self.plain.block_in["hot"].get("x"), Interval(0, 10))
        self.assertEqual(self.plain.asserts[0].verdict, "unknown")

    def test_partitions_keep_branches_separate(self) -> None:
        groups = {l.text: s for l, s in self.part.reachable_partitions("fork2")}
        self.assertEqual(set(groups), {"T", "F"})
        self.assertEqual(groups["T"].get("x"), Interval(0, 3))
        self.assertEqual(groups["T"].get("y"), Interval(0, 0))
        self.assertEqual(groups["F"].get("x"), Interval(4, 10))
        self.assertEqual(groups["F"].get("y"), Interval(10, 10))

    def test_hot_only_reachable_from_false_partition(self) -> None:
        hot = self.part.reachable_partitions("hot")
        self.assertEqual(len(hot), 1)
        label, state = hot[0]
        self.assertEqual(label.values, (FALSE,))
        self.assertEqual(state.get("x"), Interval(4, 10))

    def test_assert_proved_per_partition(self) -> None:
        st = self.part.asserts[0]
        self.assertEqual(st.verdict, "proved")
        self.assertEqual(len(st.partitions), 1)
        self.assertEqual(st.partitions[0].label, "F")
        self.assertEqual(st.partitions[0].observed, Interval(4, 10))

    def test_independent_soundness(self) -> None:
        report = check_local_soundness(self.part)
        self.assertTrue(report.ok, report.violations)

    def test_stronger_assert_still_unknown_per_partition(self) -> None:
        # x>=8 在唯一可达分区 x∈[4,10] 内仍证不出：逐分区判定，不放宽
        cfg = correlation_program(looser_assert=True)
        res = analyze(cfg, track_guards=("fork1",))
        self.assertEqual(res.asserts[0].verdict, "unknown")
        self.assertTrue(check_local_soundness(res).ok)

    def test_concrete_reference_confirms_but_does_not_prove(self) -> None:
        # 具体枚举只确认 hot 块 x 确实为 4..10（覆盖性对照，不是证明手段）
        report = run_bounded(
            self.cfg, [{"x": x, "y": 0} for x in range(11)]
        )
        self.assertFalse(report.truncated)
        self.assertEqual(report.interval_observed("hot", "x"), (4, 10))
        self.assertEqual(report.assert_violations, [])


# -- 循环翻转 ------------------------------------------------------------------


class TestLoopFlippingCondition(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = loop_flip_program()
        self.plain = analyze(self.cfg)
        self.part = analyze(self.cfg, track_guards=("inner",))

    def test_plain_unknown(self) -> None:
        self.assertEqual(self.plain.block_in["exit"].get("flag"), Interval(0, 100))
        self.assertEqual(self.plain.asserts[0].verdict, "unknown")

    def test_label_overwritten_across_iterations(self) -> None:
        groups = {l.text: s for l, s in self.part.reachable_partitions("inner")}
        # 进入 inner 时标签是"上一轮"内条件的结果：
        # ?=首次 x=0；F=上轮为假（本轮 x=1,2,3——x=3 当轮才翻真）；
        # T=上轮为真（本轮 x=4）。
        self.assertEqual(groups["?"].get("x"), Interval(0, 0))
        self.assertEqual(groups["F"].get("x"), Interval(1, 3))
        self.assertEqual(groups["T"].get("x"), Interval(4, 4))
        # 条件判定后分支标签即时更新：假支 x∈[0,2]，真支 x∈[3,4]
        lo = {l.text: s for l, s in self.part.reachable_partitions("lo")}
        hi = {l.text: s for l, s in self.part.reachable_partitions("hi")}
        self.assertEqual(lo["F"].get("x"), Interval(0, 2))
        self.assertEqual(hi["T"].get("x"), Interval(3, 4))

    def test_exit_carries_last_outcome_not_first(self) -> None:
        ex = self.part.reachable_partitions("exit")
        self.assertEqual(len(ex), 1)
        label, state = ex[0]
        self.assertEqual(label.values, (TRUE,))  # 最后一次 x=4 为真
        self.assertEqual(state.get("flag"), Interval(100, 100))

    def test_assert_proved_and_sound(self) -> None:
        self.assertEqual(self.part.asserts[0].verdict, "proved")
        self.assertTrue(check_local_soundness(self.part).ok)

    def test_concrete_exit_flag_is_100(self) -> None:
        report = run_bounded(self.cfg, [{"x": 0, "flag": 0}])
        self.assertEqual(report.interval_observed("exit", "flag"), (100, 100))


# -- 不可达分支 ----------------------------------------------------------------


class TestPartitionedUnreachableBranch(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = CFG(
            variables=("x",),
            blocks={
                "init": Block("init", (AssignConst("x", 0),), ("fork",)),
                "fork": Block("fork", (), ("dead", "cont"), Guard("x", ">=", 5)),
                "dead": Block("dead", (AssertRange("x", 100, 200),), ()),
                "cont": Block("cont", (AssertRange("x", 0, 0),), ()),
            },
            entry="init",
        )
        self.res = analyze(self.cfg, track_guards=("fork",))

    def test_dead_partition_absent_not_bottom_label(self) -> None:
        self.assertEqual(self.res.reachable_partitions("dead"), [])
        self.assertTrue(self.res.partition_in["dead"].is_bottom)

    def test_live_partition_is_false(self) -> None:
        labels = [l.text for l, _ in self.res.reachable_partitions("cont")]
        self.assertEqual(labels, ["F"])

    def test_vacuous_assert(self) -> None:
        st = next(a for a in self.res.asserts if a.block == "dead")
        self.assertEqual(st.verdict, "proved")
        self.assertTrue(st.vacuous)
        self.assertEqual(st.partitions, ())

    def test_soundness(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


# -- 强制合并 ------------------------------------------------------------------


class TestForcedMerge(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = three_guard_tree()
        self.full = analyze(
            self.cfg, track_guards=("g1", "g2", "g3"), max_partitions=8
        )
        self.capped = analyze(
            self.cfg, track_guards=("g1", "g2", "g3"), max_partitions=3
        )

    def test_no_merge_under_cap(self) -> None:
        self.assertEqual(self.full.merges, ())
        join_labels = {l.text for l, _ in self.full.reachable_partitions("join")}
        # x∈[0,1]: T,T,T; x=2: F,T,T; x=3: F,F,T; x∈[4,10]: F,F,F
        self.assertEqual(join_labels, {"T.T.T", "F.T.T", "F.F.T", "F.F.F"})

    def test_merge_events_reported_with_location(self) -> None:
        self.assertGreaterEqual(len(self.capped.merges), 1)
        ev = self.capped.merges[0]
        self.assertEqual(ev.block, "join")
        self.assertGreaterEqual(ev.round, 1)
        self.assertLessEqual(ev.partitions_after, 3)
        self.assertIn("join", ev.location)
        # 按标签总序：被并的是最末两个（T.T.T 与 F.T.T 在首槽冲突）
        self.assertEqual(ev.surviving.text, "x.T.T")
        self.assertEqual(ev.frozen_slots, (0,))

    def test_cap_respected_everywhere(self) -> None:
        for name in self.cfg.blocks:
            self.assertLessEqual(
                len(self.capped.partition_in[name].members), 3, name
            )

    def test_hull_conserved_no_state_deleted(self) -> None:
        # 合并前后总凸包逐块相等：只丢标签、不删状态
        for name in self.cfg.blocks:
            self.assertEqual(
                self.capped.block_in[name], self.full.block_in[name], name
            )

    def test_frozen_partition_does_not_resplit(self) -> None:
        # 幸存标签首槽冻结：之后再经过 g1（本程序无回流，故直接查结果标签）
        for label, _ in self.capped.reachable_partitions("join"):
            for i in label.frozen:
                self.assertEqual(label.values[i], UNKNOWN)

    def test_soundness_after_merge(self) -> None:
        self.assertTrue(check_local_soundness(self.capped).ok)


class TestCapOneEquivalence(unittest.TestCase):
    """cap=1：所有路径信息被合并抹除，结论应与普通模式一致（不更弱）。"""

    def test_cap_one_matches_plain_on_loop_programs(self) -> None:
        from tests._programs import (
            bounded_count_program,
            two_backedges_program,
            unbounded_growth_program,
        )

        for make in (
            bounded_count_program,
            unbounded_growth_program,
            two_backedges_program,
            loop_flip_program,
        ):
            with self.subTest(program=make.__name__):
                cfg = make()
                plain = analyze(cfg)
                guards = tuple(n for n, b in cfg.blocks.items() if b.guard is not None)
                capped = analyze(cfg, track_guards=guards[:3], max_partitions=1)
                self.assertEqual(
                    [(a.block, a.index, a.verdict, a.vacuous) for a in plain.asserts],
                    [(a.block, a.index, a.verdict, a.vacuous) for a in capped.asserts],
                )
                for name in cfg.blocks:
                    self.assertEqual(plain.block_in[name], capped.block_in[name])
                self.assertTrue(check_local_soundness(capped).ok)


class TestCoarsenPrimitive(unittest.TestCase):
    def test_coarsen_hull_conserved_unit(self) -> None:
        variables = ("x",)
        members = {
            Label((TRUE,)): AbstractState(variables, {"x": Interval(0, 1)}),
            Label((FALSE,)): AbstractState(variables, {"x": Interval(9, 10)}),
        }
        work, groups, events = coarsen_members(members, 1, "b", 1)
        self.assertEqual(len(work), 1)
        surviving = next(iter(work))
        self.assertEqual(surviving.values, (UNKNOWN,))
        self.assertEqual(surviving.frozen, frozenset({0}))
        self.assertEqual(work[surviving].get("x"), Interval(0, 10))
        self.assertEqual(groups[surviving], [Label((FALSE,)), Label((TRUE,))])
        self.assertEqual(events[0].partitions_after, 1)


# -- 输入校验 ------------------------------------------------------------------


class TestPartitionValidation(unittest.TestCase):
    def _cfg(self) -> CFG:
        return CFG(
            variables=("x",),
            blocks={
                "g": Block("g", (), ("a", "b"), Guard("x", "<=", 1)),
                "a": Block("a", (), ()),
                "b": Block("b", (), ()),
            },
            entry="g",
        )

    def test_too_many_points(self) -> None:
        cfg = self._cfg()
        with self.assertRaises(ValidationError):
            analyze(cfg, track_guards=("g", "g", "g", "g"))
        # 常量与题面上限一致
        self.assertEqual(MAX_PARTITION_POINTS, 3)

    def test_duplicate_point(self) -> None:
        with self.assertRaises(ValidationError):
            analyze(self._cfg(), track_guards=("g", "g"))

    def test_missing_block(self) -> None:
        with self.assertRaises(ValidationError):
            analyze(self._cfg(), track_guards=("nope",))

    def test_point_without_guard(self) -> None:
        cfg = CFG(
            variables=("x",),
            blocks={"a": Block("a", (), ())},
            entry="a",
        )
        with self.assertRaises(ValidationError):
            analyze(cfg, track_guards=("a",))

    def test_bad_cap(self) -> None:
        cfg = self._cfg()
        with self.assertRaises(ValueError):
            analyze(cfg, track_guards=("g",), max_partitions=0)
        with self.assertRaises(TypeError):
            analyze(cfg, track_guards=("g",), max_partitions=True)  # type: ignore[arg-type]

    def test_bad_track_type(self) -> None:
        with self.assertRaises(TypeError):
            analyze(self._cfg(), track_guards="g")  # type: ignore[arg-type]

    def test_empty_points_is_plain(self) -> None:
        r1 = analyze(self._cfg())
        r2 = analyze(self._cfg(), track_guards=())
        self.assertFalse(r1.partitioned)
        self.assertFalse(r2.partitioned)

    def test_default_cap(self) -> None:
        self.assertGreaterEqual(DEFAULT_MAX_PARTITIONS, 2)


# -- 结果结构 ------------------------------------------------------------------


class TestPartitionResultStructure(unittest.TestCase):
    def setUp(self) -> None:
        self.res = analyze(correlation_program(), track_guards=("fork1",))

    def test_flags_and_metadata(self) -> None:
        self.assertTrue(self.res.partitioned)
        self.assertEqual(self.res.track_guards, ("fork1",))
        self.assertEqual(self.res.max_partitions, DEFAULT_MAX_PARTITIONS)
        self.assertIsInstance(self.res.merges, tuple)

    def test_to_dict_contains_partitions(self) -> None:
        data = self.res.to_dict()
        self.assertEqual(data["track_guards"], ["fork1"])
        self.assertIn("partitions", data)
        self.assertIn("hot", data["partitions"])
        self.assertIn("F", data["partitions"]["hot"]["in"])

    def test_partition_state_at(self) -> None:
        t_label = Label((TRUE,))
        self.assertEqual(
            self.res.partition_state_at("fork2", t_label).get("y"),
            Interval(0, 0),
        )
        self.assertIsNone(self.res.partition_state_at("hot", t_label))
        plain = analyze(correlation_program())
        with self.assertRaises(ValueError):
            plain.partition_state_at("hot", t_label)


# -- 独立检查器：篡改必须被抓 --------------------------------------------------


class TestPartitionCheckerAdversarial(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = correlation_program()
        self.res = analyze(self.cfg, track_guards=("fork1",))

    def test_tampered_partition_losing_state_is_caught(self) -> None:
        pin = dict(self.res.partition_in)
        ps = pin["hot"]
        label, state = next(iter(ps.members.items()))
        bad = PartitionedState(
            ps.variables, {label: state.assign("x", Interval(5, 10))}
        )  # 漏掉 x=4
        tampered = replace(self.res, partition_in={**pin, "hot": bad})
        report = check_local_soundness(tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("hot" in v for v in report.violations))

    def test_false_proved_is_caught(self) -> None:
        cfg = correlation_program(looser_assert=True)
        res = analyze(cfg, track_guards=("fork1",))
        self.assertEqual(res.asserts[0].verdict, "unknown")
        tampered = replace(
            res, asserts=[replace(res.asserts[0], verdict="proved")]
        )
        self.assertFalse(check_local_soundness(tampered).ok)

    def test_fake_merge_event_is_caught(self) -> None:
        fake = MergeEvent(
            block="hot",
            surviving=Label((TRUE,), frozenset()),
            dropped=(
                Label((FALSE,), frozenset()),
                Label((UNKNOWN,), frozenset()),
            ),
            partitions_after=1,
            round=1,
        )
        tampered = replace(
            self.res,
            merges=tuple(self.res.merges) + (fake,),
            max_partitions=1,
        )
        report = check_local_soundness(tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("merge" in v for v in report.violations))

    def test_cap_violation_is_caught(self) -> None:
        tampered = replace(self.res, max_partitions=1)
        # fork2 有两个可达分区，超过谎称的 cap=1
        report = check_local_soundness(tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("cap" in v for v in report.violations))

    def test_checker_independent_of_engine_modules(self) -> None:
        # 独立性回归：检查器不得 import engine/partitions/transfer
        import ast
        import pathlib

        src = (
            pathlib.Path(__file__).resolve().parents[1]
            / "interval_ai"
            / "checker.py"
        ).read_text(encoding="utf-8")
        imported = set()
        for node in ast.walk(ast.parse(src)):
            if isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module)
            if isinstance(node, ast.Import):
                imported.update(a.name for a in node.names)
        self.assertNotIn("interval_ai.engine", imported)
        self.assertNotIn("interval_ai.partitions", imported)
        self.assertNotIn("interval_ai.transfer", imported)


# -- 收窄在分区模式仍精确 ------------------------------------------------------


class TestPartitionedNarrowing(unittest.TestCase):
    def test_bounded_loop_exit_exact(self) -> None:
        from tests._programs import bounded_count_program

        cfg = bounded_count_program(4)
        res = analyze(cfg, track_guards=("head",))
        # 退出支标签为假；收窄后退出值精确为 [5,5]
        label, state = res.reachable_partitions("exit")[0]
        self.assertEqual(label.values, (FALSE,))
        self.assertEqual(state.get("i"), Interval(5, 5))
        self.assertTrue(res.narrowing_refined)
        self.assertTrue(check_local_soundness(res).ok)


class TestAssertIsConjunctionOverPartitions(unittest.TestCase):
    def _cfg(self, bound) -> CFG:
        # 两可达分区 T:y=0 / F:y=10 汇合后在 join 处断言 y>=bound
        return CFG(
            variables=("x", "y"),
            blocks={
                "fork": Block("fork", (), ("t", "e"), Guard("x", "<=", 3)),
                "t": Block("t", (AssignConst("y", 0),), ("join",)),
                "e": Block("e", (AssignConst("y", 10),), ("join",)),
                "join": Block("join", (AssertRange("y", bound, None),), ()),
            },
            entry="fork",
            entry_bounds={"x": Interval(0, 10)},
        )

    def test_one_bad_partition_makes_unknown(self) -> None:
        res = analyze(self._cfg(5), track_guards=("fork",))
        labels = {p.label: p.observed for p in res.asserts[0].partitions}
        self.assertEqual(set(labels), {"T", "F"})
        self.assertEqual(labels["T"], Interval(0, 0))   # y=0 不满足 y>=5
        self.assertEqual(labels["F"], Interval(10, 10))
        self.assertEqual(res.asserts[0].verdict, "unknown")
        self.assertTrue(check_local_soundness(res).ok)

    def test_all_good_partitions_proved(self) -> None:
        res = analyze(self._cfg(0), track_guards=("fork",))
        self.assertEqual(res.asserts[0].verdict, "proved")
        # 凸包观测 [0,10] 也满足 y>=0，但这里是逐分区都满足才 proved
        self.assertTrue(check_local_soundness(res).ok)


class TestWidenPointTamperCaught(unittest.TestCase):
    def test_shrunk_loop_head_partition_is_caught(self) -> None:
        from tests._programs import bounded_count_program

        cfg = bounded_count_program(4)
        res = analyze(cfg, track_guards=("head",))
        # 把 head 的 T 分区上界缩小，漏掉 body->head 回边的真实像
        pin = dict(res.partition_in)
        ps = pin["head"]
        bad_members = dict(ps.members)
        target = next(l for l in bad_members if l.values == (TRUE,))
        bad_members[target] = bad_members[target].assign("i", Interval(0, 2))
        tampered = replace(res, partition_in={**pin, "head": PartitionedState(ps.variables, bad_members)})
        report = check_local_soundness(tampered)
        self.assertFalse(report.ok)
        self.assertTrue(any("head" in v for v in report.violations))


if __name__ == "__main__":
    unittest.main()
