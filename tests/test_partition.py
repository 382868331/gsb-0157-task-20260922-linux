"""有限路径分区模式测试。

覆盖题面要求的四类场景：
* 两分支分别设置不同区间后再判断（分区带来精度提升）；
* 循环内指定条件真/假翻转（标签被更新，不永久固定）；
* 不可达分支（无可达分区时断言空真）；
* 分区数超上限的强制合并（按标签序、不删状态、记录发生处）。

期望区间/标签均为手算后硬编码；独立有限执行（run_bounded）只用于
找反例，不作为证明依据。
"""

import unittest

from interval_ai import (
    DEFAULT_MAX_PARTITIONS,
    MAX_PARTITION_POINTS,
    Interval,
    ValidationError,
    analyze,
    check_local_soundness,
    run_bounded,
)

from tests._programs import (
    correlated_branches_program,
    loop_flip_program,
    merge_pressure_program,
    unreachable_branch_program,
)


def labels(result, block):
    return tuple(p.label for p in result.block_partitions_in[block])


class TestCorrelatedBranches(unittest.TestCase):
    """两分支分别设置不同区间后再判断：分区模式证明凸包模式证明不了的断言。"""

    def setUp(self) -> None:
        self.cfg = correlated_branches_program()
        self.plain = analyze(self.cfg)
        self.part = analyze(self.cfg, partition_points=("sw1",), max_partitions=4)

    def test_plain_hull_loses_correlation(self) -> None:
        # 凸包：x ∈ [1,2]，y 与分支的相关性丢失，两条断言都只能 unknown
        self.assertEqual(
            [a.verdict for a in self.plain.asserts], ["unknown", "unknown"]
        )

    def test_partitioned_proves_both_asserts(self) -> None:
        verdicts = {a.block: a for a in self.part.asserts}
        self.assertEqual(verdicts["t2"].verdict, "proved")
        self.assertEqual(verdicts["f2"].verdict, "proved")
        # 每个可达分区都单独被证明（proved 要求逐分区成立）
        self.assertEqual(verdicts["t2"].partition_verdicts, (("T", "proved"),))
        self.assertEqual(verdicts["f2"].partition_verdicts, (("F", "proved"),))

    def test_partition_labels_and_states(self) -> None:
        # sw1 之后：T 分区记住 y>=0，F 分区记住 y<=-1；未经过时标签为 "?"
        self.assertEqual(labels(self.part, "sw1"), (("?",),))
        self.assertEqual(labels(self.part, "sw2"), (("F",), ("T",)))
        t2 = self.part.block_partitions_in["t2"]
        self.assertEqual(len(t2), 1)
        self.assertEqual(t2[0].label, ("T",))
        self.assertEqual(t2[0].state.get("x"), Interval(1, 1))
        # 走错支的分区被守卫过滤成底：f2 只剩 F 分区
        self.assertEqual(labels(self.part, "f2"), (("F",),))

    def test_no_forced_merge_under_cap(self) -> None:
        self.assertEqual(self.part.merges, ())
        self.assertEqual(self.part.partition_points, ("sw1",))
        self.assertEqual(self.part.max_partitions, 4)

    def test_default_max_partitions(self) -> None:
        res = analyze(self.cfg, partition_points=("sw1",))
        self.assertEqual(res.max_partitions, DEFAULT_MAX_PARTITIONS)
        self.assertEqual([a.verdict for a in res.asserts], ["proved", "proved"])

    def test_independent_checker_passes(self) -> None:
        report = check_local_soundness(self.part)
        self.assertTrue(report.ok, report.violations)

    def test_concrete_execution_finds_no_counterexample(self) -> None:
        # 独立有限执行仅用于找反例；证明由上面的符号包含检查承担
        for y0 in (-3, 0, 7):
            concrete = run_bounded(self.cfg, [{"x": 0, "y": y0}])
            self.assertFalse(concrete.truncated)
            self.assertEqual(concrete.assert_violations, [])


class TestLoopFlip(unittest.TestCase):
    """循环再次经过指定条件时标签被更新：旧真/假不被永久固定。"""

    def setUp(self) -> None:
        self.cfg = loop_flip_program()
        self.res = analyze(self.cfg, partition_points=("sw",))

    def test_labels_cover_unknown_true_false(self) -> None:
        # 循环头同时存在：尚未经过 sw 的 "?"，以及最近结果为 F / T 的分区
        self.assertEqual(labels(self.res, "head"), (("?",), ("F",), ("T",)))

    def test_label_is_updated_not_stuck(self) -> None:
        # 若旧真/假被永久固定，循环内只可能出现其中一种标签；
        # 出口同时存在 F（x=0）与 T（x=1）分区说明标签每轮被重写
        self.assertEqual(labels(self.res, "exit"), (("F",), ("T",)))
        parts = {p.label: p.state for p in self.res.block_partitions_in["exit"]}
        self.assertEqual(parts[("F",)].get("x"), Interval(0, 0))
        self.assertEqual(parts[("T",)].get("x"), Interval(1, 1))

    def test_assert_proved_in_every_partition(self) -> None:
        st = self.res.asserts[0]
        self.assertEqual(st.verdict, "proved")
        self.assertEqual(
            st.partition_verdicts, (("F", "proved"), ("T", "proved"))
        )

    def test_widening_still_terminates(self) -> None:
        self.assertEqual(self.res.widen_points, ("head",))
        self.assertLessEqual(self.res.ascending_rounds, 20)
        self.assertLessEqual(self.res.narrowing_rounds, 8)

    def test_independent_checker_passes(self) -> None:
        report = check_local_soundness(self.res)
        self.assertTrue(report.ok, report.violations)

    def test_concrete_execution_finds_no_counterexample(self) -> None:
        concrete = run_bounded(self.cfg, [{"i": 0, "f": 0, "x": 0}])
        self.assertFalse(concrete.truncated)
        self.assertEqual(concrete.assert_violations, [])


class TestUnreachableBranchWithPartitioning(unittest.TestCase):
    """不可达分支：没有可达分区时断言空真 proved（vacuous）。"""

    def setUp(self) -> None:
        self.res = analyze(
            unreachable_branch_program(), partition_points=("fork",)
        )

    def test_dead_block_has_no_partition(self) -> None:
        self.assertEqual(self.res.block_partitions_in["dead"], ())
        self.assertTrue(self.res.block_in["dead"].bottom)

    def test_dead_assert_vacuously_proved(self) -> None:
        st = next(a for a in self.res.asserts if a.block == "dead")
        self.assertEqual(st.verdict, "proved")
        self.assertTrue(st.vacuous)
        self.assertEqual(st.partition_verdicts, ())

    def test_live_branch_carries_false_label(self) -> None:
        # x=0 使 fork 的 x>=5 为假：cont 只由 F 分区到达
        self.assertEqual(labels(self.res, "cont"), (("F",),))
        st = next(a for a in self.res.asserts if a.block == "cont")
        self.assertEqual(st.verdict, "proved")
        self.assertEqual(st.partition_verdicts, (("F", "proved"),))

    def test_independent_checker_passes(self) -> None:
        self.assertTrue(check_local_soundness(self.res).ok)


class TestForcedMerge(unittest.TestCase):
    """分区数超过显式上限：按标签序合并、丢失标签取凸包、不删状态、记录发生处。"""

    def setUp(self) -> None:
        self.cfg = merge_pressure_program()
        self.res = analyze(
            self.cfg,
            partition_points=("s1", "s2", "s3"),
            max_partitions=2,
        )

    def test_partition_count_never_exceeds_cap(self) -> None:
        for name in self.cfg.blocks:
            self.assertLessEqual(
                len(self.res.block_partitions_in[name]),
                2,
                f"block {name} exceeds cap",
            )

    def test_merge_events_report_location(self) -> None:
        self.assertTrue(self.res.merges, "expected forced merges to be recorded")
        for ev in self.res.merges:
            self.assertIn(ev.block, self.cfg.blocks)
            self.assertIn(ev.phase, ("ascending", "narrowing"))
            self.assertTrue(ev.merged_labels)
        # 8 种标签组合在 cap=2 下，合并首先发生在第三个条件位置之后
        self.assertTrue(any(ev.block == "s3" for ev in self.res.merges))

    def test_merged_partition_loses_label_but_keeps_states(self) -> None:
        end = {p.label: p.state for p in self.res.block_partitions_in["end"]}
        self.assertIn(None, end, "merged partition must exist (label lost)")
        merged = end[None]
        # 被合并的状态取凸包而不是删除：x/y/z 的 [1,1] 与 [2,2] 都在 [1,2] 内
        for v in ("x", "y", "z"):
            self.assertEqual(merged.get(v), Interval(1, 2))
        # 凸包视图 block_in 覆盖全部分区（不删状态的另一侧面）
        hull = self.res.block_in["end"]
        for p in self.res.block_partitions_in["end"]:
            self.assertTrue(p.state.subseteq(hull))

    def test_asserts_still_proved_after_merge(self) -> None:
        self.assertEqual(
            [a.verdict for a in self.res.asserts],
            ["proved", "proved", "proved"],
        )

    def test_cap_one_merges_everything(self) -> None:
        res = analyze(
            self.cfg,
            partition_points=("s1", "s2", "s3"),
            max_partitions=1,
        )
        self.assertTrue(res.merges)
        for name in self.cfg.blocks:
            self.assertLessEqual(len(res.block_partitions_in[name]), 1)
        end_labels = [p.label for p in res.block_partitions_in["end"]]
        self.assertEqual(end_labels, [None])
        self.assertTrue(check_local_soundness(res).ok)

    def test_independent_checker_passes(self) -> None:
        report = check_local_soundness(self.res)
        self.assertTrue(report.ok, report.violations)

    def test_concrete_execution_finds_no_counterexample(self) -> None:
        stores = [
            {"a": a, "b": b, "c": c, "x": 0, "y": 0, "z": 0}
            for a in (-1, 1)
            for b in (-1, 1)
            for c in (-1, 1)
        ]
        concrete = run_bounded(self.cfg, stores)
        self.assertFalse(concrete.truncated)
        self.assertEqual(concrete.assert_violations, [])


class TestPartitionValidation(unittest.TestCase):
    def setUp(self) -> None:
        self.cfg = correlated_branches_program()

    def _invalid(self, points, cap=4):
        with self.assertRaises(ValidationError):
            analyze(self.cfg, partition_points=points, max_partitions=cap)

    def test_too_many_partition_points(self) -> None:
        self.assertEqual(MAX_PARTITION_POINTS, 3)
        self._invalid(("sw1", "sw2", "t1", "f1"))

    def test_duplicate_partition_point(self) -> None:
        self._invalid(("sw1", "sw1"))

    def test_unknown_block(self) -> None:
        self._invalid(("nope",))

    def test_block_without_guard(self) -> None:
        self._invalid(("t1",))  # t1 只有一个后继、无守卫

    def test_partition_points_must_be_sequence_of_names(self) -> None:
        self._invalid("sw1")  # 字符串不是名字序列
        self._invalid((42,))

    def test_max_partitions_must_be_positive_int(self) -> None:
        self._invalid(("sw1",), cap=0)
        self._invalid(("sw1",), cap=True)  # bool 按契约拒绝
        self._invalid(("sw1",), cap="4")

    def test_error_is_locatable(self) -> None:
        try:
            analyze(self.cfg, partition_points=("sw1", "t1"))
        except ValidationError as exc:
            self.assertEqual(exc.location, "partition_points[1]")
        else:  # pragma: no cover
            self.fail("expected ValidationError")


class TestBackwardCompatibility(unittest.TestCase):
    """不指定分区位置时行为与旧版完全一致。"""

    def test_empty_partition_points_matches_plain(self) -> None:
        cfg = loop_flip_program()
        plain = analyze(cfg)
        compat = analyze(cfg, partition_points=())
        self.assertEqual(plain.block_in, compat.block_in)
        self.assertEqual(plain.block_out, compat.block_out)
        self.assertEqual(
            [a.verdict for a in plain.asserts],
            [a.verdict for a in compat.asserts],
        )
        self.assertEqual(compat.partition_points, ())
        self.assertEqual(compat.merges, ())
        self.assertEqual(compat.block_partitions_in, {})
        self.assertTrue(all(a.partition_verdicts == () for a in compat.asserts))


if __name__ == "__main__":
    unittest.main()
