"""分析器端到端测试：不动点、widening/narrowing、回边、结论。"""

import unittest

from interval_ai import (
    AnalyzerBudgetExhausted,
    analyze,
    check_analysis,
)
from interval_ai.interval import Interval

from tests.programs import (
    bounded_two_branch_program,
    copy_program,
    correlated_loop_program,
    entry_is_header_program,
    infinite_growth_program,
    negative_counter_program,
    nested_loop_program,
    two_back_edges_program,
    unreachable_branch_program,
)


def _iv(result, block, var, side="entry"):
    state = result.in_states[block] if side == "entry" else result.out_states[block]
    d = state.to_dict(result.program)
    return None if d is None else Interval(d[var]["lo"], d[var]["hi"])


class TestBoundedConcreteMatch(unittest.TestCase):
    """有界程序：抽象不变量必须覆盖独立具体执行的全部观察值。"""

    def setUp(self):
        self.prog = bounded_two_branch_program()
        self.res = analyze(self.prog)

    def test_statuses(self):
        self.assertEqual(self.res.status_of("a_x"), "proved")
        self.assertEqual(self.res.status_of("a_addy_x"), "proved")
        # y 的自增受 x 上的内层条件保护，非关系域无法证明其界
        self.assertEqual(self.res.status_of("a_y_exact"), "unknown")
        self.assertEqual(self.res.status_of("a_y_wide"), "unknown")

    def test_loop_header_shape(self):
        # widening 后 narrowing 恢复 x 的精确上界 6；y 无法被收窄
        self.assertEqual(_iv(self.res, "h", "x"), Interval(0, 6))
        self.assertEqual(_iv(self.res, "h", "y"), Interval(0, None))

    def test_independent_certificate(self):
        report = check_analysis(self.prog, self.res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])

    def test_abstract_covers_concrete(self):
        # 独立具体执行（不调用核心）逐值对照覆盖性
        from interval_ai import execute_concrete

        trace = execute_concrete(self.prog)
        for block_name, bucket in trace.entry_values.items():
            for var, values in bucket.items():
                iv = _iv(self.res, block_name, var)
                for v in values:
                    self.assertTrue(
                        iv.contains(v),
                        f"{block_name}:{var} 具体值 {v} 不在抽象区间 {iv}",
                    )
        self.assertFalse(trace.is_violated("a_x"))
        self.assertFalse(trace.is_violated("a_y_exact"))
        # 具体上 y 恰好为 3（虽抽象证不出）
        self.assertEqual(trace.entry_values["done"]["y"], {3})

    def test_widen_started_on_third_expansion(self):
        self.assertEqual(self.res.widen_expansions["h"], 3)
        self.assertGreaterEqual(self.res.narrowing_rounds, 1)


class TestInfiniteGrowth(unittest.TestCase):
    def setUp(self):
        self.prog = infinite_growth_program()
        self.res = analyze(self.prog)

    def test_unbounded_interval(self):
        self.assertEqual(_iv(self.res, "h", "i"), Interval(0, None))

    def test_exit_unreachable(self):
        self.assertFalse(self.res.in_states["end"].reachable)
        a = next(a for a in self.res.assertions if a.assert_id == "a_dead")
        self.assertEqual(a.status, "proved")  # 不可达：空真
        self.assertFalse(a.reachable)

    def test_narrowing_cannot_shrink_unbounded(self):
        # 无界程序 narrowing 后仍为 [0,+inf)，且证书成立
        report = check_analysis(self.prog, self.res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])


class TestCorrelatedNarrowingImprovement(unittest.TestCase):
    """收窄改善：x 上界经 narrowing 从 +inf 收回 11，从而证明 x==11。"""

    def setUp(self):
        self.prog = correlated_loop_program()
        self.res = analyze(self.prog)

    def test_narrowing_proves_x(self):
        self.assertEqual(self.res.status_of("a_x"), "proved")
        self.assertEqual(_iv(self.res, "done", "x"), Interval(11, 11))

    def test_relation_lost_for_y(self):
        # 非关系域无法把 x 的界传播给同步增长的 y：
        # x==11 可证（narrowing 恢复），y 连有限上界都没有，全部 unknown。
        self.assertEqual(self.res.status_of("a_y_exact"), "unknown")
        self.assertEqual(self.res.status_of("a_y_wide"), "unknown")
        self.assertEqual(_iv(self.res, "done", "y"), Interval(0, None))

    def test_narrowing_actually_changed_invariants(self):
        # 若没有 narrowing，done:x 会是 [11,+inf)；这里必须已收紧
        self.assertLessEqual(self.res.narrowing_rounds, 8)
        self.assertEqual(_iv(self.res, "h", "x"), Interval(0, 11))

    def test_certificate(self):
        report = check_analysis(self.prog, self.res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])


class TestTwoBackEdges(unittest.TestCase):
    def setUp(self):
        self.prog = two_back_edges_program()
        self.res = analyze(self.prog)

    def test_two_back_edges_detected(self):
        back = set(self.res.back_edges)
        self.assertEqual(back, {("small", "h"), ("big", "h")})
        self.assertEqual(self.res.loop_headers, ("h",))

    def test_exit_range(self):
        self.assertEqual(self.res.status_of("a_exit"), "proved")
        # 抽象过近似 [11,12]：11 来自路径形状，实际确定性执行只到 12
        self.assertEqual(_iv(self.res, "end", "i"), Interval(11, 12))

    def test_concrete_values_covered(self):
        from interval_ai import execute_concrete

        trace = execute_concrete(self.prog)
        end_vals = trace.entry_values["end"]["i"]
        self.assertEqual(end_vals, {12})  # 独立参考：唯一具体出口值
        iv = _iv(self.res, "end", "i")
        self.assertTrue(all(iv.contains(v) for v in end_vals))

    def test_certificate(self):
        report = check_analysis(self.prog, self.res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])


class TestUnreachableBranch(unittest.TestCase):
    def setUp(self):
        self.prog = unreachable_branch_program()
        self.res = analyze(self.prog)

    def test_dead_block_bottom(self):
        self.assertFalse(self.res.in_states["dead"].reachable)
        self.assertEqual(self.res.status_of("a_dead"), "proved")
        self.assertEqual(self.res.status_of("a_live"), "proved")

    def test_edge_filtered(self):
        self.assertFalse(self.res.edge_states[("entry", "dead")].reachable)
        self.assertTrue(self.res.edge_states[("entry", "live")].reachable)

    def test_certificate(self):
        report = check_analysis(self.prog, self.res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])


class TestCopy(unittest.TestCase):
    def test_copy_propagates_interval(self):
        prog = copy_program()
        res = analyze(prog)
        self.assertEqual(res.status_of("a_b"), "proved")
        self.assertEqual(_iv(res, "entry", "b", side="exit"), Interval(10, 10))


class TestExtraLoopShapes(unittest.TestCase):
    def test_nested_loop_localized_widening(self):
        prog = nested_loop_program()
        res = analyze(prog)
        self.assertEqual(res.status_of("a_i"), "proved")
        self.assertEqual(_iv(res, "done", "i"), Interval(3, 3))
        report = check_analysis(prog, res)
        self.assertTrue(report.holds, [i.detail for i in report.failures()])
        # 内层头 hj 的 widening 掩码只应含 j，不含外层变量 i
        from interval_ai.analyzer import Analyzer as _A

        masks = _A(prog).header_masks
        vi = prog.var_index
        self.assertFalse(masks["hj"][vi["i"]])
        self.assertTrue(masks["hj"][vi["j"]])

    def test_negative_counter_lower_bound(self):
        prog = negative_counter_program()
        res = analyze(prog)
        self.assertEqual(_iv(res, "d", "i"), Interval(-6, -6))
        self.assertEqual(res.status_of("a_i"), "proved")
        self.assertTrue(check_analysis(prog, res).holds)

    def test_entry_block_is_header(self):
        prog = entry_is_header_program()
        res = analyze(prog)
        self.assertEqual(res.loop_headers, ("h",))
        self.assertEqual(_iv(res, "d", "i"), Interval(4, 4))
        self.assertEqual(res.status_of("a_i"), "proved")
        self.assertTrue(check_analysis(prog, res).holds)

    def test_zero_narrowing_is_sound_but_imprecise(self):
        # 关闭收窄：结论退化为 unknown，但证书仍必须成立
        prog = negative_counter_program()
        res = analyze(prog, max_narrowing=0)
        self.assertEqual(res.status_of("a_i"), "unknown")
        self.assertTrue(check_analysis(prog, res).holds)


class TestFixpointProtocol(unittest.TestCase):
    def test_narrowing_capped_at_8(self):
        prog = correlated_loop_program()
        res = analyze(prog)
        self.assertLessEqual(res.narrowing_rounds, 8)

    def test_budget_exhaustion_distinct_from_unknown(self):
        # max_rounds=1：上升阶段不可能稳定，必须抛“预算耗尽”而非给 unknown
        prog = two_back_edges_program()
        with self.assertRaises(AnalyzerBudgetExhausted):
            analyze(prog, max_rounds=1)

    def test_stable_is_post_fixpoint(self):
        # 对每个块：入边凸包 ⊆ 块入不变量（结果自身即后置不动点）
        prog = bounded_two_branch_program()
        res = analyze(prog)
        from interval_ai import State

        for block in prog.blocks:
            contribs = []
            if block.name == prog.entry:
                contribs.append(State.entry_state(prog))
            for p in prog.blocks:
                if (p.name, block.name) in res.edge_states:
                    contribs.append(res.edge_states[(p.name, block.name)])
            if not contribs:
                continue
            join = contribs[0]
            for c in contribs[1:]:
                join = State.join(join, c)
            self.assertTrue(
                join <= res.in_states[block.name],
                f"{block.name} 不是后置不动点",
            )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
