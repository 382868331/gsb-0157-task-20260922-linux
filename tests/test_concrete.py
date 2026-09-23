"""具体执行（独立参考）与抽象不变量的覆盖性对照。

``interval_ai.concrete`` 不导入被测核心（transfer/engine/checker），
这里的期望值来自具体语义枚举；本文件只做"具体可达值 ⊆ 抽象不变量"的
覆盖性检查，不反向用核心生成期望值。
"""

import unittest

from interval_ai import AssertRange, analyze, run_bounded
from interval_ai.intervals import Interval

from tests._programs import bounded_count_program, two_backedges_program


class TestConcreteCoverage(unittest.TestCase):
    def _assert_coverage(self, cfg, initial_stores) -> None:
        concrete = run_bounded(cfg, initial_stores)
        self.assertFalse(concrete.truncated, "参考枚举必须未截断才构成对照")
        result = analyze(cfg)

        # 1) 具体可达块 ⊆ 抽象非底块
        for name in cfg.blocks:
            abstract_bottom = result.block_in[name].bottom
            if name in concrete.reachable:
                self.assertFalse(
                    abstract_bottom, f"块 {name} 具体可达但抽象判为不可达"
                )

        # 2) 每个可达块上，每个变量的具体 min/max 落在抽象区间内
        for name in concrete.reachable:
            for var in cfg.variables:
                lo = concrete.var_min[name][var]
                hi = concrete.var_max[name][var]
                iv: Interval = result.block_in[name].get(var)
                self.assertTrue(
                    iv.contains_int(lo) and iv.contains_int(hi),
                    f"{name}.{var}: 具体[{lo},{hi}] 不被抽象 {iv.text} 覆盖",
                )

        # 3) 具体无断言违反；抽象标 proved 的断言具体也必成立
        self.assertEqual(concrete.assert_violations, [])
        proved = {(a.block, a.index) for a in result.asserts if a.verdict == "proved"}
        # 具体执行过的断言位置必须包含在 proved 中（非空真位置另计）
        for name in concrete.reachable:
            for i, st in enumerate(cfg.blocks[name].statements):
                if isinstance(st, AssertRange):
                    self.assertIn((name, i), proved)

    def test_bounded_count_family(self) -> None:
        # 确定性枚举多个有界上界，n=0 是退化零次循环
        for n in range(0, 8):
            with self.subTest(n=n):
                self._assert_coverage(bounded_count_program(n), [{"i": 0}])

    def test_two_backedges_one_concrete_choice(self) -> None:
        # j=0 固定走 +1 支：具体路径有限，抽象因 j 无界而更粗，仍须覆盖
        self._assert_coverage(two_backedges_program(), [{"i": 0, "j": 0}])

    def test_concrete_module_is_independent_of_core(self) -> None:
        import interval_ai.concrete as concrete_mod

        for banned in (
            "interval_ai.engine",
            "interval_ai.transfer",
            "interval_ai.checker",
            "interval_ai.relational",
            "interval_ai.diffs",
        ):
            self.assertNotIn(banned, concrete_mod.__dict__,
                             "具体参考不得直接依赖被测核心模块")


if __name__ == "__main__":
    unittest.main()
