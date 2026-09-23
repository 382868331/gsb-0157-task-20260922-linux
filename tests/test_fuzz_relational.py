"""确定性小规模枚举对照：随机（固定种子）生成有界小程序，用独立具体执行器
枚举全部可达具体状态，核对关系分析结果的健全性。

期望值**只**来自 :mod:`interval_ai.concrete` 的具体整数枚举，绝不调用被测
核心生成期望；本文件核对的性质：

1. 具体可达的块，抽象不得判底；具体不可达不做反向要求（抽象允许更粗）。
2. 每个可达块入口，每个具体存储都满足抽象 DBM 的**每一条**界
   ``s_i - s_j <= M[i][j]``（零节点取 0），且具体 min/max 落在区间内。
3. 抽象判 proved 的（非空真）断言位置，具体枚举中零违反；
   具体枚举有违反的差分断言，抽象必须 unknown（不得误证）。
4. 独立符号检查器对每个结果通过。

生成的程序结构保证具体状态有限：变量初值为小常数，循环守卫 ``x <= LIMIT``，
循环体每轮 x 至少 +1，其余变量只做非负小增量；AssumeDiff 只会剪枝。
"""

import random
import unittest

from interval_ai import (
    AssertDiff,
    AssumeDiff,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    analyze,
    check_local_soundness,
    run_bounded,
)

LIMIT = 4
NAMES = ("x", "y", "z")
PAIRS = [
    ("x", None), ("y", None), ("z", None),
    ("x", "y"), ("y", "x"), ("x", "z"), ("z", "x"),
    ("y", "z"), ("z", "y"),
]


def _build_program(rng: random.Random):
    inits = tuple(rng.randint(0, 2) for _ in NAMES)
    incs = (rng.randint(1, 2), rng.randint(0, 2), rng.randint(0, 2))

    def rand_const() -> int:
        return rng.randint(-3, 3)

    def rand_assert() -> AssertDiff:
        l, r = rng.choice(PAIRS)
        return AssertDiff(l, r, rand_const())

    def rand_assume() -> AssumeDiff:
        l, r = rng.choice(PAIRS)
        return AssumeDiff(l, r, rand_const())

    body_stmts = []
    # 0~2 条假设（位置在增量之前，约束具体路径）
    for _ in range(rng.randint(0, 2)):
        body_stmts.append(rand_assume())
    # 0~2 条断言（增量前）
    for _ in range(rng.randint(0, 2)):
        body_stmts.append(rand_assert())
    for v, k in zip(NAMES, incs):
        if k:
            body_stmts.append(AssignAdd(v, v, k))

    head_stmts = [rand_assert() for _ in range(rng.randint(0, 2))]
    exit_stmts = [rand_assert() for _ in range(rng.randint(0, 3))]

    cfg = CFG(
        variables=NAMES,
        blocks={
            "init": Block(
                "init",
                tuple(AssignConst(v, c) for v, c in zip(NAMES, inits)),
                ("head",),
            ),
            "head": Block(
                "head", tuple(head_stmts), ("body", "exit"),
                Guard("x", "<=", LIMIT),
            ),
            "body": Block("body", tuple(body_stmts), ("head",)),
            "exit": Block("exit", tuple(exit_stmts), ()),
        },
        entry="init",
    )
    return cfg, inits


def _store_satisfies_dbm(store, diff_state, variables) -> bool:
    z = diff_state.zero
    vals = [store[v] for v in variables] + [0]
    i = 0
    n = len(variables) + 1
    while i < n:
        j = 0
        while j < n:
            bound = diff_state.matrix[i][j]
            if bound is not None and vals[i] - vals[j] > bound:
                return False
            j += 1
        i += 1
    return True


class TestEnumeratedConformance(unittest.TestCase):
    def test_seeded_programs_conform_to_concrete(self) -> None:
        for seed in range(60):
            with self.subTest(seed=seed):
                rng = random.Random(20260924 + seed)
                cfg, inits = _build_program(rng)
                store0 = dict(zip(NAMES, inits))
                concrete = run_bounded(cfg, [store0])
                self.assertFalse(
                    concrete.truncated,
                    f"seed {seed}: 具体枚举被截断，枚举对照失效",
                )
                result = analyze(cfg)
                report = check_local_soundness(result)
                self.assertTrue(report.ok, f"seed {seed}: {report.violations}")
                self.assertTrue(result.relational_converged)

                # 1) 可达性 + 2) 每条 DBM 界与区间端点
                for name in cfg.blocks:
                    stores = concrete.in_stores[name]
                    if not stores:
                        continue
                    self.assertFalse(
                        result.block_in[name].bottom,
                        f"seed {seed}: 块 {name} 具体可达却判底",
                    )
                    diff_in = result.block_in_diff[name]
                    self.assertFalse(diff_in.bottom)
                    for store in stores:
                        self.assertTrue(
                            _store_satisfies_dbm(store, diff_in, NAMES),
                            f"seed {seed}: 块 {name} 具体存储 {store} 违反 DBM "
                            f"{diff_in.text()}",
                        )
                    for v in NAMES:
                        iv = result.block_in[name].get(v)
                        lo = min(s[v] for s in stores)
                        hi = max(s[v] for s in stores)
                        self.assertTrue(
                            iv.contains_int(lo) and iv.contains_int(hi),
                            f"seed {seed}: {name}.{v} 具体[{lo},{hi}] "
                            f"超出抽象 {iv.text}",
                        )

                # 3) 断言：proved ⇒ 零违反；有违反 ⇒ 必 unknown
                violated = {
                    (b, i) for b, i, _ in concrete.diff_violations
                }
                for st in result.diff_asserts:
                    key = (st.block, st.index)
                    if key in violated:
                        self.assertEqual(
                            st.verdict, "unknown",
                            f"seed {seed}: {key} 具体有违反却标 {st.verdict}",
                        )
                    elif st.verdict == "proved" and not st.vacuous:
                        self.assertNotIn(key, violated)
                # 区间断言同理
                range_violated = {
                    (b, i) for b, i, _ in concrete.assert_violations
                }
                for st in result.asserts:
                    key = (st.block, st.index)
                    if key in range_violated:
                        self.assertEqual(st.verdict, "unknown")

    def test_enumeration_finds_real_diff_proofs(self) -> None:
        """健全性之外也要求"不总是 unknown"：至少一个种子里 DBM 证明了
        区间无法表达的纯差值断言（两个非常量变量之间的界）。"""
        found_pure_diff_proof = False
        for seed in range(60):
            rng = random.Random(20260924 + seed)
            cfg, _ = _build_program(rng)
            result = analyze(cfg)
            for st in result.diff_asserts:
                if (
                    st.verdict == "proved"
                    and not st.vacuous
                    and st.statement.right is not None
                ):
                    found_pure_diff_proof = True
        self.assertTrue(
            found_pure_diff_proof,
            "枚举的程序族中没有出现任何区间无法表达的纯差值证明，"
            "关系域可能没有真正参与",
        )


if __name__ == "__main__":
    unittest.main()
