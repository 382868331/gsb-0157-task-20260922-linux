"""独立具体执行参考（仅用于有界程序的覆盖性对照测试）。

本模块是与核心抽象解释**完全独立**的参考：它只把 ``cfg`` 的数据类
当作输入描述，不导入 interval/state/semantics/analyzer/checker，
期望集合由真正的整数状态在 CFG 上逐步执行得到，绝不调用被测核心。

终止性：具体状态是 ``(块名, 整数存储)``，用访问集合去重；对有界
程序（可达具体状态有限）必然终止。为防止误把无界程序喂进来导致
永久运行，设步数预算；耗尽抛 :class:`ConcreteBudgetExhausted`——
这是“参考执行跑不完”，与抽象结论 unknown 无关。
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .cfg import AddConst, AssertRange, Assign, Block, Cond, Copy, Jump, Program


class ConcreteBudgetExhausted(Exception):
    """具体执行步数预算耗尽（通常意味着程序在具体层面无界）。"""


@dataclass
class ConcreteTrace:
    """具体执行结果。"""

    reachable_blocks: set[str] = field(default_factory=set)
    reachable_edges: set[tuple[str, str]] = field(default_factory=set)
    # assert_id -> 该断言点观察到的 var 具体值集合，及是否出现违背
    assert_values: dict[str, set[int]] = field(default_factory=dict)
    assert_violations: dict[str, set[int]] = field(default_factory=dict)
    # 每个块入口观察到的 (变量索引 -> 具体值集合)，用于覆盖性对照
    entry_values: dict[str, dict[str, set[int]]] = field(default_factory=dict)
    steps: int = 0

    def is_violated(self, assert_id: str) -> bool:
        return bool(self.assert_violations.get(assert_id))


def execute(program: Program, *, max_steps: int = 1_000_000) -> ConcreteTrace:
    """对确定性初值的程序做具体可达状态枚举。

    入口存储：Program.entry_state 给定则用之，否则所有变量为 0。
    条件边在具体值下只有一个走向；同一 (块, 存储) 不重复展开。
    """
    variables = program.variables
    block_map = program.block_map
    if program.entry_state is None:
        init = tuple(0 for _ in variables)
    else:
        init = tuple(program.entry_state)

    trace = ConcreteTrace()
    # 工作列表元素：(块名, 块入口存储)
    pending: list[tuple[str, tuple[int, ...]]] = [(program.entry, init)]
    seen: set[tuple[str, tuple[int, ...]]] = set()

    while pending:
        name, store = pending.pop()
        key = (name, store)
        if key in seen:
            continue
        seen.add(key)
        trace.reachable_blocks.add(name)
        bucket = trace.entry_values.setdefault(
            name, {v: set() for v in variables}
        )
        for i, v in enumerate(variables):
            bucket[v].add(store[i])

        block: Block = block_map[name]
        cur = list(store)
        trace.steps += 1
        if trace.steps > max_steps:
            raise ConcreteBudgetExhausted(
                f"具体执行超过 {max_steps} 步仍有新状态；该程序在具体层面无界，"
                "不能用本参考做有限覆盖对照"
            )

        vi = {v: i for i, v in enumerate(variables)}
        for st in block.statements:
            if isinstance(st, Assign):
                cur[vi[st.var]] = st.value
            elif isinstance(st, Copy):
                cur[vi[st.var]] = cur[vi[st.src]]
            elif isinstance(st, AddConst):
                cur[vi[st.var]] += st.const
            elif isinstance(st, AssertRange):
                val = cur[vi[st.var]]
                trace.assert_values.setdefault(st.assert_id, set()).add(val)
                if not (st.lo <= val <= st.hi):
                    trace.assert_violations.setdefault(st.assert_id, set()).add(val)

        br = block.branch
        out = tuple(cur)
        if br is None:
            continue
        if isinstance(br, Jump):
            trace.reachable_edges.add((name, br.target))
            pending.append((br.target, out))
            continue
        assert isinstance(br, Cond)
        idx = variables.index(br.var)
        x = out[idx]
        cond = x <= br.const if br.op == "<=" else x >= br.const
        succ = br.taken if cond else br.skipped
        trace.reachable_edges.add((name, succ))
        pending.append((succ, out))

    return trace
