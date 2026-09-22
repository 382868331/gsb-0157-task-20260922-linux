"""确定性的具体执行参考（独立于被测核心）。

本模块**不导入** :mod:`interval_ai.transfer` / :mod:`interval_ai.engine` /
:mod:`interval_ai.checker`：语句语义与守卫补集在此按数学整数重新实现一遍，
供测试把"小的有界程序"的具体可达值集合与抽象不变量做覆盖性对照。

注意：具体执行只对**有界**小程序（可达具体状态有限）完备；对无界循环它受
``max_visited_states`` 限制并在报告里置 ``truncated=True``，此时只能作为
补充，不能用来否证抽象结论。抽象结论的健全性由 :mod:`interval_ai.checker`
的符号包含检查承担，而不是靠采样。
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .cfg import CFG, AssertRange, AssignAdd, AssignConst, AssignCopy, Block

Store = dict[str, int]


class ConcreteBudget(Exception):
    """具体状态访问数超过预算（仅表示参考枚举被截断，不是分析结论）。"""


@dataclass
class ConcreteReport:
    reachable: set[str]
    in_stores: dict[str, list[Store]]
    var_min: dict[str, dict[str, int]]
    var_max: dict[str, dict[str, int]]
    assert_violations: list[tuple[str, int, Store]]
    truncated: bool = False

    def interval_observed(self, block: str, var: str) -> tuple[int, int] | None:
        vals = self.var_min.get(block)
        if not vals or var not in vals:
            return None
        return vals[var], self.var_max[block][var]


def _exec_statement(store: Store, stmt) -> Store:
    nxt = dict(store)
    if isinstance(stmt, AssignConst):
        nxt[stmt.target] = stmt.const
    elif isinstance(stmt, AssignCopy):
        nxt[stmt.target] = store[stmt.source]
    elif isinstance(stmt, AssignAdd):
        nxt[stmt.target] = store[stmt.source] + stmt.const
    elif isinstance(stmt, AssertRange):
        pass
    else:  # pragma: no cover - CFG 构造期保证
        raise TypeError(type(stmt).__name__)
    return nxt


def _guard_holds(store: Store, block: Block) -> bool:
    g = block.guard
    x = store[g.variable]
    return x <= g.const if g.op == "<=" else x >= g.const


def run_bounded(
    cfg: CFG,
    initial_stores: list[Store],
    *,
    max_visited_states: int = 200_000,
) -> ConcreteReport:
    """从若干具体初始存储出发做确定性的可达状态枚举。

    状态 = (块名, 各变量取值的元组)。循环回到完全相同的具体状态时剪枝。
    超过 ``max_visited_states`` 个不同状态时停止并置 ``truncated=True``。
    """
    for i, st0 in enumerate(initial_stores):
        if set(st0) != set(cfg.variables):
            raise ValueError(
                f"initial_stores[{i}] must define exactly the declared variables"
            )

    key_vars = tuple(cfg.variables)
    in_stores: dict[str, list[Store]] = {n: [] for n in cfg.blocks}
    seen: set[tuple[str, tuple[int, ...]]] = set()
    frontier: list[tuple[str, Store]] = []
    for st0 in initial_stores:
        key = (cfg.entry, tuple(st0[v] for v in key_vars))
        if key not in seen:
            seen.add(key)
            frontier.append((cfg.entry, dict(st0)))

    assert_violations: list[tuple[str, int, Store]] = []
    truncated = False

    while frontier:
        if len(seen) > max_visited_states:
            truncated = True
            break
        name, store = frontier.pop(0)  # FIFO，确定的 BFS 顺序
        in_stores[name].append(store)

        block = cfg.blocks[name]
        cur = store
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                x = cur[stmt.target]
                lo_ok = stmt.lower is None or x >= stmt.lower
                hi_ok = stmt.upper is None or x <= stmt.upper
                if not (lo_ok and hi_ok):
                    assert_violations.append((name, i, dict(cur)))
            cur = _exec_statement(cur, stmt)

        if not block.successors:
            continue
        if block.guard is None:
            chosen = [(block.successors[0], cur)]
        else:
            idx = 0 if _guard_holds(cur, block) else 1
            chosen = [(block.successors[idx], cur)]
        for succ, env in chosen:
            key = (succ, tuple(env[v] for v in key_vars))
            if key not in seen:
                seen.add(key)
                frontier.append((succ, env))

    var_min: dict[str, dict[str, int]] = {}
    var_max: dict[str, dict[str, int]] = {}
    reachable = {n for n, ss in in_stores.items() if ss}
    for n, ss in in_stores.items():
        if not ss:
            continue
        var_min[n] = {v: min(s[v] for s in ss) for v in key_vars}
        var_max[n] = {v: max(s[v] for s in ss) for v in key_vars}

    return ConcreteReport(
        reachable=reachable,
        in_stores=in_stores,
        var_min=var_min,
        var_max=var_max,
        assert_violations=assert_violations,
        truncated=truncated,
    )
