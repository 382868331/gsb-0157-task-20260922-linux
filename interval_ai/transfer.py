"""局部抽象转移（语句 / 块尾守卫 / 整块）。

守卫的整数补集语义（变量取数学整数）：

* ``x <= c`` 为假 ⇔ ``x >= c + 1``
* ``x >= c`` 为假 ⇔ ``x <= c - 1``

:class:`~interval_ai.cfg.AssertRange` 是检查性语句，不改变抽象状态。
"""

from __future__ import annotations

from .cfg import (
    AssertDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
    Block,
    Guard,
    Statement,
)
from .intervals import AbstractState, Interval


def guard_interval(guard: Guard, taken: bool) -> Interval:
    """守卫在 taken（真支）/ not taken（假支）下对变量施加的单变量区间。"""
    c = guard.const
    if guard.op == "<=":
        return Interval(None, c) if taken else Interval(c + 1, None)
    # op == ">="
    return Interval(c, None) if taken else Interval(None, c - 1)


def transfer_statement(state: AbstractState, stmt: Statement) -> AbstractState:
    """单条语句的抽象转移。"""
    if state.bottom:
        return state
    if isinstance(stmt, AssignConst):
        return state.assign(stmt.target, Interval.singleton(stmt.const))
    if isinstance(stmt, AssignCopy):
        return state.assign(stmt.target, state.get(stmt.source))
    if isinstance(stmt, AssignAdd):
        return state.assign(stmt.target, state.get(stmt.source).add(stmt.const))
    if isinstance(stmt, (AssertRange, AssumeDiff, AssertDiff)):
        # 检查性语句不改变抽象状态；差分语句在纯区间视图下也只能跳过
        # （关系结论由积引擎负责；见 engine._analyze_with_relations）。
        return state
    raise TypeError(f"unsupported statement: {type(stmt).__name__}")  # pragma: no cover


def transfer_block(state: AbstractState, block: Block) -> AbstractState:
    """顺序执行块内全部语句（不含块尾守卫）。"""
    cur = state
    for stmt in block.statements:
        cur = transfer_statement(cur, stmt)
    return cur


def edge_state(state: AbstractState, block: Block, succ_index: int) -> AbstractState:
    """块出状态经过到第 ``succ_index`` 个后继的边守卫过滤后的状态。"""
    if state.bottom or block.guard is None:
        return state
    taken = succ_index == 0
    return state.restrict(block.guard.variable, guard_interval(block.guard, taken))
