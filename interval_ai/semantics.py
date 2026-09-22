"""局部抽象转移函数。

对每个 ``Block`` 给定入口 ``State``，顺序执行语句，再按出边条件给出
各后继的入口状态（条件过滤）。这些函数是纯函数，同时供：

* ``analyzer`` 做不动点迭代；
* ``checker`` 做独立的“局部转移包含性”检查（不重新实现语义，而是
  对状态空间做符号化界端点比较，见 checker 模块）。
"""

from __future__ import annotations

from typing import Optional

from .cfg import AddConst, AssertRange, Assign, Block, Cond, Copy, Jump, Program
from .interval import Interval
from .state import State


def apply_statement(state: State, stmt, program: Program) -> State:
    """单条语句的抽象转移。不可达状态保持不可达。"""
    if not state.reachable:
        return state
    vi = program.var_index
    if isinstance(stmt, Assign):
        i = vi[stmt.var]
        return state.with_value(i, Interval.of(stmt.value))
    if isinstance(stmt, Copy):
        i = vi[stmt.src]
        j = vi[stmt.var]
        src_iv = state.get(i, program)
        return state.with_value(j, src_iv)
    if isinstance(stmt, AddConst):
        i = vi[stmt.var]
        iv = state.get(i, program)
        return state.with_value(i, iv.add_const(stmt.const))
    if isinstance(stmt, AssertRange):
        # assert 不改变计算状态；它只在结果里被检验。
        return state
    raise TypeError(f"未知语句类型: {type(stmt).__name__}")  # pragma: no cover


def apply_block_body(state: State, block: Block, program: Program) -> State:
    """执行块内全部语句后的状态。"""
    cur = state
    for st in block.statements:
        cur = apply_statement(cur, st, program)
    return cur


def branch_outputs(
    state: State, block: Block, program: Program
) -> dict[str, State]:
    """块尾按出边分流。

    返回 ``{后继块名: 后继入口状态}``；被条件过滤为空的边映射到
    bottom（即不可达）。无条件跳转/无后继分别有 1/0 条边。
    """
    if not state.reachable:
        return {s: State.bottom(program) for s in block.successors}

    br = block.branch
    if br is None:
        return {}
    if isinstance(br, Jump):
        return {br.target: state}

    assert isinstance(br, Cond)
    i = program.var_index[br.var]
    iv = state.get(i, program)
    if br.op == "<=":
        true_iv = iv.restrict_le(br.const)
        false_iv = iv.restrict_ge(br.const + 1)
    else:  # ">="
        true_iv = iv.restrict_ge(br.const)
        false_iv = iv.restrict_le(br.const - 1)

    def replace(iv2: Optional[Interval]) -> State:
        vals = list(state._intervals)
        if iv2 is None:
            return State.bottom(program)
        vals[i] = iv2
        return State(tuple(vals))

    t_state = replace(true_iv)
    f_state = replace(false_iv)
    if br.taken == br.skipped:
        # 两边目标相同：该后继收到两个过滤结果的并
        return {br.taken: State.join(t_state, f_state)}
    return {br.taken: t_state, br.skipped: f_state}


def block_transfer(state: State, block: Block, program: Program) -> dict[str, State]:
    """完整块转移：入口状态 -> ``{后继名: 其后继入口状态}``。

    块“出口状态”（语句执行完、分支过滤前）可用
    :func:`apply_block_body` 单独得到。
    """
    out = apply_block_body(state, block, program)
    return branch_outputs(out, block, program)
