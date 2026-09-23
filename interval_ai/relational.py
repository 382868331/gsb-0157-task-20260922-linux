"""区间域 × 差分约束域的简约积（reduced product）。

每个程序点同时持有：

* :class:`~interval_ai.intervals.AbstractState` —— 逐变量区间（含不可达底）；
* :class:`~interval_ai.diffs.DiffState` —— 闭包后的 DBM（含不可满足底）。

两个域在**每一步之后交换信息**（Granger 式简约，单轮即对本语言完备，因为
两域共享同一组 x-z / z-x 约束）：

1. 语句/守卫先用各自最强后条件处理；
2. 把新区间端点并入 DBM 重新闭包（区间 -> 差分）；
3. 把 DBM 推出的每个变量端点回写区间（差分 -> 区间）。

于是区间单独表达不了的差值关系（如 ``y = x`` 之后 ``x - y <= 0``、
分支合流后仍保持的 ``x - y <= c``）可以由 DBM 表达；DBM 不精确时区间
照常工作。任一侧变底，整个积状态变底（不可达）。
"""

from __future__ import annotations

from dataclasses import dataclass

from .cfg import (
    AssertDiff,
    AssumeDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    Block,
    Guard,
    Statement,
)
from .diffs import DiffState
from .intervals import AbstractState, Interval
from .transfer import guard_interval


@dataclass(frozen=True, slots=True)
class ProductState:
    """简约积状态；任一域判底则整体为底。"""

    intervals: AbstractState
    diffs: DiffState

    @classmethod
    def bottom_of(cls, variables: tuple[str, ...]) -> "ProductState":
        return cls(
            AbstractState.bottom_of(variables), DiffState.bottom_of(variables)
        )

    @classmethod
    def initial(cls, cfg) -> "ProductState":
        variables = cfg.variable_tuple
        iv = AbstractState(variables, cfg.initial_state_intervals(), False)
        d = DiffState.from_intervals(variables, cfg.initial_state_intervals())
        return ProductState(iv, d)

    @property
    def bottom(self) -> bool:
        return self.intervals.bottom or self.diffs.bottom

    # -- 域间简约 ------------------------------------------------------------

    def _reduce(self) -> "ProductState":
        """区间 -> DBM 闭包 -> 区间，双向交换一次。"""
        if self.bottom:
            return ProductState.bottom_of(self.intervals.variables)
        refined = self.diffs.refine_with_intervals(self.intervals.bounds)
        if refined is None:
            return ProductState.bottom_of(self.intervals.variables)
        bounds = dict(self.intervals.bounds)
        for v in self.intervals.variables:
            bounds[v] = refined.interval_of(v)
        return ProductState(
            AbstractState(self.intervals.variables, bounds, False), refined
        )

    # -- 格运算 --------------------------------------------------------------

    def join(self, other: "ProductState") -> "ProductState":
        if self.bottom:
            return other
        if other.bottom:
            return self
        joined = ProductState(
            self.intervals.join(other.intervals),
            self.diffs.join(other.diffs),
        )
        return joined._reduce()

    def widen_selective(
        self, other: "ProductState", modified: set[str]
    ) -> "ProductState":
        if self.bottom:
            return other
        if other.bottom:
            return self
        wide = ProductState(
            self.intervals.widen_selective(other.intervals, modified),
            self.diffs.widen_selective(other.diffs, modified),
        )
        return wide._reduce()

    def narrow_selective(
        self, other: "ProductState", modified: set[str]
    ) -> "ProductState":
        if self.bottom:
            return self
        if other.bottom:
            return self
        narrow = ProductState(
            self.intervals.narrow_selective(other.intervals, modified),
            self.diffs.narrow_selective(other.diffs, modified),
        )
        return narrow._reduce()

    def subseteq(self, other: "ProductState") -> bool:
        if self.bottom:
            return True
        if other.bottom:
            return False
        # 简约后两域信息一致；同时检查两侧以保证稳健。
        return self.intervals.subseteq(other.intervals) and self.diffs.subseteq(
            other.diffs
        )

    # -- 守卫过滤 ------------------------------------------------------------

    def restrict_guard(self, guard: Guard, taken: bool) -> "ProductState":
        """块尾守卫在真/假支上的过滤，两域同时收窄并交换信息。

        守卫只有单边形式：``x <= c`` 真支（或 ``x >= c`` 假支）施加 x <= c；
        ``x >= c`` 真支（或 ``x <= c`` 假支）施加 x >= c。
        """
        if self.bottom:
            return self
        iv = guard_interval(guard, taken)
        new_iv = self.intervals.restrict(guard.variable, iv)
        if new_iv.bottom:
            return ProductState.bottom_of(self.intervals.variables)
        is_upper = (guard.op == "<=") == taken
        if is_upper:
            new_diff = self.diffs.assume(guard.variable, None, iv.upper)
        else:
            new_diff = self.diffs.assume_lower(guard.variable, iv.lower)
        if new_diff.bottom:
            return ProductState.bottom_of(self.intervals.variables)
        return ProductState(new_iv, new_diff)._reduce()

    # -- 展示 ----------------------------------------------------------------

    @property
    def text(self) -> str:
        if self.bottom:
            return "bottom (unreachable)"
        return f"{self.intervals.text} | diff: {self.diffs.text()}"


def transfer_statement_rel(state: ProductState, stmt: Statement) -> ProductState:
    """简约积上的单语句最强后条件。"""
    if state.bottom:
        return state
    iv, d = state.intervals, state.diffs
    if isinstance(stmt, AssignConst):
        new_iv = iv.assign(stmt.target, Interval.singleton(stmt.const))
        new_d = d.assign_const(stmt.target, stmt.const)
        return ProductState(new_iv, new_d)._reduce()
    if isinstance(stmt, AssignCopy):
        new_iv = iv.assign(stmt.target, iv.get(stmt.source))
        new_d = d.assign_copy(stmt.target, stmt.source)
        return ProductState(new_iv, new_d)._reduce()
    if isinstance(stmt, AssignAdd):
        new_iv = iv.assign(stmt.target, iv.get(stmt.source).add(stmt.const))
        new_d = d.assign_add(stmt.target, stmt.source, stmt.const)
        return ProductState(new_iv, new_d)._reduce()
    if isinstance(stmt, AssertRange):
        return state  # 检查性语句不改变状态
    if isinstance(stmt, AssumeDiff):
        new_d = d.assume(stmt.left, stmt.right, stmt.const)
        if new_d.bottom:
            return ProductState.bottom_of(iv.variables)
        return ProductState(iv, new_d)._reduce()
    if isinstance(stmt, AssertDiff):
        return state  # 断言不改变状态
    raise TypeError(
        f"unsupported statement: {type(stmt).__name__}"
    )  # pragma: no cover


def transfer_block_rel(state: ProductState, block: Block) -> ProductState:
    cur = state
    for stmt in block.statements:
        cur = transfer_statement_rel(cur, stmt)
    return cur


def edge_state_rel(state: ProductState, block: Block, succ_index: int) -> ProductState:
    """块出状态经过第 ``succ_index`` 条守卫边后的积状态。"""
    if state.bottom or block.guard is None:
        return state
    return state.restrict_guard(block.guard, succ_index == 0)
