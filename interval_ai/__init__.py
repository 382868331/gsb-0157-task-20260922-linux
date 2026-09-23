"""整数循环的区间抽象解释 + 差分约束关系域（本题库，Python 3.14 标准库）。

公开接口：

数据结构
    :class:`CFG`, :class:`Block`, :class:`Guard`
    :class:`AssignConst`, :class:`AssignCopy`, :class:`AssignAdd`, :class:`AssertRange`
    :class:`AssumeDiff`, :class:`AssertDiff`（``x - y <= c`` 差分约束）
    :class:`Interval`, :class:`AbstractState`, :class:`DiffState`

分析
    :func:`analyze` -> :class:`AnalysisResult`（含 ``block_in`` / ``block_out`` /
    ``asserts``，每条断言为 ``proved`` 或 ``unknown``；含差分断言
    ``diff_asserts`` 与关系域收敛标记 ``relational_converged``）

独立检查
    :func:`check_local_soundness`, :func:`check_transfer_step`,
    :func:`check_edge_guard`, :class:`ContainmentViolation`

具体执行参考（仅测试/演示对照）
    :func:`interval_ai.concrete.run_bounded`
错误
    :class:`IntervalAIError`, :class:`ValidationError`,
    :class:`BudgetExhaustedError`
"""

from .cfg import (
    MAX_BLOCKS,
    MAX_DIFF_VARIABLES,
    MAX_VARIABLES,
    AssertRange,
    AssertDiff,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
    Block,
    CFG,
    Guard,
)
from .checker import (
    ContainmentViolation,
    check_edge_guard,
    check_local_soundness,
    check_transfer_step,
)
from .diffs import DiffState
from .engine import (
    DEFAULT_LOOP_BUDGET,
    MAX_NARROWING_ROUNDS,
    AnalysisResult,
    AssertStatus,
    DiffAssertStatus,
    analyze,
)
from .errors import BudgetExhaustedError, IntervalAIError, ValidationError
from .intervals import AbstractState, Interval
from .concrete import ConcreteBudget, ConcreteReport, run_bounded
from .transfer import edge_state, guard_interval, transfer_block, transfer_statement

__all__ = [
    # cfg
    "CFG",
    "Block",
    "Guard",
    "AssignConst",
    "AssignCopy",
    "AssignAdd",
    "AssertRange",
    "AssumeDiff",
    "AssertDiff",
    "MAX_VARIABLES",
    "MAX_BLOCKS",
    "MAX_DIFF_VARIABLES",
    # domain
    "Interval",
    "AbstractState",
    "DiffState",
    # engine
    "analyze",
    "AnalysisResult",
    "AssertStatus",
    "DiffAssertStatus",
    "MAX_NARROWING_ROUNDS",
    "DEFAULT_LOOP_BUDGET",
    # transfer
    "transfer_statement",
    "transfer_block",
    "edge_state",
    "guard_interval",
    # independent checker
    "check_local_soundness",
    "check_transfer_step",
    "check_edge_guard",
    "ContainmentViolation",
    # errors
    "IntervalAIError",
    "ValidationError",
    "BudgetExhaustedError",
    # concrete reference
    "run_bounded",
    "ConcreteReport",
    "ConcreteBudget",
]
