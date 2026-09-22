"""整数循环的区间抽象解释（本题库，Python 3.14 标准库）。

公开接口：

数据结构
    :class:`CFG`, :class:`Block`, :class:`Guard`
    :class:`AssignConst`, :class:`AssignCopy`, :class:`AssignAdd`, :class:`AssertRange`
    :class:`Interval`, :class:`AbstractState`

分析
    :func:`analyze` -> :class:`AnalysisResult`（含 ``block_in`` / ``block_out`` /
    ``asserts``，每条断言为 ``proved`` 或 ``unknown``）

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
    MAX_VARIABLES,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
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
from .engine import (
    MAX_NARROWING_ROUNDS,
    AnalysisResult,
    AssertStatus,
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
    "MAX_VARIABLES",
    "MAX_BLOCKS",
    # domain
    "Interval",
    "AbstractState",
    # engine
    "analyze",
    "AnalysisResult",
    "AssertStatus",
    "MAX_NARROWING_ROUNDS",
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
