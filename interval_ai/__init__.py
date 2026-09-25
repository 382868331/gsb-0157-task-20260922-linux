"""整数循环的区间抽象解释（本题库，Python 3.14 标准库）。

公开接口：

数据结构
    :class:`CFG`, :class:`Block`, :class:`Guard`
    :class:`AssignConst`, :class:`AssignCopy`, :class:`AssignAdd`, :class:`AssertRange`
    :class:`Interval`, :class:`AbstractState`

分析
    :func:`analyze` -> :class:`AnalysisResult`（含 ``block_in`` / ``block_out`` /
    ``asserts``，每条断言为 ``proved`` 或 ``unknown``）

可选有限路径分区
    :func:`analyze(cfg, track_guards=(...), max_partitions=N)`；
    :class:`~interval_ai.partitions.Label`、
    :class:`~interval_ai.partitions.PartitionedState`、
    :class:`~interval_ai.partitions.MergeEvent`，
    常量 :data:`~interval_ai.partitions.MAX_PARTITION_POINTS` /
    ``TRUE`` / ``FALSE`` / ``UNKNOWN``；结果上的 ``partition_in/out``、
    ``merges``、``reachable_partitions``。

独立检查
    :func:`check_local_soundness`, :func:`check_transfer_step`,
    :func:`check_edge_guard`, :class:`ContainmentViolation`
    （分区结果同样由 ``check_local_soundness`` 在细标签网格上独立复核）

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
    DEFAULT_MAX_PARTITIONS,
    MAX_NARROWING_ROUNDS,
    AnalysisResult,
    AssertStatus,
    PartitionAssert,
    analyze,
)
from .errors import BudgetExhaustedError, IntervalAIError, ValidationError
from .intervals import AbstractState, Interval
from .concrete import ConcreteBudget, ConcreteReport, run_bounded
from .partitions import (
    FALSE,
    MAX_PARTITION_POINTS,
    TRUE,
    UNKNOWN,
    Label,
    MergeEvent,
    PartitionedState,
)
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
    "PartitionAssert",
    "MAX_NARROWING_ROUNDS",
    "DEFAULT_MAX_PARTITIONS",
    # finite path partitioning
    "Label",
    "PartitionedState",
    "MergeEvent",
    "MAX_PARTITION_POINTS",
    "TRUE",
    "FALSE",
    "UNKNOWN",
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
