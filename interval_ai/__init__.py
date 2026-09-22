"""整数循环的区间抽象解释（interval abstract interpretation）。

公开接口：

* CFG：:class:`Program`, :class:`Block`, :class:`Assign`, :class:`Copy`,
  :class:`AddConst`, :class:`AssertRange`, :class:`Cond`, :class:`Jump`；
* 域与状态：:class:`Interval`, :class:`State`；
* 分析：:func:`analyze`, :class:`Analyzer`, :class:`AnalysisResult`,
  :class:`AssertResult`；
* 独立证书检查器：:func:`check_analysis`, :func:`check_block_transfer`,
  :class:`CheckReport`；
* 独立具体执行参考：:func:`execute_concrete`（测试/对照用）。
"""

from __future__ import annotations

from .cfg import (
    MAX_BLOCKS,
    MAX_VARIABLES,
    AddConst,
    AssertRange,
    Block,
    Cond,
    Jump,
    Program,
    Assign,
    Copy,
)
from .interval import Interval
from .state import State
from .semantics import (
    apply_block_body,
    apply_statement,
    block_transfer,
    branch_outputs,
)
from .analyzer import (
    DEFAULT_MAX_NARROWING,
    DEFAULT_MAX_ROUNDS,
    AnalysisResult,
    Analyzer,
    AssertResult,
    analyze,
)
from .checker import (
    CheckItem,
    CheckReport,
    CheckViolation,
    check_analysis,
    check_block_transfer,
)
from .reference import ConcreteBudgetExhausted, ConcreteTrace, execute as execute_concrete
from .errors import (
    AnalyzerBudgetExhausted,
    DuplicateIdError,
    InconsistentGraphError,
    IntervalAIError,
    InvalidOperandError,
    LimitExceededError,
    ProgramStructureError,
)

__all__ = [
    # cfg
    "Program",
    "Block",
    "Assign",
    "Copy",
    "AddConst",
    "AssertRange",
    "Cond",
    "Jump",
    "MAX_VARIABLES",
    "MAX_BLOCKS",
    # domain
    "Interval",
    "State",
    # semantics
    "apply_statement",
    "apply_block_body",
    "branch_outputs",
    "block_transfer",
    # analyzer
    "analyze",
    "Analyzer",
    "AnalysisResult",
    "AssertResult",
    "DEFAULT_MAX_ROUNDS",
    "DEFAULT_MAX_NARROWING",
    # checker
    "check_analysis",
    "check_block_transfer",
    "CheckReport",
    "CheckItem",
    "CheckViolation",
    # concrete reference
    "execute_concrete",
    "ConcreteTrace",
    "ConcreteBudgetExhausted",
    # errors
    "IntervalAIError",
    "ProgramStructureError",
    "InvalidOperandError",
    "DuplicateIdError",
    "LimitExceededError",
    "InconsistentGraphError",
    "AnalyzerBudgetExhausted",
]
