"""错误语义（公开契约的一部分）。

异常层级::

    IntervalAIError                 所有本库错误的基类
      +-- ProgramStructureError     CFG 结构 / 命名引用非法
      +-- InvalidOperandError       常量不是有限数学整数，或整数参数传了 bool
      +-- DuplicateIdError           变量 / 块 / 断言 id 重复
      +-- LimitExceededError         超过 20 变量 / 40 块等接口上限
      +-- InconsistentGraphError     边引用不存在的块等
      +-- AnalyzerBudgetExhausted    迭代预算耗尽（不等于“证不出”）

分析结果中“无法证明断言”用状态字符串 ``"unknown"`` 表达，**不**抛异常；
抛异常只用于非法输入或预算耗尽，二者语义严格分开。
"""

from __future__ import annotations


class IntervalAIError(Exception):
    """本库抛出的所有错误的基类；``where`` 给出可定位的上下文。"""

    def __init__(self, message: str, *, where: str | None = None) -> None:
        self.where = where
        text = message if where is None else f"{where}: {message}"
        super().__init__(text)


class ProgramStructureError(IntervalAIError):
    """CFG 结构非法（空块列表、缺 entry、语句形状错等）。"""


class InvalidOperandError(IntervalAIError):
    """常量不是有限整数：float/NaN/Infinity/非整数，或整数参数传了 bool。"""


class DuplicateIdError(IntervalAIError):
    """变量名、块名或断言 id 重复。"""


class LimitExceededError(IntervalAIError):
    """超过契约规定的规模上限。"""


class InconsistentGraphError(IntervalAIError):
    """边引用了不存在的块，或 entry 不在块集合中。"""


class AnalyzerBudgetExhausted(IntervalAIError):
    """迭代预算在不动点达到之前耗尽。

    这与“断言无法证明（unknown）”完全不同：unknown 是合法的分析结论，
    本异常表示算法没能给出任何结论。
    """
