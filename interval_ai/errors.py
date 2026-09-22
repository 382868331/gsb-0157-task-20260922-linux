"""错误语义（公开契约）。

所有由本库主动抛出的异常都继承 :class:`IntervalAIError`：

* :class:`ValidationError` -- 输入不满足本题库公开契约（非法常量、未知变量、
  超过上限等）。错误对象带 ``location``，可定位到具体块/语句/参数。
* :class:`BudgetExhaustedError` -- 算法搜索预算耗尽。它与"无法证明"
  （``AssertOutcome(verdict="unknown")``，不是异常）严格区分。
"""

from __future__ import annotations

from typing import Any


class IntervalAIError(Exception):
    """本库所有自定义异常的基类。"""


class ValidationError(IntervalAIError):
    """非法输入。

    :param message: 人类可读的错误说明。
    :param location: 可定位坐标，例如 ``block 'head'.stmt[1].const``。
    """

    def __init__(self, message: str, location: str | None = None) -> None:
        self.location = location
        if location:
            full = f"[{location}] {message}"
        else:
            full = message
        super().__init__(full)


class BudgetExhaustedError(IntervalAIError):
    """迭代预算耗尽（区别于证明无解）。

    区间域 + 本题规定的加宽策略在数学上必然终止；预算只是防御性安全阀。
    触发时携带当时的部分不变量，便于调用方诊断，但该部分结果**不是**
    已验证的不动点，禁止当作可靠结论使用。
    """

    def __init__(self, message: str, *, rounds: int, partial: Any = None) -> None:
        super().__init__(message)
        self.rounds = rounds
        self.partial = partial


def require_int(value: Any, location: str) -> int:
    """整数参数校验：拒绝 bool、NaN/Infinity、非整数浮点与非整数类型。

    ``bool`` 是 ``int`` 的子类，按契约必须显式拒绝。浮点统一拒绝
    （本题变量是数学整数，不存在浮点输入），其中 NaN/Infinity 给出专门文案。
    """
    if isinstance(value, bool):
        raise ValidationError(
            f"expected an integer parameter, got bool {value!r} (bool is not accepted)",
            location,
        )
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        if value != value:  # NaN
            raise ValidationError("numeric input must not be NaN", location)
        if value in (float("inf"), float("-inf")):
            raise ValidationError("numeric input must not be Infinity", location)
        raise ValidationError(
            f"expected an integer parameter, got non-integral float {value!r}",
            location,
        )
    raise ValidationError(
        f"expected an integer parameter, got {type(value).__name__} {value!r}",
        location,
    )
