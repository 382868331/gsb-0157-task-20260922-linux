"""区间域：带无穷端点的数学整数区间。

端点用 Python 任意精度 int 表示有限值，无穷用 None 表示
（``lo=None`` 即 -∞，``hi=None`` 即 +∞）。不使用 float，因此没有 NaN、
舍入或误差问题。

格运算：

* 偏序 ``<=`` 为集合包含；
* join 为最小外包（凸包）``hull``；
* ``widen`` 为经典区间 widening：在上升链中端点一旦变化即推到无穷，
  有限端保持不动（保证有限步终止）；
* ``narrow`` 为经典区间 narrowing：只允许把无穷端点替换成新一轮迭代
  给出的有限界，有限端不动（单调下降，保证可靠）。
"""

from __future__ import annotations

from typing import Optional

from .errors import InvalidOperandError

# 端点：None 表示对应方向的无穷。
Bound = Optional[int]


def check_int(value: object, where: str) -> int:
    """把外部数值输入校验为有限数学整数。

    拒绝 bool（``True`` 不是本题意义上的整数 1）、float（含 NaN/Infinity
    及一切非整数值）、str 及其它非 int 类型。
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise InvalidOperandError(
            f"需要有限数学整数 int，得到 {type(value).__name__}: {value!r}",
            where=where,
        )
    return value


class Interval:
    """非空整数区间 ``[lo, hi]``；None 端点表示 ±∞。

    不变式：两端有限时 ``lo <= hi``。不可变、可哈希。不可达用
    ``None`` 状态表示，本类不表示空区间。
    """

    __slots__ = ("lo", "hi")

    def __init__(self, lo: Bound, hi: Bound) -> None:
        if isinstance(lo, bool) or isinstance(hi, bool):
            raise InvalidOperandError("端点不允许 bool", where="Interval")
        if lo is not None and not isinstance(lo, int):
            raise InvalidOperandError(
                f"下端点必须是 int 或 None，得到 {type(lo).__name__}",
                where="Interval",
            )
        if hi is not None and not isinstance(hi, int):
            raise InvalidOperandError(
                f"上端点必须是 int 或 None，得到 {type(hi).__name__}",
                where="Interval",
            )
        if lo is not None and hi is not None and lo > hi:
            raise InvalidOperandError(
                f"空区间 [{lo}, {hi}]：本域用 None 状态表示不可达，不表示空区间",
                where="Interval",
            )
        self.lo: Bound = lo
        self.hi: Bound = hi

    # ---- 构造 ----
    @staticmethod
    def top() -> "Interval":
        return Interval(None, None)

    @staticmethod
    def of(value: object) -> "Interval":
        """单值区间 [c, c]。"""
        c = check_int(value, where="Interval.of")
        return Interval(c, c)

    def is_top(self) -> bool:
        return self.lo is None and self.hi is None

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Interval):
            return NotImplemented
        return self.lo == other.lo and self.hi == other.hi

    def __hash__(self) -> int:
        return hash((self.lo, self.hi))

    def __repr__(self) -> str:
        l = "-inf" if self.lo is None else str(self.lo)
        h = "+inf" if self.hi is None else str(self.hi)
        return f"[{l}, {h}]"

    def to_dict(self) -> dict:
        """JSON 友好表示：无穷端点为 ``null``。"""
        return {"lo": self.lo, "hi": self.hi}

    # ---- 格运算 ----
    def __le__(self, other: "Interval") -> bool:
        """包含序：``self ⊆ other``。"""
        lo_ok = other.lo is None or (self.lo is not None and self.lo >= other.lo)
        hi_ok = other.hi is None or (self.hi is not None and self.hi <= other.hi)
        return lo_ok and hi_ok

    def subset_eq(self, other: "Interval") -> bool:
        """``self ⊆ other`` 的具名版本。"""
        return self <= other

    @staticmethod
    def hull(x: "Interval", y: "Interval") -> "Interval":
        """最小外包（凸包），即区间 join。"""
        lo = None if x.lo is None or y.lo is None else min(x.lo, y.lo)
        hi = None if x.hi is None or y.hi is None else max(x.hi, y.hi)
        return Interval(lo, hi)

    @staticmethod
    def widen(prev: "Interval", nxt: "Interval") -> "Interval":
        """经典区间 widening。

        端点在上升链中降低（下界）/升高（上界）时立即推到对应无穷；
        未变化的端点与有限端保持不动。要求 ``prev ⊆ nxt``（调用方
        保证），此时 ``prev ⊆ widen(prev, nxt)`` 成立。
        """
        if prev.lo is None:
            lo: Bound = None
        elif nxt.lo is None or nxt.lo < prev.lo:
            lo = None
        else:
            lo = prev.lo
        if prev.hi is None:
            hi: Bound = None
        elif nxt.hi is None or nxt.hi > prev.hi:
            hi = None
        else:
            hi = prev.hi
        return Interval(lo, hi)

    @staticmethod
    def narrow(prev: "Interval", nxt: "Interval") -> "Interval":
        """经典区间 narrowing。

        要求 ``nxt ⊆ prev``（调用方保证）。有限端点保持 prev 的值，
        无穷端点可以被 nxt 的有限界收回，结果仍满足
        ``nxt ⊆ narrow(prev, nxt) ⊆ prev``。
        """
        lo = nxt.lo if prev.lo is None else prev.lo
        hi = nxt.hi if prev.hi is None else prev.hi
        return Interval(lo, hi)

    # ---- 算术 / 条件（本题子集）----
    def add_const(self, c: int) -> "Interval":
        """``x + c``，c 为有限 int。"""
        check_int(c, where="Interval.add_const")
        lo = None if self.lo is None else self.lo + c
        hi = None if self.hi is None else self.hi + c
        return Interval(lo, hi)

    def meet(self, other: "Interval") -> Optional["Interval"]:
        """区间交；空交返回 ``None``（代表不可达）。"""
        if self.lo is None:
            lo: Bound = other.lo
        elif other.lo is None:
            lo = self.lo
        else:
            lo = max(self.lo, other.lo)
        if self.hi is None:
            hi: Bound = other.hi
        elif other.hi is None:
            hi = self.hi
        else:
            hi = min(self.hi, other.hi)
        if lo is not None and hi is not None and lo > hi:
            return None
        return Interval(lo, hi)

    def restrict_le(self, c: int) -> Optional["Interval"]:
        """与 ``(-∞, c]`` 相交；不可达返回 ``None``。"""
        check_int(c, where="Interval.restrict_le")
        if self.lo is not None and self.lo > c:
            return None
        hi = c if self.hi is None else min(self.hi, c)
        return Interval(self.lo, hi)

    def restrict_ge(self, c: int) -> Optional["Interval"]:
        """与 ``[c, +∞)`` 相交；不可达返回 ``None``。"""
        check_int(c, where="Interval.restrict_ge")
        if self.hi is not None and self.hi < c:
            return None
        lo = c if self.lo is None else max(self.lo, c)
        return Interval(lo, self.hi)

    def contains(self, value: object) -> bool:
        """具体整数 value 是否落在区间内。"""
        v = check_int(value, where="Interval.contains")
        return (self.lo is None or v >= self.lo) and (self.hi is None or v <= self.hi)
