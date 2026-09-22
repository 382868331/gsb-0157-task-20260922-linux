"""整数区间域与逐变量抽象状态。

端点约定：``None`` 表示无穷端点（``lower=None`` 即 -∞，``upper=None`` 即 +∞）。
所有有限端点必须是 Python ``int``（构造时拒绝 ``bool``）。

空集不在 :class:`Interval` 内表示，而是由
:class:`AbstractState` 的 ``bottom`` 标志统一表示（状态底 = 不可达）。
:meth:`Interval.intersect` 在不相交时返回 ``None``。
"""

from __future__ import annotations

from dataclasses import dataclass

from .errors import ValidationError, require_int


# -- 端点偏序：None 代表相应方向的无穷 ---------------------------------------

def _low_less(a: int | None, b: int | None) -> bool:
    """a < b，下端点语义（None = -∞）。"""
    if a is None:
        return b is not None
    if b is None:
        return False
    return a < b


def _low_leq(a: int | None, b: int | None) -> bool:
    if a is None:
        return True  # -∞ <= 一切
    if b is None:
        return False
    return a <= b


def _high_leq(a: int | None, b: int | None) -> bool:
    if b is None:
        return True  # 一切 <= +∞
    if a is None:
        return False
    return a <= b


def _low_min(a: int | None, b: int | None) -> int | None:
    if a is None or b is None:
        return None
    return min(a, b)


def _high_max(a: int | None, b: int | None) -> int | None:
    if a is None or b is None:
        return None
    return max(a, b)


@dataclass(frozen=True, slots=True)
class Interval:
    """闭整数区间 [lower, upper]；端点为 ``None`` 表示无穷。"""

    lower: int | None
    upper: int | None

    def __post_init__(self) -> None:
        lo, hi = self.lower, self.upper
        if lo is not None:
            require_int(lo, "Interval.lower")
        if hi is not None:
            require_int(hi, "Interval.upper")
        if lo is not None and hi is not None and lo > hi:
            raise ValidationError(
                f"empty/degenerate interval [{lo}, {hi}]: lower > upper",
                "Interval",
            )

    # -- 基本构造 ------------------------------------------------------------

    @classmethod
    def singleton(cls, value: int) -> "Interval":
        require_int(value, "Interval.singleton.value")
        return cls(value, value)

    @classmethod
    def top(cls) -> "Interval":
        return cls(None, None)

    @classmethod
    def at_most(cls, c: int) -> "Interval":
        require_int(c, "Interval.at_most.c")
        return cls(None, c)

    @classmethod
    def at_least(cls, c: int) -> "Interval":
        require_int(c, "Interval.at_least.c")
        return cls(c, None)

    @property
    def is_top(self) -> bool:
        return self.lower is None and self.upper is None

    # -- 集合运算 ------------------------------------------------------------

    def contains_int(self, value: int) -> bool:
        require_int(value, "Interval.contains_int.value")
        if self.lower is not None and value < self.lower:
            return False
        if self.upper is not None and value > self.upper:
            return False
        return True

    def subseteq(self, other: "Interval") -> bool:
        """逐端点包含判定（符号比较，绝不枚举整数）。"""
        return _low_leq(other.lower, self.lower) and _high_leq(self.upper, other.upper)

    def join(self, other: "Interval") -> "Interval":
        """凸包（并集的最小外包区间）。"""
        return Interval(
            _low_min(self.lower, other.lower),
            _high_max(self.upper, other.upper),
        )

    def intersect(self, other: "Interval") -> "Interval | None":
        """交集；不相交返回 ``None``。"""
        lo = self.lower if other.lower is None else (
            other.lower if self.lower is None else max(self.lower, other.lower)
        )
        hi = self.upper if other.upper is None else (
            other.upper if self.upper is None else min(self.upper, other.upper)
        )
        if lo is not None and hi is not None and lo > hi:
            return None
        return Interval(lo, hi)

    def add(self, k: int) -> "Interval":
        """整体平移 x -> x + k。"""
        require_int(k, "Interval.add.k")
        return Interval(
            None if self.lower is None else self.lower + k,
            None if self.upper is None else self.upper + k,
        )

    # -- 加宽 / 收窄 ---------------------------------------------------------

    def widen(self, other: "Interval") -> "Interval":
        """标准区间加宽：端点一旦被突破就推到无穷。

        调用约定：``other`` 是更新的迭代值，凸包序列下单调
        （``self ⊆ other``）；引擎用"先凸包两次、第三次起加宽"保证这一点。
        """
        lo = self.lower
        if _low_less(other.lower, self.lower):
            lo = None
        hi = self.upper
        if _high_leq(self.upper, other.upper) and self.upper != other.upper:
            hi = None
        return Interval(lo, hi)

    def narrow(self, other: "Interval") -> "Interval":
        """标准区间收窄：仅把加宽推出的无穷端点换成新迭代值的有限端点。"""
        lo = other.lower if self.lower is None else self.lower
        hi = other.upper if self.upper is None else self.upper
        return Interval(lo, hi)

    # -- 展示 ----------------------------------------------------------------

    @property
    def text(self) -> str:
        lo = "-inf" if self.lower is None else str(self.lower)
        hi = "+inf" if self.upper is None else str(self.upper)
        return f"[{lo}, {hi}]"

    def to_dict(self) -> dict[str, int | None]:
        return {"lower": self.lower, "upper": self.upper}


@dataclass(frozen=True, slots=True)
class AbstractState:
    """对一组变量的逐变量区间映射；``bottom=True`` 表示不可达（底元素）。"""

    variables: tuple[str, ...]
    bounds: dict[str, Interval]
    bottom: bool = False

    @classmethod
    def bottom_of(cls, variables: tuple[str, ...]) -> "AbstractState":
        return cls(tuple(variables), {}, bottom=True)

    @classmethod
    def top_of(cls, variables: tuple[str, ...]) -> "AbstractState":
        return cls(
            tuple(variables),
            {v: Interval.top() for v in variables},
            bottom=False,
        )

    def get(self, var: str) -> Interval:
        if self.bottom:
            raise ValueError("cannot read a variable from bottom state")
        return self.bounds[var]

    def _join_into(self, other: "AbstractState", how: str) -> "AbstractState":
        if self.bottom:
            return other
        if other.bottom:
            return self
        bounds: dict[str, Interval] = {}
        for v in self.variables:
            a, b = self.bounds[v], other.bounds[v]
            if how == "join":
                bounds[v] = a.join(b)
            elif how == "widen":
                bounds[v] = a.widen(b)
            elif how == "narrow":
                bounds[v] = a.narrow(b)
            else:  # pragma: no cover - 内部调用不会出现
                raise AssertionError(how)
        return AbstractState(self.variables, bounds, False)

    def join(self, other: "AbstractState") -> "AbstractState":
        return self._join_into(other, "join")

    def widen(self, other: "AbstractState") -> "AbstractState":
        return self._join_into(other, "widen")

    def narrow(self, other: "AbstractState") -> "AbstractState":
        return self._join_into(other, "narrow")

    def widen_selective(
        self, other: "AbstractState", widened: set[str]
    ) -> "AbstractState":
        """``widened`` 中的变量用标准 widening，其余取精确凸包。"""
        if self.bottom:
            return other
        if other.bottom:
            return self
        bounds: dict[str, Interval] = {}
        for v in self.variables:
            bounds[v] = self.bounds[v].widen(other.bounds[v]) if v in widened else self.bounds[v].join(other.bounds[v])
        return AbstractState(self.variables, bounds, False)

    def narrow_selective(
        self, other: "AbstractState", widened: set[str]
    ) -> "AbstractState":
        """``widened`` 中的变量用标准 narrowing，其余直接采用新方程值。"""
        if self.bottom:
            return self
        if other.bottom:
            return self
        bounds: dict[str, Interval] = {}
        for v in self.variables:
            bounds[v] = self.bounds[v].narrow(other.bounds[v]) if v in widened else other.bounds[v]
        return AbstractState(self.variables, bounds, False)

    def subseteq(self, other: "AbstractState") -> bool:
        """逐变量符号包含；底 ⊆ 一切。"""
        if self.bottom:
            return True
        if other.bottom:
            return False
        return all(self.bounds[v].subseteq(other.bounds[v]) for v in self.variables)

    def assign(self, var: str, value: Interval) -> "AbstractState":
        if self.bottom:
            return self
        bounds = dict(self.bounds)
        bounds[var] = value
        return AbstractState(self.variables, bounds, False)

    def restrict(self, var: str, iv: Interval | None) -> "AbstractState":
        """与单变量区间 iv 取交；为空则到底。"""
        if self.bottom:
            return self
        if iv is None:
            return AbstractState.bottom_of(self.variables)
        new_iv = self.bounds[var].intersect(iv)
        if new_iv is None:
            return AbstractState.bottom_of(self.variables)
        bounds = dict(self.bounds)
        bounds[var] = new_iv
        return AbstractState(self.variables, bounds, False)

    @property
    def text(self) -> str:
        if self.bottom:
            return "bottom (unreachable)"
        return ", ".join(f"{v}: {self.bounds[v].text}" for v in self.variables)

    def to_dict(self) -> dict[str, object]:
        if self.bottom:
            return {"bottom": True}
        return {"bottom": False, "bounds": {v: self.bounds[v].to_dict() for v in self.variables}}
