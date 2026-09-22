"""抽象状态：变量名 -> Interval 的映射；不可达用 ``None`` 表示。"""

from __future__ import annotations

from typing import Iterable, Optional

from .cfg import Program
from .interval import Interval


class State:
    """抽象状态。

    内部持有 ``tuple[Interval | None, ...]``（按 Program.variables 的
    顺序）；任何变量对应 ``None`` 表示该状态整体不可达。不可达是
    全有或全无的：一旦某路径为空，整条路径状态为 BOTTOM。
    """

    __slots__ = ("_intervals", "_reachable")

    def __init__(self, intervals: Iterable[Optional[Interval]], reachable: bool = True) -> None:
        vals = tuple(intervals)
        if reachable:
            for iv in vals:
                if iv is None:
                    raise ValueError("可达状态不允许含 None 区间；不可达请用 State.bottom")
        self._intervals: tuple[Optional[Interval], ...] = vals
        self._reachable = reachable

    # ---- 构造 ----
    @staticmethod
    def bottom(program: Program) -> "State":
        return State((None,) * len(program.variables), reachable=False)

    @staticmethod
    def entry_state(program: Program) -> "State":
        """入口状态：给定具体初值则每变量为单值，否则全部 [0, 0]。"""
        if program.entry_state is None:
            vals = tuple(Interval.of(0) for _ in program.variables)
        else:
            vals = tuple(Interval.of(v) for v in program.entry_state)
        return State(vals)

    @property
    def reachable(self) -> bool:
        return self._reachable

    def get(self, name_or_index: str | int, program: Program) -> Optional[Interval]:
        """取变量区间；不可达状态返回 None。"""
        if not self._reachable:
            return None
        idx = program.var_index[name_or_index] if isinstance(name_or_index, str) else name_or_index
        return self._intervals[idx]

    def with_value(self, index: int, iv: Optional[Interval]) -> "State":
        """返回把第 index 个变量换成 iv 的新状态；iv=None 使状态不可达。"""
        if iv is None:
            if not self._reachable:
                return self
            return State((None,) * len(self._intervals), reachable=False)
        if not self._reachable:
            return self
        vals = list(self._intervals)
        vals[index] = iv
        return State(tuple(vals))

    # ---- 格运算 ----
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, State):
            return NotImplemented
        return self._reachable == other._reachable and (
            not self._reachable or self._intervals == other._intervals
        )

    def __hash__(self) -> int:
        return hash((self._reachable, self._intervals if self._reachable else None))

    def __le__(self, other: "State") -> bool:
        """``self ⊆ other``：bottom 含于一切；bottom 之外不可比下。"""
        if not self._reachable:
            return True
        if not other._reachable:
            return False
        return all(a <= b for a, b in zip(self._intervals, other._intervals))

    def subset_eq(self, other: "State") -> bool:
        return self <= other

    @staticmethod
    def join(x: "State", y: "State") -> "State":
        """逐变量凸包合并。bottom 是单位元。"""
        if not x._reachable:
            return y
        if not y._reachable:
            return x
        vals = tuple(
            Interval.hull(a, b) for a, b in zip(x._intervals, y._intervals)
        )
        return State(vals)

    @staticmethod
    def widen(x: "State", y: "State", mask: "tuple[bool, ...] | None" = None) -> "State":
        """逐变量 widening（x 为上一轮，y 为新合并值）。

        ``mask[i]=False`` 时第 i 个变量只做凸包不推无穷——用于局部化
        widening：循环头只加宽在本循环回边路径上被修改的变量。其余
        变量在循环内像为恒等，其上升由外层循环头的 widening 保证终止。
        """
        if not x._reachable:
            return y
        if not y._reachable:
            return x

        def one(a: Interval, b: Interval, widen_it: bool) -> Interval:
            return Interval.widen(a, b) if widen_it else Interval.hull(a, b)

        if mask is None:
            vals = tuple(
                Interval.widen(a, b) for a, b in zip(x._intervals, y._intervals)
            )
        else:
            vals = tuple(
                one(a, b, m)
                for a, b, m in zip(x._intervals, y._intervals, mask)
            )
        return State(vals)

    @staticmethod
    def narrow(x: "State", y: "State") -> "State":
        """逐变量 narrowing。"""
        if not x._reachable or not y._reachable:
            return x
        vals = tuple(
            Interval.narrow(a, b) for a, b in zip(x._intervals, y._intervals)
        )
        return State(vals)

    def to_dict(self, program: Program) -> Optional[dict[str, dict]]:
        """JSON 友好输出；不可达为 None。"""
        if not self._reachable:
            return None
        return {v: self._intervals[i].to_dict() for i, v in enumerate(program.variables)}

    def __repr__(self) -> str:
        if not self._reachable:
            return "State(BOTTOM)"
        return f"State{self._intervals!r}"
