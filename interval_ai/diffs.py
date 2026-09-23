"""差分约束域（difference-bound matrix，DBM）。

刻画形如 ``x_i - x_j <= c`` 的差分约束系统，``c`` 为数学整数；用一个
``(n+1) × (n+1)`` 的矩阵表示，多出的下标 ``n`` 是**零常数节点** z（值恒为 0）：

* ``M[i][j]`` = 已知最紧的 ``x_i - x_j`` 上界（``None`` 表示 +∞，无约束）；
* ``x <= c`` 即 ``M[i][z] = c``；``x >= c`` 即 ``M[z][i] = -c``；
* 矩阵始终保持 **Floyd–Warshall 闭包**（最短路径闭包）；对角线出现负数
  说明约束系统不可满足，对应抽象底（路径不可达）。

本域与区间域在 :mod:`interval_ai.relational` 里组成简约积：区间端点作为
``x - z`` / ``z - x`` 约束喂入 DBM，DBM 闭包后又把推出的端点回写给区间。
变量数受 CFG 构造期限制（至多 4 个程序变量），矩阵至多 5×5，闭包常数时间。

赋值的最强后条件按标准 DBM 做法：先"遗忘"目标变量的整行整列，再加入目标与
源/零节点的两条边，最后重新闭包。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .intervals import Interval

# 矩阵元素：None = +∞（无边）
_Bound = int | None


def _min_bound(a: _Bound, b: _Bound) -> _Bound:
    if a is None:
        return b
    if b is None:
        return a
    return min(a, b)


def _max_bound(a: _Bound, b: _Bound) -> _Bound:
    if a is None or b is None:
        return None
    return max(a, b)


def _top_matrix(n: int) -> tuple[tuple[_Bound, ...], ...]:
    rows: list[tuple[_Bound, ...]] = []
    for i in range(n):
        rows.append(tuple(0 if i == j else None for j in range(n)))
    return tuple(rows)


def _close(matrix: list[list[_Bound]]) -> list[list[_Bound]] | None:
    """就地 Floyd–Warshall 闭包；出现负对角线（不可满足）返回 ``None``。"""
    n = len(matrix)
    for k in range(n):
        row_k = matrix[k]
        for i in range(n):
            aik = matrix[i][k]
            if aik is None:
                continue
            row_i = matrix[i]
            for j in range(n):
                b = row_k[j]
                if b is None:
                    continue
                cand = aik + b
                cur = row_i[j]
                if cur is None or cand < cur:
                    row_i[j] = cand
    for i in range(n):
        if matrix[i][i] is not None and matrix[i][i] < 0:
            return None
    return matrix


@dataclass(frozen=True, slots=True)
class DiffState:
    """闭包后的 DBM 抽象状态；``bottom=True`` 表示约束不可满足（不可达）。"""

    variables: tuple[str, ...]
    matrix: tuple[tuple[_Bound, ...], ...] = ()
    bottom: bool = False

    # -- 构造 ----------------------------------------------------------------

    @classmethod
    def bottom_of(cls, variables: tuple[str, ...]) -> "DiffState":
        return cls(tuple(variables), (), bottom=True)

    @classmethod
    def top_of(cls, variables: tuple[str, ...]) -> "DiffState":
        n = len(variables) + 1
        return cls(tuple(variables), _top_matrix(n), bottom=False)

    @classmethod
    def from_intervals(
        cls,
        variables: tuple[str, ...],
        bounds: Mapping[str, Interval],
    ) -> "DiffState":
        """从逐变量区间构造初始 DBM（端点即 x-z / z-x 约束）。"""
        d = cls.top_of(variables)
        d = d.refine_with_intervals(bounds)
        return d if d is not None else cls.bottom_of(variables)

    # -- 下标 ----------------------------------------------------------------

    @property
    def zero(self) -> int:
        return len(self.variables)

    def _idx(self, name: str) -> int:
        return self.variables.index(name)

    def _as_lists(self) -> list[list[_Bound]]:
        return [list(row) for row in self.matrix]

    @staticmethod
    def _freeze(rows: list[list[_Bound]]) -> tuple[tuple[_Bound, ...], ...]:
        return tuple(tuple(row) for row in rows)

    # -- 观测 ----------------------------------------------------------------

    def _node(self, name: str | None) -> int:
        return self.zero if name is None else self.variables.index(name)

    def bound_of(self, left: str | None, right: str | None) -> _Bound:
        """已推出的最紧 ``left - right`` 上界；任一端为 ``None`` 对零节点。"""
        if self.bottom:
            raise ValueError("cannot read a bound from bottom diff state")
        return self.matrix[self._node(left)][self._node(right)]

    def implies(self, left: str | None, right: str | None, const: int) -> bool:
        """符号判定 DBM 是否已蕴含 ``left - right <= const``（绝不枚举值）。"""
        if self.bottom:
            return True  # 不可达位置空真
        bound = self.bound_of(left, right)
        return bound is not None and bound <= const

    def interval_of(self, name: str) -> Interval:
        """把某变量的 x-z / z-x 约束投影回闭区间。"""
        i = self._idx(name)
        upper = self.matrix[i][self.zero]
        low_bound = self.matrix[self.zero][i]
        lower = None if low_bound is None else -low_bound
        return Interval(lower, upper)

    # -- 约束添加 / 精化 ------------------------------------------------------

    def assume(
        self, left: str | None, right: str | None, const: int
    ) -> "DiffState":
        """加入 ``left - right <= const`` 并重新闭包（可能变底）。

        ``left``/``right`` 为 ``None`` 的一端取零常数节点：
        ``assume("x", None, c)`` 即 x <= c；``assume(None, "x", -c)`` 即 x >= c。
        """
        if self.bottom:
            return self
        return self._assume_edge(self._node(left), self._node(right), const)

    def assume_lower(self, name: str, const: int) -> "DiffState":
        """加入单边下界 ``name >= const``（即 ``z - name <= -const``）。"""
        if self.bottom:
            return self
        return self._assume_edge(self.zero, self._idx(name), -const)

    def _assume_edge(self, i: int, j: int, const: int) -> "DiffState":
        cur = self.matrix[i][j]
        if cur is not None and cur <= const:
            return self  # 已有更强约束
        rows = self._as_lists()
        rows[i][j] = const if cur is None else min(cur, const)
        closed = _close(rows)
        if closed is None:
            return DiffState.bottom_of(self.variables)
        return DiffState(self.variables, self._freeze(closed), False)

    def refine_with_intervals(
        self, bounds: Mapping[str, Interval]
    ) -> "DiffState | None":
        """把各变量有限端点并入 DBM；不可满足时返回 ``None``。

        ``None`` 返回值供简约积在内部区分"不可满足"；对外构造用
        :meth:`from_intervals`（它把 ``None`` 映射为底状态）。
        """
        if self.bottom:
            return self
        rows = self._as_lists()
        z = self.zero
        for name, iv in bounds.items():
            i = self._idx(name)
            if iv.upper is not None:
                cur = rows[i][z]
                rows[i][z] = iv.upper if cur is None else min(cur, iv.upper)
            if iv.lower is not None:
                cur = rows[z][i]
                bound = -iv.lower
                rows[z][i] = bound if cur is None else min(cur, bound)
        closed = _close(rows)
        if closed is None:
            return None
        return DiffState(self.variables, self._freeze(closed), False)

    # -- 赋值最强后条件 -------------------------------------------------------

    def _forgotten(self, target: int) -> list[list[_Bound]]:
        """遗忘 target 的整行整列（对角线重置为 0）。"""
        rows = self._as_lists()
        n = len(rows)
        for j in range(n):
            rows[target][j] = 0 if j == target else None
        for i in range(n):
            if i != target:
                rows[i][target] = None
        return rows

    def assign_const(self, target: str, const: int) -> "DiffState":
        if self.bottom:
            return self
        x = self._idx(target)
        z = self.zero
        rows = self._forgotten(x)
        rows[x][z] = const
        rows[z][x] = -const
        closed = _close(rows)
        if closed is None:  # pragma: no cover - 单变量常数赋值不可能矛盾
            return DiffState.bottom_of(self.variables)
        return DiffState(self.variables, self._freeze(closed), False)

    def assign_copy(self, target: str, source: str) -> "DiffState":
        return self._assign_from(target, source, 0)

    def assign_add(self, target: str, source: str, const: int) -> "DiffState":
        return self._assign_from(target, source, const)

    def _assign_from(self, target: str, source: str, const: int) -> "DiffState":
        """``target := source + const`` 的最强后条件（source 可等于 target）。

        标准做法：先在闭矩阵上保存 source 的整行整列（source==target 时
        必须先保存，遗忘后旧列已被清空），遗忘 target，再按
        ``new_t = v_source + const`` 填入：

        * ``M[i][t] = saved_col[i] - const``  （v_i - new_t）
        * ``M[t][j] = saved_row[j] + const``  （new_t - v_j）

        最后重新闭包。
        """
        if self.bottom:
            return self
        x = self._idx(target)
        y = self._idx(source)
        saved_col = [row[y] for row in self.matrix]
        saved_row = list(self.matrix[y])
        rows = self._forgotten(x)
        n = len(rows)
        for i in range(n):
            if i != x:
                b = saved_col[i]
                if b is not None:
                    rows[i][x] = b - const
        for j in range(n):
            if j != x:
                b = saved_row[j]
                if b is not None:
                    rows[x][j] = b + const
        closed = _close(rows)
        if closed is None:  # pragma: no cover - 仿射赋值不引入矛盾
            return DiffState.bottom_of(self.variables)
        return DiffState(self.variables, self._freeze(closed), False)

    # -- 格运算 ---------------------------------------------------------------

    def join(self, other: "DiffState") -> "DiffState":
        """逐元素取最大界（两个闭 DBM 的逐点最大仍闭，是标准 DBM 合流）。"""
        if self.bottom:
            return other
        if other.bottom:
            return self
        rows = [
            [_max_bound(a, b) for a, b in zip(r1, r2)]
            for r1, r2 in zip(self.matrix, other.matrix)
        ]
        return DiffState(self.variables, self._freeze(rows), False)

    def subseteq(self, other: "DiffState") -> bool:
        """``self`` 刻画的集合 ⊆ ``other``：self 的每条界都不更松。"""
        if self.bottom:
            return True
        if other.bottom:
            return False
        for r1, r2 in zip(self.matrix, other.matrix):
            for a, b in zip(r1, r2):
                if b is None:
                    continue  # other 无界，任意 a 都满足 a <= +∞
                if a is None or a > b:
                    return False
        return True

    def widen_selective(
        self, other: "DiffState", modified: set[str]
    ) -> "DiffState":
        """标准 DBM 加宽：被新迭代值突破的界直接放到 +∞。

        仅放宽"涉及该加宽点自然循环内被修改变量"的表项（行或列命中）；
        两个循环外变量之间的表项取精确合流，与区间域的选择性加宽一致。
        对角线恒为 0，不加宽。
        """
        if self.bottom:
            return other
        if other.bottom:
            return self
        mod_idx = {self._idx(v) for v in modified}
        n = len(self.variables) + 1
        rows: list[tuple[_Bound, ...]] = []
        for i in range(n):
            row: list[_Bound] = []
            for j in range(n):
                a, b = self.matrix[i][j], other.matrix[i][j]
                if i == j:
                    row.append(0)
                elif i in mod_idx or j in mod_idx:
                    # 被突破（新界更松）即推到 +∞
                    row.append(None if (a is None or _max_bound(a, b) != a) else a)
                else:
                    row.append(_max_bound(a, b))
            rows.append(tuple(row))
        return DiffState(self.variables, tuple(rows), False)

    def narrow_selective(
        self, other: "DiffState", modified: set[str]
    ) -> "DiffState":
        """加宽表项只把 +∞ 换回新方程值的有限界；其余直接采用新方程值。"""
        if self.bottom:
            return self
        if other.bottom:
            return self
        mod_idx = {self._idx(v) for v in modified}
        n = len(self.variables) + 1
        rows: list[tuple[_Bound, ...]] = []
        for i in range(n):
            row: list[_Bound] = []
            for j in range(n):
                a, b = self.matrix[i][j], other.matrix[i][j]
                if i == j:
                    row.append(0)
                elif i in mod_idx or j in mod_idx:
                    row.append(b if a is None else a)
                else:
                    row.append(b)
            rows.append(tuple(row))
        closed = _close([list(r) for r in rows])
        if closed is None:  # pragma: no cover - 收窄不会产生新矛盾
            return DiffState.bottom_of(self.variables)
        return DiffState(self.variables, self._freeze(closed), False)

    # -- 展示 ----------------------------------------------------------------

    def text(self) -> str:
        if self.bottom:
            return "diff-bottom (unsatisfiable)"
        parts: list[str] = []
        z = self.zero
        names = self.variables + ("0",)
        for i in range(z + 1):
            for j in range(z + 1):
                if i == j:
                    continue
                bound = self.matrix[i][j]
                if bound is not None:
                    parts.append(f"{names[i]}-{names[j]}<={bound}")
        return ", ".join(parts) if parts else "top (no difference bounds)"

    def to_dict(self) -> dict[str, object]:
        if self.bottom:
            return {"bottom": True}
        return {
            "bottom": False,
            "variables": list(self.variables),
            "matrix": [
                [v for v in row] for row in self.matrix
            ],
        }
