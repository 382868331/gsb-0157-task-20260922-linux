"""差分约束关系域（DBM）及其与区间域的**归约积**。

差界矩阵（difference bound matrix，含零参考节点）：

* 节点 0 是值恒为 0 的虚拟节点 ``Z``；节点 i>=1 对应变量
  ``variables[i-1]``。
* 矩阵元素 ``M[i][j]`` 是已知最紧的约束 ``x_i - x_j <= M[i][j]``，
  ``None`` 表示 +∞（无约束）。
* 单变量区间由到零节点的两条边给出：``x <= c`` 即 ``M[x][Z] = c``；
  ``x >= c`` 即 ``M[Z][x] = -c``。
* 矩阵始终保持**最短路径闭包**（Floyd-Warshall）：对角线 < 0 即负环，
  约束系统不可行，对应抽象状态底（不可达）。

归约积在每一步都双向交换信息：区间端点注入 DBM，闭包后再把被关系约束
压紧的端点抽回区间（一次闭包即到归约不动点）。因此像 ``y = x`` 之后
在守卫 ``x <= 0`` 的真支上，区间域单独得不到的 ``y <= 0`` 会被自动推出。

加宽/收窄逐边进行，且与区间侧一样做"按循环内被修改变量的选择性加宽"：
只有端点触及被加宽变量的差界允许推到 +∞，其余边取精确凸包。
"""

from __future__ import annotations

from dataclasses import dataclass

from .cfg import (
    AssertDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
    Block,
    Guard,
)
from .intervals import Interval

INF = None  # 矩阵元素语义：None = 无界（+∞）
Edge = int | None


# -- 矩阵基础 -----------------------------------------------------------------

def _fresh_matrix(n: int) -> tuple[tuple[Edge, ...], ...]:
    """n 个节点（含零节点）：对角线 0，其余 +∞。"""
    m = [[INF] * n for _ in range(n)]
    for i in range(n):
        m[i][i] = 0
    return tuple(tuple(row) for row in m)


def _closure(
    m: tuple[tuple[Edge, ...], ...]
) -> tuple[tuple[Edge, ...], ...] | None:
    """全源最短路径闭包；出现负环（对角线 < 0）返回 ``None``。"""
    n = len(m)
    d = [list(row) for row in m]
    for k in range(n):
        dk = d[k]
        for i in range(n):
            dik = d[i][k]
            if dik is INF:
                continue
            di = d[i]
            for j in range(n):
                dkj = dk[j]
                if dkj is INF:
                    continue
                cand = dik + dkj
                if di[j] is INF or cand < di[j]:
                    di[j] = cand
    for i in range(n):
        if d[i][i] < 0:
            return None
    return tuple(tuple(row) for row in d)


def _pointwise_max(
    a: tuple[tuple[Edge, ...], ...], b: tuple[tuple[Edge, ...], ...]
) -> tuple[tuple[Edge, ...], ...]:
    """逐边取较弱界（任一为 +∞ 则 +∞）；调用后通常再做闭包。"""
    return tuple(
        tuple(
            INF if (x is INF or y is INF) else max(x, y)
            for x, y in zip(ra, rb)
        )
        for ra, rb in zip(a, b)
    )


# -- 公开的差分成品状态 --------------------------------------------------------

@dataclass(frozen=True, slots=True)
class DiffState:
    """归约积的关系视图：闭包后的差界矩阵（``bottom`` 时 ``matrix`` 为 None）。

    节点 0 为零参考；变量顺序与 :attr:`ProductState.variables` 一致。
    ``matrix[i][j]`` 即最紧的 ``x_i - x_j`` 上界（``None`` 无界）。
    """

    variables: tuple[str, ...]
    matrix: tuple[tuple[Edge, ...], ...] | None
    bottom: bool = False

    def index(self, var: str) -> int:
        return self.variables.index(var) + 1

    def bound(self, a: str, b: str) -> Edge:
        """当前可符号推出的最紧 ``a - b`` 上界；推不出返回 ``None``。"""
        if self.bottom or self.matrix is None:
            return INF
        return self.matrix[self.index(a)][self.index(b)]

    def entails(self, a: str, b: str, c: int) -> bool:
        """是否符号蕴含 ``a - b <= c``。"""
        d = self.bound(a, b)
        return d is not INF and d <= c

    def interval_of(self, var: str) -> Interval:
        """把该变量的差界投影回单变量区间。"""
        if self.bottom:
            raise ValueError("cannot project a bottom state")
        i = self.index(var)
        m = self.matrix
        hi = m[i][0]
        lo = INF if m[0][i] is INF else -m[0][i]
        return Interval(lo, hi)

    @property
    def text(self) -> str:
        if self.bottom:
            return "bottom (unreachable)"
        parts: list[str] = []
        for i, a in enumerate(self.variables, start=1):
            for j, b in enumerate(self.variables, start=1):
                if i == j:
                    continue
                d = self.matrix[i][j]
                if d is not INF:
                    parts.append(f"{a}-{b}<={d}")
            if self.matrix[i][0] is not INF:
                parts.append(f"{a}<={self.matrix[i][0]}")
            if self.matrix[0][i] is not INF:
                parts.append(f"-{a}<={self.matrix[0][i]}")
        return "; ".join(parts) if parts else "top (no relations)"

    def to_dict(self) -> dict[str, object]:
        if self.bottom or self.matrix is None:
            return {"bottom": True}
        bounds: dict[str, int] = {}
        for i, a in enumerate(self.variables, start=1):
            for j in range(0, len(self.variables) + 1):
                d = self.matrix[i][j]
                if d is INF:
                    continue
                rhs = "0" if j == 0 else self.variables[j - 1]
                bounds[f"{a}-{rhs}"] = d
        return {"bottom": False, "bounds": bounds}


# -- 归约积状态 ----------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class ProductState:
    """区间域 × 差界域的归约积状态。

    不变式（非底时）：``matrix`` 已闭包；``intervals`` 与矩阵相互归约
    （区间端点与到零节点的两条边一致，且不会更松）。
    """

    variables: tuple[str, ...]
    intervals: dict[str, Interval]
    matrix: tuple[tuple[Edge, ...], ...]
    bottom: bool = False

    # -- 构造 ---------------------------------------------------------------

    @classmethod
    def bottom_of(cls, variables: tuple[str, ...]) -> "ProductState":
        return cls(tuple(variables), {}, (), bottom=True)

    @classmethod
    def from_intervals(
        cls, variables: tuple[str, ...], intervals: dict[str, Interval]
    ) -> "ProductState | None":
        """由区间状态建立归约积：区间注入零节点边并闭包；不可行返回 None。"""
        n = len(variables) + 1
        m = _fresh_matrix(n)
        reduced = _reduce(variables, dict(intervals), m)
        if reduced is None:
            return None
        ivs, m2 = reduced
        return cls(tuple(variables), ivs, m2, False)

    def as_diff_state(self) -> DiffState:
        if self.bottom:
            return DiffState(self.variables, None, bottom=True)
        return DiffState(self.variables, self.matrix, False)

    def as_abstract_state(self):
        from .intervals import AbstractState

        if self.bottom:
            return AbstractState.bottom_of(self.variables)
        return AbstractState(self.variables, dict(self.intervals), False)

    def get(self, var: str) -> Interval:
        if self.bottom:
            raise ValueError("cannot read a variable from bottom state")
        return self.intervals[var]

    def index(self, var: str) -> int:
        return self.variables.index(var) + 1

    # -- 偏序与合并 ----------------------------------------------------------

    def subseteq(self, other: "ProductState") -> bool:
        if self.bottom:
            return True
        if other.bottom:
            return False
        iv_ok = all(self.intervals[v].subseteq(other.intervals[v]) for v in self.variables)
        if not iv_ok:
            return False
        # 关系包含：other 的每条差界都必须被 self 蕴含（self 的界 <= other 的界）
        for i in range(len(self.variables) + 1):
            for j in range(len(self.variables) + 1):
                ob = other.matrix[i][j]
                if ob is not INF:
                    sb = self.matrix[i][j]
                    if sb is INF or sb > ob:
                        return False
        return True

    def join(self, other: "ProductState") -> "ProductState":
        if self.bottom:
            return other
        if other.bottom:
            return self
        ivs = {v: self.intervals[v].join(other.intervals[v]) for v in self.variables}
        m = _closure(_pointwise_max(self.matrix, other.matrix))
        if m is None:
            # 两个闭包系统的逐边最大不可能引入负环；防御性处理
            m = _pointwise_max(self.matrix, other.matrix)
        return _product_or_bottom(self.variables, ivs, m)

    def widen_selective(
        self, candidate: "ProductState", widened: frozenset[str]
    ) -> "ProductState":
        """逐变量/逐边选择性加宽。

        区间侧与旧引擎一致：``widened`` 变量标准 widening，其余精确凸包。
        DBM 侧：只有端点触及被加宽变量的边允许推到 +∞；其余边直接采用
        合并值（这些边在该循环内不发散）。
        """
        if self.bottom:
            return candidate
        if candidate.bottom:
            return self
        # 先凸包（与区间侧延迟加宽同构），保证加宽参照单调的合并值
        hull_ivs = {
            v: self.intervals[v].join(candidate.intervals[v]) for v in self.variables
        }
        hull_m = _closure(_pointwise_max(self.matrix, candidate.matrix))
        if hull_m is None:  # 两个可行系统的凸包不可行不可能；防御
            hull_m = _pointwise_max(self.matrix, candidate.matrix)
        ivs = {
            v: (
                self.intervals[v].widen(hull_ivs[v])
                if v in widened
                else hull_ivs[v]
            )
            for v in self.variables
        }
        n = len(self.variables) + 1
        m = [list(row) for row in self.matrix]
        for i in range(n):
            for j in range(n):
                sb, hb = self.matrix[i][j], hull_m[i][j]
                # 闭包凸包保证：hb 有限 ⇒ sb 有限且 hb >= sb。
                # 标准加宽：该边任何变弱（0->1 或 有限->+∞）都推到 +∞。
                weakened = sb is not INF and (hb is INF or hb > sb)
                if weakened and _edge_touches(i, j, self.variables, widened):
                    m[i][j] = INF
                else:
                    m[i][j] = hb
        mt = tuple(tuple(row) for row in m)
        return _product_or_bottom(self.variables, ivs, mt)

    def narrow_selective(
        self, candidate: "ProductState", widened: frozenset[str]
    ) -> "ProductState":
        """收窄：被加宽变量相关边上的 +∞ 允许换成新方程值的有限界。"""
        if self.bottom:
            return self
        if candidate.bottom:
            return self
        ivs = {
            v: (
                self.intervals[v].narrow(candidate.intervals[v])
                if v in widened
                else candidate.intervals[v]
            )
            for v in self.variables
        }
        n = len(self.variables) + 1
        rows: list[list[Edge]] = []
        for i in range(n):
            row: list[Edge] = []
            for j in range(n):
                sb, cb = self.matrix[i][j], candidate.matrix[i][j]
                if not _edge_touches(i, j, self.variables, widened):
                    row.append(cb)
                elif sb is INF:
                    row.append(cb)  # 只允许 +∞ -> 有限界
                else:
                    row.append(sb)
            rows.append(row)
        mt = tuple(tuple(row) for row in rows)
        return _product_or_bottom(self.variables, ivs, mt)

    # -- 赋值 / 假设 / 守卫 ---------------------------------------------------

    def assign_const(self, target: str, c: int) -> "ProductState":
        if self.bottom:
            return self
        ivs = dict(self.intervals)
        ivs[target] = Interval.singleton(c)
        m = _forget(self.matrix, self.index(target))
        i = self.index(target)
        m = _set_edge(m, i, 0, c)
        m = _set_edge(m, 0, i, -c)
        return _product_or_bottom(self.variables, ivs, m)

    def assign_copy(self, target: str, source: str) -> "ProductState":
        if self.bottom:
            return self
        if target == source:
            return self
        ivs = dict(self.intervals)
        ivs[target] = self.intervals[source]
        ti, si = self.index(target), self.index(source)
        m = _forget(self.matrix, ti)
        m = _set_edge(m, ti, si, 0)
        m = _set_edge(m, si, ti, 0)
        return _product_or_bottom(self.variables, ivs, m)

    def assign_add(self, target: str, source: str, k: int) -> "ProductState":
        if self.bottom:
            return self
        ivs = dict(self.intervals)
        ivs[target] = self.intervals[source].add(k)
        ti, si = self.index(target), self.index(source)
        if ti == si:
            # x = x + k：旧关系整体平移即可，比"遗忘后重建"更精确
            m = [list(row) for row in self.matrix]
            for j in range(len(self.variables) + 1):
                if j != ti and m[ti][j] is not INF:
                    m[ti][j] += k
            for i in range(len(self.variables) + 1):
                if i != ti and m[i][ti] is not INF:
                    m[i][ti] -= k
            m[ti][ti] = 0
            mt = tuple(tuple(row) for row in m)
        else:
            m = _forget(self.matrix, ti)
            m = _set_edge(m, ti, si, k)
            m = _set_edge(m, si, ti, -k)
            mt = m
        return _product_or_bottom(self.variables, ivs, mt)

    def assume_diff(self, a: str, b: str, c: int) -> "ProductState":
        """并入假设 a - b <= c；与已知约束矛盾则到底（路径不可达）。"""
        if self.bottom:
            return self
        m = _set_edge(self.matrix, self.index(a), self.index(b), c)
        result = _reduce(self.variables, dict(self.intervals), m)
        if result is None:
            return ProductState.bottom_of(self.variables)
        ivs, m2 = result
        return ProductState(self.variables, ivs, m2, False)

    def restrict_interval(self, var: str, iv: Interval | None) -> "ProductState":
        """与单变量区间取交（守卫用）；为空到底。"""
        if self.bottom:
            return self
        if iv is None:
            return ProductState.bottom_of(self.variables)
        new_iv = self.intervals[var].intersect(iv)
        if new_iv is None:
            return ProductState.bottom_of(self.variables)
        ivs = dict(self.intervals)
        ivs[var] = new_iv
        result = _reduce(self.variables, ivs, self.matrix)
        if result is None:
            return ProductState.bottom_of(self.variables)
        ivs2, m = result
        return ProductState(self.variables, ivs2, m, False)

    def apply_guard(self, guard: Guard, taken: bool) -> "ProductState":
        c = guard.const
        if guard.op == "<=":
            iv = Interval(None, c) if taken else Interval(c + 1, None)
        else:
            iv = Interval(c, None) if taken else Interval(None, c - 1)
        return self.restrict_interval(guard.variable, iv)

    def entails_diff(self, a: str, b: str, c: int) -> bool:
        if self.bottom:
            return True  # 不可达位置空真
        return self.as_diff_state().entails(a, b, c)

    # -- 展示 ----------------------------------------------------------------

    @property
    def text(self) -> str:
        if self.bottom:
            return "bottom (unreachable)"
        iv = ", ".join(f"{v}: {self.intervals[v].text}" for v in self.variables)
        return f"[{iv}] {{ {self.as_diff_state().text} }}"


# -- 内部工具 ------------------------------------------------------------------

def _edge_touches(
    i: int, j: int, variables: tuple[str, ...], widened: frozenset[str]
) -> bool:
    for node in (i, j):
        if node != 0 and variables[node - 1] in widened:
            return True
    return False


def _set_edge(
    m: tuple[tuple[Edge, ...], ...], i: int, j: int, bound: int
) -> tuple[tuple[Edge, ...], ...]:
    rows = [list(row) for row in m]
    if rows[i][j] is INF or bound < rows[i][j]:
        rows[i][j] = bound
    return tuple(tuple(row) for row in rows)


def _forget(
    m: tuple[tuple[Edge, ...], ...], i: int
) -> tuple[tuple[Edge, ...], ...]:
    """遗忘节点 i 的全部入射/出射差界（对角线保 0）。"""
    n = len(m)
    rows = [list(row) for row in m]
    for k in range(n):
        if k != i:
            rows[i][k] = INF
            rows[k][i] = INF
    return tuple(tuple(row) for row in rows)


def _reduce(
    variables: tuple[str, ...],
    intervals: dict[str, Interval],
    m: tuple[tuple[Edge, ...], ...],
) -> tuple[dict[str, Interval], tuple[tuple[Edge, ...], ...]] | None:
    """区间 → DBM 注入、闭包、DBM → 区间 抽回（一次到归约不动点）。"""
    rows = [list(row) for row in m]
    for k, v in enumerate(variables, start=1):
        iv = intervals[v]
        if iv.upper is not INF and (rows[k][0] is INF or iv.upper < rows[k][0]):
            rows[k][0] = iv.upper
        if iv.lower is not INF:
            bound = -iv.lower
            if rows[0][k] is INF or bound < rows[0][k]:
                rows[0][k] = bound
    closed = _closure(tuple(tuple(row) for row in rows))
    if closed is None:
        return None
    ivs: dict[str, Interval] = {}
    for k, v in enumerate(variables, start=1):
        hi = closed[k][0]
        lo = INF if closed[0][k] is INF else -closed[0][k]
        projected = Interval(lo, hi)
        old = intervals[v]
        ivs[v] = projected if old.subseteq(projected) else old.intersect(projected)
    return ivs, closed


def _product_or_bottom(
    variables: tuple[str, ...],
    intervals: dict[str, Interval],
    m: tuple[tuple[Edge, ...], ...],
) -> ProductState:
    reduced = _reduce(variables, intervals, m)
    if reduced is None:
        return ProductState.bottom_of(variables)
    ivs, m2 = reduced
    return ProductState(variables, ivs, m2, False)


# -- 块 / 边转移（供引擎复用；断言类语句不改变状态） ----------------------------

def transfer_statement_product(state: ProductState, stmt: object) -> ProductState:
    if state.bottom:
        return state
    if isinstance(stmt, AssignConst):
        return state.assign_const(stmt.target, stmt.const)
    if isinstance(stmt, AssignCopy):
        return state.assign_copy(stmt.target, stmt.source)
    if isinstance(stmt, AssignAdd):
        return state.assign_add(stmt.target, stmt.source, stmt.const)
    if isinstance(stmt, AssumeDiff):
        return state.assume_diff(stmt.a, stmt.b, stmt.const)
    if isinstance(stmt, (AssertRange, AssertDiff)):
        return state
    raise TypeError(f"unsupported statement: {type(stmt).__name__}")  # pragma: no cover


def transfer_block_product(state: ProductState, block: Block) -> ProductState:
    cur = state
    for stmt in block.statements:
        cur = transfer_statement_product(cur, stmt)
    return cur


def edge_state_product(
    state: ProductState, block: Block, succ_index: int
) -> ProductState:
    if state.bottom or block.guard is None:
        return state
    return state.apply_guard(block.guard, taken=(succ_index == 0))
