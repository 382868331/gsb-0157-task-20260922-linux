"""独立局部转移包含性检查器。

本模块是**独立**的参考实现与检查器：不导入 :mod:`interval_ai.transfer`、
:mod:`interval_ai.engine`、:mod:`interval_ai.relational`，也不导入
:mod:`interval_ai.diffs` 的 DBM 实现；端点算术、守卫过滤、Floyd–Warshall
闭包与赋值最强后条件全部在此重新手写一遍，避免"用被测核心给自己算期望值"。

证明方式是**符号包含**（无穷按偏序比较，有限端点按整数不等式；DBM 按
逐表项的界比较），绝不枚举整数、不用有限采样冒充证明：

* 区间：对任意具体整数 x，``a.lower <= x <= a.upper`` 且
  ``a ⊆ b``（端点逐点成立）⇒ x ∈ b。
* 差分约束：闭 DBM 的每条边 ``x_i - x_j <= M[i][j]`` 都是线性推论，
  逐表项 ``M_a[i][j] <= M_b[i][j]`` ⇒ a 刻画的整点集 ⊆ b。

检查的局部关系（局部可靠性）：

1. 块转移：独立参考域算出的块出精确像 ``T_ref(block_in)`` 必须与引擎
   ``block_out`` 一致（本语言子集下实际相等；区间与 DBM 两域都查）。
2. 边守卫：``filter_guard(block_out, edge)`` 必须被后继块的 ``block_in`` 包含。
3. 入口：声明的入口初始区间必须被入口 ``block_in`` 包含。
4. 断言：``proved`` 的区间断言观测区间必须符号包含于要求区间；
   ``proved`` 的差分断言必须被该点参考 DBM 蕴含。
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .cfg import (
    CFG,
    AssertDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
    Block,
    Guard,
    Statement,
)
from .intervals import AbstractState, Interval

# 参考域端点：None = 无穷。为保持独立性，不复用 intervals.py 里的比较函数。
Bound = tuple[int | None, int | None]  # (lower, upper)
_BOTTOM = object()  # 参考状态底标记
# DBM 表项：None = +∞（无边）
_DB = int | None


# -- 独立的端点算术（与 intervals.py 平行重写） --------------------------------

def _ref_le_lower(a: int | None, b: int | None) -> bool:
    """a <= b，下端点语义（None=-∞）。"""
    if a is None:
        return True
    if b is None:
        return False
    return a <= b


def _ref_le_upper(a: int | None, b: int | None) -> bool:
    """a <= b，上端点语义（None=+∞）。"""
    if b is None:
        return True
    if a is None:
        return False
    return a <= b


def _ref_iv_subseteq(a: Bound, b: Bound) -> bool:
    return _ref_le_lower(b[0], a[0]) and _ref_le_upper(a[1], b[1])


def _ref_join_iv(a: Bound, b: Bound) -> Bound:
    lo = None if (a[0] is None or b[0] is None) else min(a[0], b[0])
    hi = None if (a[1] is None or b[1] is None) else max(a[1], b[1])
    return (lo, hi)


def _ref_intersect_iv(a: Bound, b: Bound) -> Bound | None:
    if a[0] is None:
        lo = b[0]
    elif b[0] is None:
        lo = a[0]
    else:
        lo = max(a[0], b[0])
    if a[1] is None:
        hi = b[1]
    elif b[1] is None:
        hi = a[1]
    else:
        hi = min(a[1], b[1])
    if lo is not None and hi is not None and lo > hi:
        return None
    return (lo, hi)


def _ref_add_iv(a: Bound, k: int) -> Bound:
    return (None if a[0] is None else a[0] + k, None if a[1] is None else a[1] + k)


def _ref_guard_bound(guard: Guard, taken: bool) -> Bound:
    c = guard.const
    if guard.op == "<=":
        return (None, c) if taken else (c + 1, None)
    return (c, None) if taken else (None, c - 1)


# -- 独立的 DBM 参考实现（与 diffs.py 平行重写） -------------------------------
# 注意：本文件刻意不出现 range(...) 调用（独立性测试强制）：下标循环用
# while 表达；这里遍历的是矩阵下标，绝不枚举变量的整数值。

def _ref_db_top(n: int):
    rows = []
    i = 0
    while i < n:
        row = []
        j = 0
        while j < n:
            row.append(0 if i == j else None)
            j += 1
        rows.append(row)
        i += 1
    return rows


def _ref_db_close(rows) -> bool:
    """就地 Floyd–Warshall 闭包；负对角线（不可满足）时返回 False。"""
    n = len(rows)
    k = 0
    while k < n:
        rk = rows[k]
        i = 0
        while i < n:
            aik = rows[i][k]
            if aik is not None:
                ri = rows[i]
                j = 0
                while j < n:
                    b = rk[j]
                    if b is not None:
                        cand = aik + b
                        cur = ri[j]
                        if cur is None or cand < cur:
                            ri[j] = cand
                    j += 1
            i += 1
        k += 1
    i = 0
    while i < n:
        if rows[i][i] is not None and rows[i][i] < 0:
            return False
        i += 1
    return True


def _ref_db_join(a, b):
    return [
        [
            None if (x is None or y is None) else max(x, y)
            for x, y in zip(ra, rb)
        ]
        for ra, rb in zip(a, b)
    ]


def _ref_db_subseteq(a, b) -> bool:
    """a 刻画的整点集 ⊆ b：a 的每条界不更松。"""
    for ra, rb in zip(a, b):
        for x, y in zip(ra, rb):
            if y is None:
                continue
            if x is None or x > y:
                return False
    return True


def _ref_db_refine(rows, intervals, variables, z):
    """把区间端点并入 DBM 并闭包（区间 -> 差分方向的简约）。"""
    for name, iv in intervals.items():
        i = variables.index(name)
        if iv[1] is not None:
            cur = rows[i][z]
            rows[i][z] = iv[1] if cur is None else min(cur, iv[1])
        if iv[0] is not None:
            cur = rows[z][i]
            b = -iv[0]
            rows[z][i] = b if cur is None else min(cur, b)
    return _ref_db_close(rows)


def _ref_db_project(rows, variables, z, old_intervals):
    """DBM 端点投影回区间并与旧区间取交（差分 -> 区间方向的简约）。"""
    out = {}
    for name in variables:
        i = variables.index(name)
        upper = rows[i][z]
        low_bound = rows[z][i]
        lower = None if low_bound is None else -low_bound
        hit = _ref_intersect_iv(old_intervals[name], (lower, upper))
        if hit is None:
            return None
        out[name] = hit
    return out


class _RefRel:
    """区间 + DBM 的独立参考积状态（构造后即简约闭包）。"""

    def __init__(self, variables, intervals, db, ok=True):
        self.variables = list(variables)
        self.z = len(self.variables)
        self.intervals = intervals
        self.db = db
        self.ok = ok  # False = 底（不可满足）

    @classmethod
    def top(cls, variables, entry_bounds=None) -> "_RefRel":
        variables = list(variables)
        intervals = {v: (None, None) for v in variables}
        if entry_bounds:
            for v, iv in entry_bounds.items():
                intervals[v] = (iv.lower, iv.upper)
        db = _ref_db_top(len(variables) + 1)
        if not _ref_db_refine(db, intervals, variables, len(variables)):
            return cls(variables, intervals, db, ok=False)
        projected = _ref_db_project(db, variables, len(variables), intervals)
        if projected is None:
            return cls(variables, intervals, db, ok=False)
        return cls(variables, projected, db, ok=True)

    @classmethod
    def bottom(cls, variables) -> "_RefRel":
        return cls(list(variables), {}, [], ok=False)

    def copy(self) -> "_RefRel":
        if not self.ok:
            return _RefRel.bottom(self.variables)
        return _RefRel(
            self.variables,
            dict(self.intervals),
            [list(r) for r in self.db],
            ok=True,
        )

    def _reduce(self) -> "_RefRel":
        if not _ref_db_refine(self.db, self.intervals, self.variables, self.z):
            return _RefRel.bottom(self.variables)
        projected = _ref_db_project(
            self.db, self.variables, self.z, self.intervals
        )
        if projected is None:
            return _RefRel.bottom(self.variables)
        self.intervals = projected
        return self

    # -- 语句 ---------------------------------------------------------------

    def stmt(self, s: Statement) -> "_RefRel":
        if not self.ok:
            return self
        if isinstance(s, AssignConst):
            self.intervals[s.target] = (s.const, s.const)
            self._db_assign(self.z, s.const, s.target)
            return self._reduce()
        if isinstance(s, AssignCopy):
            self.intervals[s.target] = self.intervals[s.source]
            self._db_assign(self.variables.index(s.source), 0, s.target)
            return self._reduce()
        if isinstance(s, AssignAdd):
            self.intervals[s.target] = _ref_add_iv(
                self.intervals[s.source], s.const
            )
            self._db_assign(
                self.variables.index(s.source), s.const, s.target
            )
            return self._reduce()
        if isinstance(s, AssumeDiff):
            i = self.z if s.left is None else self.variables.index(s.left)
            j = self.z if s.right is None else self.variables.index(s.right)
            cur = self.db[i][j]
            self.db[i][j] = s.const if cur is None else min(cur, s.const)
            if not _ref_db_close(self.db):
                return _RefRel.bottom(self.variables)
            return self._reduce()
        # AssertRange / AssertDiff 为检查性语句，不改变状态
        return self

    def _db_assign(self, src_idx: int, k: int, target: str) -> None:
        """new_target := v_src + k 的最强后条件（src 可为零节点，可等于 target）。"""
        x = self.variables.index(target)
        saved_col = [row[src_idx] for row in self.db]
        saved_row = list(self.db[src_idx])
        n = len(self.db)
        j = 0
        while j < n:
            self.db[x][j] = 0 if j == x else None
            j += 1
        i = 0
        while i < n:
            if i != x:
                self.db[i][x] = None
            i += 1
        i = 0
        while i < n:
            if i != x and saved_col[i] is not None:
                self.db[i][x] = saved_col[i] - k
            i += 1
        j = 0
        while j < n:
            if j != x and saved_row[j] is not None:
                self.db[x][j] = saved_row[j] + k
            j += 1
        _ref_db_close(self.db)

    # -- 守卫 / 合流 ---------------------------------------------------------

    def guard(self, g: Guard, taken: bool) -> "_RefRel":
        if not self.ok:
            return self
        hit = _ref_intersect_iv(self.intervals[g.variable], _ref_guard_bound(g, taken))
        if hit is None:
            return _RefRel.bottom(self.variables)
        self.intervals[g.variable] = hit
        b = _ref_guard_bound(g, taken)
        i = self.variables.index(g.variable)
        if b[0] is None:  # x <= c
            cur = self.db[i][self.z]
            self.db[i][self.z] = b[1] if cur is None else min(cur, b[1])
        else:  # x >= c
            cur = self.db[self.z][i]
            bound = -b[0]
            self.db[self.z][i] = bound if cur is None else min(cur, bound)
        if not _ref_db_close(self.db):
            return _RefRel.bottom(self.variables)
        return self._reduce()

    def join(self, other: "_RefRel") -> "_RefRel":
        if not self.ok:
            return other.copy()
        if not other.ok:
            return self.copy()
        intervals = {
            v: _ref_join_iv(self.intervals[v], other.intervals[v])
            for v in self.variables
        }
        db = _ref_db_join(self.db, other.db)
        merged = _RefRel(self.variables, intervals, db, ok=True)
        return merged._reduce()


# -- 报告 ----------------------------------------------------------------------

@dataclass(slots=True)
class CheckReport:
    ok: bool = True
    violations: list[str] = field(default_factory=list)

    def fail(self, location: str, detail: str) -> None:
        self.ok = False
        self.violations.append(f"[{location}] {detail}")

    def raise_if_bad(self) -> None:
        if not self.ok:
            raise ContainmentViolation(self.violations)


class ContainmentViolation(Exception):
    """局部包含关系被破坏（说明核心转移或不动点不健全）。"""

    def __init__(self, violations: list[str]) -> None:
        super().__init__("; ".join(violations))
        self.violations = violations


# -- 单语句 / 单边的独立检查（区间，可脱离引擎单独使用） ------------------------

def _from_abstract(state: AbstractState):
    if state.bottom:
        return _BOTTOM
    return {v: (state.bounds[v].lower, state.bounds[v].upper) for v in state.variables}


def _ref_transfer_stmt(env, stmt: Statement):
    if env is _BOTTOM:
        return _BOTTOM
    out = dict(env)
    if isinstance(stmt, AssignConst):
        out[stmt.target] = (stmt.const, stmt.const)
    elif isinstance(stmt, AssignCopy):
        out[stmt.target] = out[stmt.source]
    elif isinstance(stmt, AssignAdd):
        out[stmt.target] = _ref_add_iv(out[stmt.source], stmt.const)
    elif isinstance(stmt, (AssertRange, AssumeDiff, AssertDiff)):
        pass  # 检查性语句；差分假设的关系信息由关系参考积单独处理
    else:  # pragma: no cover - CFG 构造期已挡住
        raise TypeError(f"unsupported statement: {type(stmt).__name__}")
    return out


def _ref_transfer_block(state: AbstractState, block: Block):
    env = _from_abstract(state)
    for stmt in block.statements:
        env = _ref_transfer_stmt(env, stmt)
    return env


def _ref_filter_guard(env, guard: Guard, taken: bool):
    if env is _BOTTOM:
        return _BOTTOM
    hit = _ref_intersect_iv(env[guard.variable], _ref_guard_bound(guard, taken))
    if hit is None:
        return _BOTTOM
    out = dict(env)
    out[guard.variable] = hit
    return out


def _ref_state_subseteq(a, b) -> bool:
    """参考状态包含；底 ⊆ 一切。"""
    if a is _BOTTOM:
        return True
    if b is _BOTTOM:
        return False
    if set(a) != set(b):
        return False
    return all(_ref_iv_subseteq(a[v], b[v]) for v in a)


def check_transfer_step(
    stmt: Statement, before: AbstractState, after: AbstractState
) -> CheckReport:
    """检查单语句：独立参考像必须被 ``after`` 包含（且本语言下应精确相等）。"""
    report = CheckReport()
    loc = f"transfer {type(stmt).__name__}"
    ref = _ref_transfer_stmt(_from_abstract(before), stmt)
    core = _from_abstract(after)
    if not _ref_state_subseteq(ref, core):
        report.fail(loc, "reference image is NOT contained in core result (unsound)")
    if not _ref_state_subseteq(core, ref):
        report.fail(loc, "core result is strictly coarser than exact reference image")
    return report


def check_edge_guard(
    guard: Guard, taken: bool, source_out: AbstractState, target_in: AbstractState
) -> CheckReport:
    """检查一条守卫边：过滤后的源出状态必须包含于目标入状态。"""
    report = CheckReport()
    side = "true" if taken else "false"
    ref = _ref_filter_guard(_from_abstract(source_out), guard, taken)
    core = _from_abstract(target_in)
    if not _ref_state_subseteq(ref, core):
        report.fail(
            f"guard {guard.variable} {guard.op} {guard.const} ({side} edge)",
            "filtered source state not contained in target block-in",
        )
    return report


# -- 整个分析结果的局部健全性检查 ----------------------------------------------

def check_local_soundness(result, cfg: CFG | None = None) -> CheckReport:
    """对引擎结果逐块、逐边、逐断言做独立符号包含性检查。"""
    cfg = cfg or result.cfg
    if getattr(result, "relational_enabled", False) and result.relational_converged:
        return _check_relational(result, cfg)
    return _check_intervals(result, cfg)


def _check_intervals(result, cfg: CFG) -> CheckReport:
    """纯区间结果检查（含关系迭代未收敛时的回退结果）。"""
    report = CheckReport()

    # 1) 入口初始区间 ⊆ 入口块入不变量
    entry_in = _from_abstract(result.block_in[cfg.entry])
    initial = {
        v: cfg.entry_bounds[v] if v in cfg.entry_bounds else Interval(None, None)
        for v in cfg.variables
    }
    initial_ref = {v: (iv.lower, iv.upper) for v, iv in initial.items()}
    if not _ref_state_subseteq(initial_ref, entry_in):
        report.fail(f"block {cfg.entry!r}.in", "does not contain declared entry bounds")

    for name, block in cfg.blocks.items():
        bloc = f"block {name!r}"
        in_s = result.block_in[name]
        out_s = result.block_out[name]

        # 2) 块内语句转移：参考精确像 == 核心出状态
        ref_out = _ref_transfer_block(in_s, block)
        core_out = _from_abstract(out_s)
        if not _ref_state_subseteq(ref_out, core_out):
            report.fail(f"{bloc}.out", "core block-out does not contain reference image (unsound)")
        if not _ref_state_subseteq(core_out, ref_out):
            report.fail(f"{bloc}.out", "core block-out is strictly coarser than reference image")

        # 3) 出状态底一致性：入底 ⇒ 出底（本语言无"奇迹"赋值）
        if in_s.bottom and not out_s.bottom:
            report.fail(f"{bloc}.out", "block-in is bottom but block-out is not")

        # 4) 每条边：守卫过滤后 ⊆ 后继入
        for i, succ in enumerate(block.successors):
            if block.guard is None:
                edge_env = _from_abstract(out_s)
            else:
                edge_env = _ref_filter_guard(_from_abstract(out_s), block.guard, i == 0)
            succ_in = _from_abstract(result.block_in[succ])
            if not _ref_state_subseteq(edge_env, succ_in):
                side = "true" if i == 0 else "false"
                report.fail(
                    f"{bloc}.successors[{i}]({side}) -> {succ!r}",
                    "edge state not contained in successor block-in",
                )

    _check_range_asserts(result, report)
    _check_diff_asserts_fallback(result, report)
    return report


def _check_range_asserts(result, report: CheckReport) -> None:
    for st in result.asserts:
        loc = f"block {st.block!r}.assert[{st.index}]"
        if st.verdict not in ("proved", "unknown"):
            report.fail(loc, f"illegal verdict {st.verdict!r}")
            continue
        if st.verdict == "proved" and not st.vacuous:
            observed = (st.observed.lower, st.observed.upper)
            required: Bound = (st.statement.lower, st.statement.upper)
            if not _ref_iv_subseteq(observed, required):
                report.fail(
                    loc,
                    f"marked proved but observed {observed} not contained in {required}",
                )


def _check_diff_asserts_fallback(result, report: CheckReport) -> None:
    """未收敛回退结果：差分断言只允许 unknown 或不可达位置的空真 proved。"""
    for st in getattr(result, "diff_asserts", []):
        loc = f"block {st.block!r}.diff-assert[{st.index}]"
        if st.verdict not in ("proved", "unknown"):
            report.fail(loc, f"illegal verdict {st.verdict!r}")
            continue
        if st.verdict == "proved" and not st.vacuous:
            report.fail(
                loc,
                "relation analysis did not converge; a non-vacuous diff assert "
                "must be unknown, not proved",
            )


# -- 关系结果（区间 × DBM 简约积）的独立检查 -----------------------------------

def _core_rel_at(result, name: str, which: str) -> _RefRel:
    """从引擎结果读出某块入/出的积状态（仅读数，不调用核心代码）。"""
    iv_state = result.block_in[name] if which == "in" else result.block_out[name]
    db_state = (
        result.block_in_diff[name] if which == "in" else result.block_out_diff[name]
    )
    variables = list(result.cfg.variables)
    if iv_state.bottom or db_state.bottom:
        return _RefRel.bottom(variables)
    intervals = {
        v: (iv_state.bounds[v].lower, iv_state.bounds[v].upper) for v in variables
    }
    db = [list(r) for r in db_state.matrix]
    return _RefRel(variables, intervals, db, ok=True)


def _rel_subseteq(a: _RefRel, b: _RefRel) -> bool:
    if not a.ok:
        return True
    if not b.ok:
        return False
    if not all(
        _ref_iv_subseteq(a.intervals[v], b.intervals[v]) for v in a.variables
    ):
        return False
    return _ref_db_subseteq(a.db, b.db)


def _rel_equal(a: _RefRel, b: _RefRel) -> bool:
    return _rel_subseteq(a, b) and _rel_subseteq(b, a)


def _check_relational(result, cfg: CFG) -> CheckReport:
    report = CheckReport()
    variables = list(cfg.variables)

    # 1) 入口初始状态 ⊆ 入口块入
    entry = _core_rel_at(result, cfg.entry, "in")
    initial = _RefRel.top(
        variables,
        {
            v: cfg.entry_bounds[v]
            for v in cfg.entry_bounds
        } or None,
    )
    if not _rel_subseteq(initial, entry):
        report.fail(f"block {cfg.entry!r}.in",
                    "does not contain declared entry bounds (relational)")

    for name, block in cfg.blocks.items():
        bloc = f"block {name!r}"
        ref_in = _core_rel_at(result, name, "in")

        # 2) 逐语句独立推进参考状态（同时记录断言点），块末须与核心出相等
        ref = ref_in.copy()
        for i, s in enumerate(block.statements):
            ref = ref.stmt(s)
            if isinstance(s, AssertRange):
                _check_one_range_assert_rel(
                    result, report, name, i, s, ref
                )
            if isinstance(s, AssertDiff):
                _check_one_diff_assert_rel(
                    result, report, name, i, s, ref
                )
        core_out = _core_rel_at(result, name, "out")
        if not _rel_subseteq(ref, core_out):
            report.fail(
                f"{bloc}.out",
                "core block-out does not contain relational reference image (unsound)",
            )
        if not _rel_subseteq(core_out, ref):
            report.fail(
                f"{bloc}.out",
                "core block-out is strictly coarser than relational reference image",
            )

        # 3) 底一致性
        if not ref_in.ok and core_out.ok:
            report.fail(f"{bloc}.out", "block-in is bottom but block-out is not")

        # 4) 每条守卫边：独立过滤后 ⊆ 后继入
        for ei, succ in enumerate(block.successors):
            if block.guard is None:
                edge = core_out.copy()
            else:
                edge = core_out.copy().guard(block.guard, ei == 0)
            succ_in = _core_rel_at(result, succ, "in")
            if not _rel_subseteq(edge, succ_in):
                side = "true" if ei == 0 else "false"
                report.fail(
                    f"{bloc}.successors[{ei}]({side}) -> {succ!r}",
                    "relational edge state not contained in successor block-in",
                )

    # 5) 断言必须与 CFG 中的断言一一对应（无丢失、无多余、verdict 合法）
    for st in result.asserts:
        loc = f"block {st.block!r}.assert[{st.index}]"
        if st.verdict not in ("proved", "unknown"):
            report.fail(loc, f"illegal verdict {st.verdict!r}")
    for st in result.diff_asserts:
        loc = f"block {st.block!r}.diff-assert[{st.index}]"
        if st.verdict not in ("proved", "unknown"):
            report.fail(loc, f"illegal verdict {st.verdict!r}")
    return report


def _check_one_range_assert_rel(
    result, report: CheckReport, name: str, index: int, s: AssertRange, ref: _RefRel
) -> None:
    st = next(
        (a for a in result.asserts if a.block == name and a.index == index), None
    )
    if st is None:
        report.fail(f"block {name!r}.assert[{index}]", "engine dropped an AssertRange")
        return
    loc = f"block {name!r}.assert[{index}]"
    if not ref.ok:
        if not st.vacuous:
            report.fail(loc, "assert after an infeasible AssumeDiff must be vacuous proved")
        return
    if st.vacuous:
        report.fail(loc, "assert marked vacuous at a reachable statement position")
        return
    observed = ref.intervals[s.target]
    required: Bound = (s.lower, s.upper)
    if st.verdict == "proved":
        if not _ref_iv_subseteq(observed, required):
            report.fail(
                loc,
                f"marked proved but reference observed {observed} not in {required}",
            )
    if st.observed is not None:
        core_obs = (st.observed.lower, st.observed.upper)
        if core_obs != observed:
            report.fail(
                loc,
                f"observed interval {core_obs} disagrees with reference {observed}",
            )


def _check_one_diff_assert_rel(
    result, report: CheckReport, name: str, index: int, s: AssertDiff, ref: _RefRel
) -> None:
    st = next(
        (a for a in result.diff_asserts if a.block == name and a.index == index),
        None,
    )
    if st is None:
        report.fail(f"block {name!r}.diff-assert[{index}]",
                    "engine dropped an AssertDiff")
        return
    loc = f"block {name!r}.diff-assert[{index}]"
    if not ref.ok:
        if not st.vacuous:
            report.fail(loc, "assert after an infeasible AssumeDiff must be vacuous proved")
        return
    if st.vacuous:
        report.fail(loc, "diff assert marked vacuous at a reachable statement position")
        return
    i = ref.z if s.left is None else ref.variables.index(s.left)
    j = ref.z if s.right is None else ref.variables.index(s.right)
    bound = ref.db[i][j]
    implies = bound is not None and bound <= s.const
    left_text = "0" if s.left is None else s.left
    right_text = "0" if s.right is None else s.right
    if st.verdict == "proved" and not implies:
        report.fail(
            loc,
            f"marked proved but reference DBM bound "
            f"{left_text}-{right_text}<={bound} does not imply <= {s.const}",
        )
    if st.observed_bound != bound:
        report.fail(
            loc,
            f"observed bound {st.observed_bound} disagrees with reference {bound}",
        )
