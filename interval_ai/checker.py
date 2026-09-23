"""独立局部转移包含性检查器。

本模块是**独立**的参考实现与检查器：不导入 :mod:`interval_ai.transfer`、
不导入引擎，端点算术与守卫过滤全部在此重新手写一遍，避免"用被测核心
给自己算期望值"。

证明方式是**符号端点包含**（无穷端点按偏序比较，有限端点按整数不等式），
绝不枚举整数、不用有限采样冒充证明：对任意具体整数 x，
``a.lower <= x <= a.upper`` 且 ``a ⊆ b``（端点逐点成立）⇒ x ∈ b。

检查的局部关系（局部可靠性）：

1. 块转移：独立参考域算出的块出精确像 ``T_ref(block_in)`` 必须被
   引擎 ``block_out`` 包含（本语言子集下实际应相等）。
2. 边守卫：``filter_guard(block_out, edge)`` 必须被后继块的 ``block_in`` 包含。
3. 入口：声明的入口初始区间必须被入口 ``block_in`` 包含。
4. 断言：``proved`` 的断言，其观测区间必须符号包含于要求区间。
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
_RefState = object  # dict[str, Bound] 或 _BOTTOM（仅作文档别名）


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


def _ref_add_iv(a: Bound, k: int) -> Bound:
    return (None if a[0] is None else a[0] + k, None if a[1] is None else a[1] + k)


def _ref_guard_bound(guard: Guard, taken: bool) -> Bound:
    c = guard.const
    if guard.op == "<=":
        return (None, c) if taken else (c + 1, None)
    return (c, None) if taken else (None, c - 1)


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


# -- 参考状态与独立转移 --------------------------------------------------------

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
    elif isinstance(stmt, AssertRange):
        pass  # 检查性语句不改变状态
    elif isinstance(stmt, (AssumeDiff, AssertDiff)):
        pass  # 区间参考视图无法表达关系语句：不改变逐变量区间
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


# -- 独立的差界矩阵参考（与 dbm.py 平行重写，互不导入） -------------------------
#
# 节点 0 为值恒 0 的参考点，节点 i>=1 为第 i-1 个变量；矩阵元素 d[i][j]
# 是最紧的 x_i - x_j <= d[i][j]，None 表示 +∞。以下闭包、赋值、假设、
# 守卫过滤都在此按 Floyd-Warshall 与差界语义独立实现，不调用关系域核心。

_RInf = None  # +∞


def _indices(n: int):
    """矩阵节点索引 0..n-1（纯索引遍历，绝不枚举变量取值）。"""
    i = 0
    while i < n:
        yield i
        i += 1


def _r_fresh(n: int):
    m = [[_RInf] * n for _ in _indices(n)]
    for i in _indices(n):
        m[i][i] = 0
    return m


def _r_closure(m):
    n = len(m)
    d = [list(row) for row in m]
    for k in _indices(n):
        dk = d[k]
        for i in _indices(n):
            dik = d[i][k]
            if dik is _RInf:
                continue
            di = d[i]
            for j in _indices(n):
                dkj = dk[j]
                if dkj is _RInf:
                    continue
                cand = dik + dkj
                if di[j] is _RInf or cand < di[j]:
                    di[j] = cand
    for i in _indices(n):
        if d[i][i] < 0:
            return None
    return d


def _r_set(m, i, j, bound):
    if m[i][j] is _RInf or bound < m[i][j]:
        m[i][j] = bound


def _r_forget(m, i):
    n = len(m)
    for k in _indices(n):
        if k != i:
            m[i][k] = _RInf
            m[k][i] = _RInf


def _r_reduce(variables, env, m):
    """区间注入零节点边 -> 闭包 -> 端点抽回区间；不可行返回 None。"""
    for k, v in enumerate(variables, start=1):
        lo, hi = env[v]
        if hi is not None:
            _r_set(m, k, 0, hi)
        if lo is not None:
            _r_set(m, 0, k, -lo)
    closed = _r_closure(m)
    if closed is None:
        return None
    out_env = dict(env)
    for k, v in enumerate(variables, start=1):
        hi = closed[k][0]
        lo = None if closed[0][k] is None else -closed[0][k]
        projected = (lo, hi)
        old = env[v]
        # 与旧区间取交（端点偏序下的逐点 min/max）
        nlo = (
            projected[0]
            if old[0] is None
            else (old[0] if projected[0] is None else max(old[0], projected[0]))
        )
        nhi = (
            projected[1]
            if old[1] is None
            else (old[1] if projected[1] is None else min(old[1], projected[1]))
        )
        out_env[v] = (nlo, nhi)
    return out_env, closed


# 积参考状态：_BOTTOM 或 (env: dict[str, Bound], matrix: list[list])
_RP_BOTTOM = object()


def _rp_from_core(abstract_state, diff_state):
    """由引擎的 (AbstractState, DiffState) 组装独立积参考状态。"""
    if abstract_state.bottom or (diff_state is not None and diff_state.bottom):
        return _RP_BOTTOM
    env = _from_abstract(abstract_state)
    if diff_state is None:
        return env  # 纯区间形态
    return env, [list(row) for row in diff_state.matrix]


def _rp_transfer_stmt(prod, stmt, variables):
    if prod is _RP_BOTTOM:
        return _RP_BOTTOM
    env, m = prod
    n = len(variables) + 1
    if isinstance(stmt, AssignConst):
        env = dict(env)
        env[stmt.target] = (stmt.const, stmt.const)
        ti = variables.index(stmt.target) + 1
        m = [list(row) for row in m]
        _r_forget(m, ti)
        _r_set(m, ti, 0, stmt.const)
        _r_set(m, 0, ti, -stmt.const)
    elif isinstance(stmt, AssignCopy):
        env = dict(env)
        env[stmt.target] = env[stmt.source]
        ti = variables.index(stmt.target) + 1
        si = variables.index(stmt.source) + 1
        m = [list(row) for row in m]
        if ti != si:
            _r_forget(m, ti)
            _r_set(m, ti, si, 0)
            _r_set(m, si, ti, 0)
    elif isinstance(stmt, AssignAdd):
        env = dict(env)
        env[stmt.target] = _ref_add_iv(env[stmt.source], stmt.const)
        ti = variables.index(stmt.target) + 1
        si = variables.index(stmt.source) + 1
        m = [list(row) for row in m]
        if ti == si:
            k = stmt.const
            for j in _indices(n):
                if j != ti and m[ti][j] is not _RInf:
                    m[ti][j] += k
            for i in _indices(n):
                if i != ti and m[i][ti] is not _RInf:
                    m[i][ti] -= k
            m[ti][ti] = 0
        else:
            _r_forget(m, ti)
            _r_set(m, ti, si, stmt.const)
            _r_set(m, si, ti, -stmt.const)
    elif isinstance(stmt, AssumeDiff):
        ai = variables.index(stmt.a) + 1
        bi = variables.index(stmt.b) + 1
        m = [list(row) for row in m]
        _r_set(m, ai, bi, stmt.const)
        reduced = _r_reduce(variables, dict(env), m)
        if reduced is None:
            return _RP_BOTTOM
        return reduced
    elif isinstance(stmt, (AssertRange, AssertDiff)):
        pass
    else:  # pragma: no cover - CFG 构造期已挡住
        raise TypeError(f"unsupported statement: {type(stmt).__name__}")
    reduced = _r_reduce(variables, env, m)
    if reduced is None:
        return _RP_BOTTOM
    return reduced


def _rp_transfer_block(prod, block: Block, variables):
    for stmt in block.statements:
        prod = _rp_transfer_stmt(prod, stmt, variables)
    return prod


def _rp_filter_guard(prod, guard: Guard, taken: bool, variables):
    if prod is _RP_BOTTOM:
        return _RP_BOTTOM
    env, m = prod
    hit = _ref_intersect_iv(env[guard.variable], _ref_guard_bound(guard, taken))
    if hit is None:
        return _RP_BOTTOM
    env = dict(env)
    env[guard.variable] = hit
    reduced = _r_reduce(variables, env, [list(row) for row in m])
    if reduced is None:
        return _RP_BOTTOM
    return reduced


def _rp_subseteq(a, b) -> bool:
    """积参考包含：底 ⊆ 一切；区间逐端点且 DBM 逐差界。"""
    if a is _RP_BOTTOM:
        return True
    if b is _RP_BOTTOM:
        return False
    env_a, m_a = a
    env_b, m_b = b
    if not all(_ref_iv_subseteq(env_a[v], env_b[v]) for v in env_a):
        return False
    n = len(m_a)
    for i in _indices(n):
        for j in _indices(n):
            bb = m_b[i][j]
            if bb is not _RInf:
                aa = m_a[i][j]
                if aa is _RInf or aa > bb:
                    return False
    return True


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


# -- 单语句 / 单边的独立检查（可脱离引擎单独使用） ------------------------------

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
    """对引擎结果逐块、逐边、逐断言做独立符号包含性检查。

    含差分约束的程序使用独立重写的"区间 × 差界矩阵"积参考：块像、边过滤、
    入口包含在积上逐端点且逐差界比较；纯区间程序沿用区间参考。
    """
    cfg = cfg or result.cfg
    report = CheckReport()

    if cfg.uses_diff_domain:
        _check_product_soundness(result, cfg, report)
    else:
        _check_interval_soundness(result, cfg, report)
    return report


def _check_interval_soundness(result, cfg: CFG, report: CheckReport) -> None:
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

    # 5) 断言结论的独立复核
    _check_range_asserts(result, report)


def _check_product_soundness(result, cfg: CFG, report: CheckReport) -> None:
    variables = tuple(cfg.variables)

    # 关系域未收敛（预算耗尽）：区间部分是一次合法的纯区间分析结果
    # （区间转移忽略差分语句），仍须满足全部区间局部关系；差分断言必须
    # 全为 unknown（未收敛不冒充任何证明，不可达空真也不允许）。
    truncated = bool(getattr(result, "relation_truncated", False))
    if truncated:
        _check_interval_soundness(result, cfg, report)
        _check_diff_asserts(result, cfg, report, truncated)
        return

    # 1) 入口初始区间 ⊆ 入口入（积投影），且入口差界必须蕴含入口区间
    entry_prod = _rp_from_core(
        result.block_in[cfg.entry], result.diff_in[cfg.entry]
    )
    initial = {
        v: cfg.entry_bounds[v] if v in cfg.entry_bounds else Interval(None, None)
        for v in cfg.variables
    }
    init_env = {v: (iv.lower, iv.upper) for v, iv in initial.items()}
    init_prod = _r_reduce(variables, init_env, _r_fresh(len(variables) + 1))
    if not _rp_subseteq(init_prod, entry_prod):
        report.fail(
            f"block {cfg.entry!r}.in",
            "entry product state does not contain declared entry bounds",
        )

    for name, block in cfg.blocks.items():
        bloc = f"block {name!r}"
        in_s = result.block_in[name]
        out_s = result.block_out[name]
        d_in = result.diff_in[name]
        d_out = result.diff_out[name]

        prod_in = _rp_from_core(in_s, d_in)
        prod_out_core = _rp_from_core(out_s, d_out)

        # 2) 块转移：独立积参考像必须 == 核心积出状态
        ref_out = _rp_transfer_block(prod_in, block, variables)
        if not _rp_subseteq(ref_out, prod_out_core):
            report.fail(f"{bloc}.out",
                        "product block-out does not contain reference image (unsound)")
        if not _rp_subseteq(prod_out_core, ref_out):
            report.fail(f"{bloc}.out",
                        "product block-out is strictly coarser than reference image")

        # 3) 入底 ⇒ 出底
        if in_s.bottom and not out_s.bottom:
            report.fail(f"{bloc}.out", "block-in is bottom but block-out is not")

        # 4) 每条边：守卫过滤后的积状态 ⊆ 后继积入
        for i, succ in enumerate(block.successors):
            if block.guard is None:
                edge = prod_out_core
            else:
                edge = _rp_filter_guard(
                    prod_out_core, block.guard, i == 0, variables
                )
            succ_prod = _rp_from_core(result.block_in[succ], result.diff_in[succ])
            if not _rp_subseteq(edge, succ_prod):
                side = "true" if i == 0 else "false"
                report.fail(
                    f"{bloc}.successors[{i}]({side}) -> {succ!r}",
                    "product edge state not contained in successor block-in",
                )

    _check_range_asserts(result, report)
    _check_diff_asserts(result, cfg, report, truncated)


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


def _check_diff_asserts(result, cfg: CFG, report: CheckReport, truncated: bool) -> None:
    for st in result.diff_asserts:
        loc = f"block {st.block!r}.diff_assert[{st.index}]"
        if st.verdict not in ("proved", "unknown"):
            report.fail(loc, f"illegal verdict {st.verdict!r}")
            continue
        if truncated and st.verdict == "proved" and not st.vacuous:
            report.fail(loc, "relation domain truncated but a diff assert is proved")
            continue
        if st.verdict != "proved" or st.vacuous:
            continue
        # 独立复核：从块入开始把该 AssertDiff 之前的语句独立走一遍
        # （AssumeDiff 会真实改变积状态），位置状态必须符号蕴含 a - b <= c。
        cur = _rp_from_core(
            result.block_in[st.block], result.diff_in[st.block]
        )
        ai = cfg.variables.index(st.statement.a) + 1
        bi = cfg.variables.index(st.statement.b) + 1
        for i, ps in enumerate(cfg.blocks[st.block].statements):
            if i == st.index:
                break
            cur = _rp_transfer_stmt(cur, ps, tuple(cfg.variables))
        if cur is _RP_BOTTOM:
            report.fail(loc, "marked proved but statement position is unreachable")
            continue
        _, mm = cur
        d = mm[ai][bi]
        if d is None or d > st.statement.const:
            report.fail(
                loc,
                f"marked proved but {st.statement.a}-{st.statement.b}<= "
                f"{d} does not imply <= {st.statement.const}",
            )
