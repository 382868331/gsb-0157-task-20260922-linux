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
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
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
    """对引擎结果逐块、逐边、逐断言做独立符号包含性检查。"""
    cfg = cfg or result.cfg
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

    # 5) 断言结论的独立复核
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
    return report
