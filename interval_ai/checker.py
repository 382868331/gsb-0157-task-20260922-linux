"""独立局部转移包含性检查器（证明器，非采样）。

用途：对一份声称的块不变量/边状态做**局部可靠性**验收。检查两条：

1. 块条件：给定块 B 的声称入口环境 ``I_B``，独立重算 B 的语句与
   分支过滤，证明每条边声称状态 ``E_{B->S}`` 包含真实抽象像；
2. 归纳条件：入口初值环境 ⊆ ``I_entry``；对每个块 B，所有入边
   声称状态的凸包 ⊆ ``I_B``。

两条全成立则声称不变量构成 Floyd/Hoare 式局部归纳证书（对本语句
子集这同时蕴含 assert 结论可靠）。

独立性与“禁止采样”：

* 本模块**不导入** interval/state/semantics/analyzer，区间用裸
  ``(lo, hi)`` 二元组，转移按下述端点公式从头实现；
* 全部结论由整数端点的单调公式与集合包含推出，是精确的符号证明，
  **不枚举任何具体取值**。本模块不存在采样/模糊测试入口；
* 因为子集只有赋常量/复制/加常量与 x<=c/x>=c 过滤，每条变量在块内
  始终是入口变量的仿射函数，端点像可由 min/max 公式精确给出，
  检查结果无近似误差。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from .cfg import AddConst, AssertRange, Assign, Block, Cond, Copy, Jump, Program

# 独立区间类型：(lo, hi)，None = 无穷。与核心 Interval 无任何代码共享。
IV = tuple[Optional[int], Optional[int]]
TOP: IV = (None, None)
BOTTOM_SENTINEL = None  # 环境不可达用 None 表示
Env = Optional[dict[str, IV]]

PROOF_METHOD = "symbolic_endpoint_inclusion:exact_for_affine_subset"


class CheckViolation(Exception):
    """构造检查输入时的结构问题（非包含失败）。"""


@dataclass(frozen=True)
class CheckItem:
    name: str
    location: str
    holds: bool
    detail: str

    def to_dict(self) -> dict:
        return {
            "check": self.name,
            "location": self.location,
            "holds": self.holds,
            "detail": self.detail,
        }


@dataclass
class CheckReport:
    holds: bool
    proof_method: str
    items: list[CheckItem] = field(default_factory=list)

    def failures(self) -> list[CheckItem]:
        return [i for i in self.items if not i.holds]

    def to_dict(self) -> dict:
        return {
            "holds": self.holds,
            "proof_method": self.proof_method,
            "checks": [i.to_dict() for i in self.items],
        }


# ---------------------------------------------------------------------------
# 独立的区间小运算（全部裸公式，不调用核心）
# ---------------------------------------------------------------------------
def _iv_subset(a: IV, b: IV) -> bool:
    """数学包含 a ⊆ b。"""
    alo, ahi = a
    blo, bhi = b
    lo_ok = blo is None or (alo is not None and alo >= blo)
    hi_ok = bhi is None or (ahi is not None and ahi <= bhi)
    return lo_ok and hi_ok


def _iv_hull(a: IV, b: IV) -> IV:
    alo, ahi = a
    blo, bhi = b
    return (
        None if alo is None or blo is None else min(alo, blo),
        None if ahi is None or bhi is None else max(ahi, bhi),
    )


def _iv_add_const(iv: IV, c: int) -> IV:
    lo, hi = iv
    return (None if lo is None else lo + c, None if hi is None else hi + c)


def _iv_le(iv: IV, c: int) -> Optional[IV]:
    lo, hi = iv
    if lo is not None and lo > c:
        return None
    return (lo, c if hi is None else min(hi, c))


def _iv_ge(iv: IV, c: int) -> Optional[IV]:
    lo, hi = iv
    if hi is not None and hi < c:
        return None
    return (c if lo is None else max(lo, c), hi)


def _env_from(entry_intervals: Optional[dict[str, IV]], program: Program) -> Env:
    """把 {var: (lo,hi)} 构造成完整环境；None/缺省按 bottom 处理。"""
    if entry_intervals is None:
        return None
    env: Env = {}
    for v in program.variables:
        if v not in entry_intervals:
            raise CheckViolation(f"环境缺少变量 {v!r} 的区间")
        iv = entry_intervals[v]
        if not (isinstance(iv, tuple) and len(iv) == 2):
            raise CheckViolation(f"变量 {v!r} 的区间必须是 (lo, hi) 二元组")
        lo, hi = iv
        if isinstance(lo, bool) or isinstance(hi, bool):
            raise CheckViolation(f"变量 {v!r} 端点不允许 bool")
        if lo is not None and not isinstance(lo, int):
            raise CheckViolation(f"变量 {v!r} 下端点非 int/None")
        if hi is not None and not isinstance(hi, int):
            raise CheckViolation(f"变量 {v!r} 上端点非 int/None")
        if lo is not None and hi is not None and lo > hi:
            raise CheckViolation(f"变量 {v!r} 区间 [{lo},{hi}] 非法")
        env[v] = (lo, hi)
    return env


def _env_subset(a: Env, b: Env) -> bool:
    """环境包含；bottom(None) 含于一切。"""
    if a is None:
        return True
    if b is None:
        return False
    return all(_iv_subset(a[v], b[v]) for v in a)


def _env_hull(a: Env, b: Env, variables: tuple[str, ...]) -> Env:
    if a is None:
        return b
    if b is None:
        return a
    return {v: _iv_hull(a[v], b[v]) for v in variables}


# ---------------------------------------------------------------------------
# 独立块转移（逐端点公式；assert 点同时记录观察区间）
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class BlockImage:
    exit_env: Env  # 语句执行完、分支前
    edges: dict[str, Env]  # 后继名 -> 过滤后环境（None=该边不可达）
    assert_observed: dict[str, IV]  # assert_id -> 断言点观察区间（None id 不用）


def compute_block_image(block: Block, entry_env: Env, program: Program) -> BlockImage:
    """独立重算块的精确抽象像（本仿射子集下端点精确）。"""
    if entry_env is None:
        return BlockImage(
            None, {s: None for s in block.successors}, {}
        )
    env: dict[str, IV] = dict(entry_env)
    observed: dict[str, IV] = {}
    for st in block.statements:
        if isinstance(st, Assign):
            env[st.var] = (st.value, st.value)
        elif isinstance(st, Copy):
            env[st.var] = env[st.src]
        elif isinstance(st, AddConst):
            env[st.var] = _iv_add_const(env[st.var], st.const)
        elif isinstance(st, AssertRange):
            observed[st.assert_id] = env[st.var]
        else:  # pragma: no cover - Program 构造已挡住
            raise CheckViolation(f"未知语句 {type(st).__name__}")

    edges: dict[str, Env] = {}
    br = block.branch
    if br is None:
        pass
    elif isinstance(br, Jump):
        edges[br.target] = dict(env)
    else:
        assert isinstance(br, Cond)
        if br.op == "<=":
            t = _iv_le(env[br.var], br.const)
            f = _iv_ge(env[br.var], br.const + 1)
        else:
            t = _iv_ge(env[br.var], br.const)
            f = _iv_le(env[br.var], br.const - 1)
        t_env: Env
        f_env: Env
        if t is None:
            t_env = None
        else:
            t_env = dict(env)
            t_env[br.var] = t
        if f is None:
            f_env = None
        else:
            f_env = dict(env)
            f_env[br.var] = f
        if br.taken == br.skipped:
            edges[br.taken] = _env_hull(t_env, f_env, tuple(env.keys()))
        else:
            edges[br.taken] = t_env
            edges[br.skipped] = f_env
    return BlockImage(dict(env), edges, observed)


# ---------------------------------------------------------------------------
# 公开检查入口
# ---------------------------------------------------------------------------
def check_block_transfer(
    program: Program,
    block_name: str,
    entry_intervals: dict[str, IV],
    claimed_edges: dict[str, Optional[dict[str, IV]]],
) -> CheckReport:
    """局部检查：块转移像 ⊆ 声称边状态。

    ``claimed_edges`` 给每个后继一个环境（``None`` 表示声称该边不可达）。
    这是纯局部证书检查：只有当块像的每条边环境都含于声称值时才成立。
    """
    report = CheckReport(holds=True, proof_method=PROOF_METHOD)
    if block_name not in program.block_map:
        raise CheckViolation(f"块 {block_name!r} 不存在")
    block = program.block_map[block_name]
    env = _env_from(entry_intervals, program)
    image = compute_block_image(block, env, program)

    for succ in block.successors:
        if succ not in claimed_edges:
            report.holds = False
            report.items.append(
                CheckItem(
                    "edge_claim_present",
                    f"{block_name}->{succ}",
                    False,
                    "声称边状态缺失",
                )
            )
            continue
        claimed = _env_from(claimed_edges[succ], program)
        actual = image.edges[succ]
        ok = _env_subset(actual, claimed)
        report.holds &= ok
        report.items.append(
            CheckItem(
                "edge_image_subset",
                f"{block_name}->{succ}",
                ok,
                f"实际边像 {_fmt(actual)} "
                + ("⊆" if ok else "⊄")
                + f" 声称 {_fmt(claimed)}",
            )
        )
    return report


def check_analysis(program: Program, result) -> CheckReport:
    """对 Analyzer 的结果做独立局部证书验收。

    验收：(a) 入口初值 ⊆ 入口块声称入不变量；(b) 每块入边凸包 ⊆
    该块声称入不变量（归纳条件）；(c) 每块声称入不变量经独立重算
    后的边像 ⊆ 结果给出的边状态（块条件）；(d) 每条 proved 断言在
    独立重算的断言点区间上确实包含于其声称范围。

    任何一项失败都给出可定位条目。全程符号证明，无采样。
    """
    report = CheckReport(holds=True, proof_method=PROOF_METHOD)

    def state_to_env(state) -> Env:
        d = state.to_dict(program)
        if d is None:
            return None
        return {v: (d[v]["lo"], d[v]["hi"]) for v in program.variables}

    claimed_in: dict[str, Env] = {
        b.name: state_to_env(result.in_states[b.name]) for b in program.blocks
    }
    claimed_edge: dict[tuple[str, str], Env] = {
        k: state_to_env(v) for k, v in result.edge_states.items()
    }

    # (a) 入口
    init = State_entry_env(program)
    ok = _env_subset(init, claimed_in[program.entry])
    report.holds &= ok
    report.items.append(
        CheckItem(
            "entry_init_subset",
            f"block:{program.entry}",
            ok,
            f"初值 {_fmt(init)} {'⊆' if ok else '⊄'} 入口不变量 {_fmt(claimed_in[program.entry])}",
        )
    )

    images: dict[str, BlockImage] = {}
    for block in program.blocks:
        image = compute_block_image(block, claimed_in[block.name], program)
        images[block.name] = image

        # (c) 块条件：边像 ⊆ 声称边状态
        for succ in block.successors:
            actual = image.edges[succ]
            claimed = claimed_edge[(block.name, succ)]
            ok = _env_subset(actual, claimed)
            report.holds &= ok
            report.items.append(
                CheckItem(
                    "block_edge_image_subset",
                    f"{block.name}->{succ}",
                    ok,
                    f"独立边像 {_fmt(actual)} {'⊆' if ok else '⊄'} 声称 {_fmt(claimed)}",
                )
            )

        # (d) proved 断言必须被独立重算的断言点区间包含性证实
        asserts = [s for s in block.statements if isinstance(s, AssertRange)]
        block_unreachable = claimed_in[block.name] is None
        for st in asserts:
            claimed_status = result.status_of(st.assert_id)
            if block_unreachable:
                really_holds = True
                detail = f"断言 {st.assert_id} 声称 proved/unknown；块不可达，空真"
            else:
                obs = image.assert_observed[st.assert_id]
                lo, hi = obs
                really_holds = lo is not None and lo >= st.lo and hi is not None and hi <= st.hi
                if claimed_status == "proved":
                    detail = f"断言 {st.assert_id} 声称 proved；独立观察 {_fmt_iv(obs)}"
                else:
                    detail = f"断言 {st.assert_id} 为 unknown（无证明义务）"
            if claimed_status == "proved":
                ok = really_holds
            else:
                ok = True  # unknown 是“不作承诺”，证书层面无义务
            report.holds &= ok
            report.items.append(
                CheckItem("assert_status_supported", f"{block.name}:{st.assert_id}", ok, detail)
            )

    # (b) 归纳条件：入边凸包 ⊆ 块声称入不变量
    for block in program.blocks:
        contribs: list[Env] = []
        if block.name == program.entry:
            contribs.append(init)
        for p in program.blocks:
            if (p.name, block.name) in claimed_edge:
                contribs.append(claimed_edge[(p.name, block.name)])
        if not contribs:
            join: Env = None
        else:
            join = contribs[0]
            for c in contribs[1:]:
                join = _env_hull(join, c, program.variables)
        ok = _env_subset(join, claimed_in[block.name])
        report.holds &= ok
        report.items.append(
            CheckItem(
                "inductive_invariant",
                f"block:{block.name}",
                ok,
                f"入边凸包 {_fmt(join)} {'⊆' if ok else '⊄'} 声称入不变量 {_fmt(claimed_in[block.name])}",
            )
        )

    return report


def State_entry_env(program: Program) -> Env:
    if program.entry_state is None:
        return {v: (0, 0) for v in program.variables}
    return {v: (c, c) for v, c in zip(program.variables, program.entry_state)}


def _fmt(env: Env) -> str:
    if env is None:
        return "BOTTOM"
    return "{" + ", ".join(f"{v}={_fmt_iv(env[v])}" for v in env) + "}"


def _fmt_iv(iv: IV) -> str:
    lo, hi = iv
    l = "-inf" if lo is None else str(lo)
    h = "+inf" if hi is None else str(hi)
    return f"[{l},{h}]"
