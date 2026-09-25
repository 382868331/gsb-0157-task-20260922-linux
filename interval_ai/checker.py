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
from itertools import product

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

# 标签槽位（独立重写，不导入 partitions 以免依赖被核的标签实现）：
# -1 = UNKNOWN（未经过/被合并抹除），0 = FALSE，1 = TRUE。
_SLOT_UNKNOWN = -1
_SLOT_FALSE = 0
_SLOT_TRUE = 1
_SLOT_ALL = (_SLOT_UNKNOWN, _SLOT_FALSE, _SLOT_TRUE)


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

        # 4) 每条边：守卫过滤后 ⊆ 后继入。
        #    分区模式下"先凸包再过滤"会丢失跨变量关联（这恰是分区要恢复的
        #    精度），故边包含改由第 6.3 节在细网格上逐分区检查；这里跳过。
        if not getattr(result, "partitioned", False):
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

    # 6) 分区模式：细网格转移包含性、cap 不变量、合并事件、逐分区断言复核
    if getattr(result, "partitioned", False):
        _check_partitions(result, cfg, report)
    return report


# -- 分区模式的独立健全性检查 --------------------------------------------------
#
# 本检查器**不导入** partitions/engine：标签（槽位 ?/F/T、冻结 gamma、
# "最近一次"覆写、逐槽泛化）全部在此按题面语义重新实现，只读结果对象里
# 的数据。证明仍是符号端点包含，不做任何枚举执行。


def _fine_labels(k: int):
    return tuple(product(_SLOT_ALL, repeat=k))


def _label_gamma(values, frozen) -> frozenset[tuple[int, ...]]:
    """粗标签的具体化细标签集合：冻结槽任取 ?/F/T，其余固定。"""
    options = [
        _SLOT_ALL if i in frozen else (v,)
        for i, v in enumerate(values)
    ]
    return frozenset(product(*options))


def _label_covers(coarse_values, frozen, fine_values) -> bool:
    for i, v in enumerate(coarse_values):
        if i not in frozen and fine_values[i] != v:
            return False
    return True


def _label_update(values, frozen, slot: int, outcome: int) -> tuple[int, ...]:
    out = list(values)
    if slot not in frozen:  # 冻结槽不被重新分裂
        out[slot] = outcome
    return tuple(out)


def _label_generalize(a_values, a_frozen, b_values, b_frozen):
    """逐槽泛化：一致保留，冲突槽抹 UNKNOWN 并冻结（独立参考规则）。"""
    values = list(a_values)
    frozen = set(a_frozen) | set(b_frozen)
    for i, (x, y) in enumerate(zip(a_values, b_values)):
        if i in frozen:
            values[i] = _SLOT_UNKNOWN
        elif x == y:
            values[i] = x
        else:
            values[i] = _SLOT_UNKNOWN
            frozen.add(i)
    return tuple(values), frozenset(frozen)


def _members_of(partition) -> dict:
    """把一个 PartitionedState 读成 {(values_tuple, frozenset): ref-env}。"""
    out = {}
    for label, state in partition.members.items():
        out[(tuple(label.values), frozenset(label.frozen))] = _from_abstract(state)
    return out


def _join_ref_envs(envs):
    acc = _BOTTOM
    for env in envs:
        if acc is _BOTTOM:
            acc = env
        elif env is not _BOTTOM:
            acc = {
                v: _ref_join_iv(acc[v], env[v]) for v in acc
            }
    return acc


def _check_partitions(result, cfg: CFG, report: CheckReport) -> None:
    points = tuple(result.track_guards)
    k = len(points)
    slot_of = {name: i for i, name in enumerate(points)}

    # 6.0) 分区点声明独立复核：<=3、块存在、恰为两路守卫
    if not 1 <= k <= 3:
        report.fail("track_guards", f"partition points must be 1..3, got {k}")
    for i, name in enumerate(points):
        bloc = f"track_guards[{i}]={name!r}"
        block = cfg.blocks.get(name)
        if block is None or block.guard is None or len(block.successors) != 2:
            report.fail(bloc, "partition point must be an existing 2-way guard block")

    pin = {n: _members_of(result.partition_in[n]) for n in cfg.blocks}
    pout = {n: _members_of(result.partition_out[n]) for n in cfg.blocks}

    def fail(loc, detail):
        report.fail(loc, detail)

    # 6.1) 标签结构合法性 + 每分区数不超过显式上限 + 凸包视图一致
    cap = result.max_partitions
    for name in cfg.blocks:
        bloc = f"block {name!r}.partitions"
        for key, env in pin[name].items():
            values, frozen = key
            if len(values) != k:
                fail(bloc, f"label {values} has wrong length {len(values)} != {k}")
            for v in values:
                if v not in _SLOT_ALL:
                    fail(bloc, f"illegal slot value in {values}")
            for i in frozen:
                if not (0 <= i < k) or values[i] != _SLOT_UNKNOWN:
                    fail(bloc, f"frozen slot {i} illegal in {values}/{sorted(frozen)}")
        if cap is not None and len(pin[name]) > cap:
            fail(bloc, f"{len(pin[name])} partitions exceed explicit cap {cap}")
        # 凸包视图必须恰好是各分区凸包（不删状态也不凭空放宽）
        hull = _join_ref_envs(list(pin[name].values()))
        core_hull = _from_abstract(result.block_in[name])
        if not _ref_state_subseteq(hull, core_hull):
            fail(bloc, "reported block-in hull does not contain partition join (state lost)")
        if not _ref_state_subseteq(core_hull, hull):
            fail(bloc, "reported block-in hull is coarser than partition join")
        hull_out = _join_ref_envs(list(pout[name].values()))
        core_hull_out = _from_abstract(result.block_out[name])
        if not _ref_state_subseteq(hull_out, core_hull_out):
            fail(f"{bloc}.out", "block-out hull does not contain partition join (state lost)")
        if not _ref_state_subseteq(core_hull_out, hull_out):
            fail(f"{bloc}.out", "reported block-out hull is coarser than partition join")

    # 6.2) 块内转移逐分区精确（标签不被语句改变；无"奇迹"赋值）
    for name, block in cfg.blocks.items():
        if set(pin[name]) != set(pout[name]):
            fail(f"block {name!r}.partitions",
                 "partition labels must be preserved by intra-block statements")
        for key, env_in in pin[name].items():
            env = env_in
            for stmt in block.statements:
                env = _ref_transfer_stmt(env, stmt)
            if not _ref_state_subseteq(env, pout[name][key]):
                fail(f"block {name!r}.partitions[{_label_text(key)}].out",
                     "partition block-out does not contain reference image (unsound)")
            if not _ref_state_subseteq(pout[name][key], env):
                fail(f"block {name!r}.partitions[{_label_text(key)}].out",
                     "partition block-out is coarser than reference image")

    # 6.3) 边包含（细网格）：源粗分区先过边（过滤+覆写，冻结槽不分裂），
    #      gamma 展开后每个细格必须被后继块某个覆盖它的粗分区包含。
    # 入口：全 ? 初始细标签必须被入口分区覆盖。
    initial = {
        v: (cfg.entry_bounds[v].lower, cfg.entry_bounds[v].upper)
        if v in cfg.entry_bounds else (None, None)
        for v in cfg.variables
    }
    entry_q = (_SLOT_UNKNOWN,) * k
    entry_hosts = [env for key, env in pin[cfg.entry].items()
                   if _label_covers(key[0], key[1], entry_q)]
    if not entry_hosts or not _ref_state_subseteq(
        initial, _join_ref_envs(entry_hosts)
    ):
        fail(f"block {cfg.entry!r}.partitions",
             "declared entry bounds not contained in partition(s) covering all-? label")

    for name, block in cfg.blocks.items():
        slot = slot_of.get(name)
        for edge_i, succ in enumerate(block.successors):
            taken = edge_i == 0
            for key, env in pout[name].items():
                values, frozen = key
                edge_env = _ref_filter_guard(env, block.guard, taken) \
                    if block.guard is not None else env
                if edge_env is _BOTTOM:
                    continue
                if slot is not None and block.guard is not None:
                    after = _label_update(values, frozen, slot,
                                          _SLOT_TRUE if taken else _SLOT_FALSE)
                    after_frozen = frozen
                else:
                    after, after_frozen = values, frozen
                for g in _label_gamma(after, after_frozen):
                    hosts = [env2 for key2, env2 in pin[succ].items()
                             if _label_covers(key2[0], key2[1], g)]
                    if not hosts:
                        fail(f"block {name!r}.partitions[{_label_text(key)}] -> {succ!r}",
                             f"fine flow {_tuple_text(g)} has no receiving partition (state lost)")
                        continue
                    if not _ref_state_subseteq(edge_env, _join_ref_envs(hosts)):
                        side = "true" if taken else "false"
                        fail(f"block {name!r}.successors[{edge_i}]({side}) -> {succ!r} "
                             f"fine {_tuple_text(g)}",
                             "edge flow not contained in receiving partition(s) (unsound)")

    # 6.4) 合并事件结构复核：幸存标签=dropped 的独立逐槽泛化；
    #      dropped 的 gamma 全部被幸存标签覆盖（只丢标签、不丢状态）；
    #      幸存标签冻结槽值为 UNKNOWN；partitions_after 合法。
    for ev in result.merges:
        loc = f"merge@{ev.block!r}"
        if ev.block not in cfg.blocks:
            fail(loc, "unknown block")
            continue
        if ev.round < 1 or ev.partitions_after < 1:
            fail(loc, f"illegal event round/after: {ev.round}/{ev.partitions_after}")
        dropped = [(tuple(d.values), frozenset(d.frozen)) for d in ev.dropped]
        if len(set(dropped)) != len(dropped) or len(dropped) < 2:
            fail(loc, "merge must combine >=2 distinct labels")
        surv_values, surv_frozen = tuple(ev.surviving.values), frozenset(ev.surviving.frozen)
        acc_v, acc_f = dropped[0]
        for dv, df in dropped[1:]:
            acc_v, acc_f = _label_generalize(acc_v, acc_f, dv, df)
        if (acc_v, acc_f) != (surv_values, surv_frozen):
            fail(loc, f"surviving label {_tuple_text(surv_values)}/f{sorted(surv_frozen)} "
                      f"!= independent generalization {_tuple_text(acc_v)}/f{sorted(acc_f)}")
        for dv, df in dropped:
            for g in _label_gamma(dv, df):
                if not _label_covers(surv_values, surv_frozen, g):
                    fail(loc, f"dropped fine flow {_tuple_text(g)} not covered by survivor "
                              "(merge would delete state)")
        if len(result.partition_in[ev.block].members) > (result.max_partitions or 0):
            fail(loc, "block still over cap after merge")

    # 6.5) 逐分区断言独立复核：每个可达分区观测符号包含于要求区间；
    #      明细集合与逐分区前缀转移一致；空真仅在无任何可达分区时给出。
    for st in result.asserts:
        loc = f"block {st.block!r}.assert[{st.index}]"
        block = cfg.blocks[st.block]
        # 用独立参考转移把各分区推进到该语句位置
        per: dict[tuple, object] = {}
        for key, env0 in pin[st.block].items():
            env = env0
            for stmt in block.statements[: st.index]:
                env = _ref_transfer_stmt(env, stmt)
            per[key] = env
        if not per:
            if not (st.verdict == "proved" and st.vacuous):
                fail(loc, "unreachable assert must be proved+vacuous")
            continue
        if st.vacuous:
            fail(loc, "reachable assert must not be marked vacuous")
        details = {(p.label): (p.observed.lower, p.observed.upper)
                   for p in getattr(st, "partitions", ())}
        if set(details) != {_label_text(key) for key in per}:
            fail(loc, "partition observation label set does not match reachable partitions")
        required: Bound = (st.statement.lower, st.statement.upper)
        for key, env in per.items():
            obs = env[st.statement.target]
            text = _label_text(key)
            if text in details and not _ref_iv_subseteq(details[text], obs):
                fail(loc, f"reported partition {text} observation is coarser than prefix image")
            if text in details and not _ref_iv_subseteq(obs, details[text]):
                fail(loc, f"reported partition {text} observation loses precision vs prefix image")
            if st.verdict == "proved" and not _ref_iv_subseteq(obs, required):
                fail(loc, f"marked proved but partition {text} observes {obs} not in {required}")
        if st.verdict == "unknown" and all(
            _ref_iv_subseteq(env[st.statement.target], required) for env in per.values()
        ):
            fail(loc, "all partitions are provable but verdict is unknown (incomplete verdict)")


def _label_text(key) -> str:
    mapping = {_SLOT_UNKNOWN: "?", _SLOT_FALSE: "F", _SLOT_TRUE: "T"}
    values, frozen = key
    return ".".join("x" if i in frozen else mapping[v] for i, v in enumerate(values))


def _tuple_text(values) -> str:
    mapping = {_SLOT_UNKNOWN: "?", _SLOT_FALSE: "F", _SLOT_TRUE: "T"}
    return ".".join(mapping[v] for v in values)
