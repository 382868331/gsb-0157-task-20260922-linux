"""不动点引擎：延迟加宽的上升迭代 + 收窄迭代（区间域 / 区间×差分区简约积）。

策略（本题契约）：

* 加宽点 = 回边目标块（DFS 染色判定回边）。
* 每个加宽点的**前两次扩张取凸包（join），第三次扩张起使用标准加宽**
  （区间端点被突破即推到无穷；DBM 表项被突破即放到 +∞）。
* 上升序列达到后置不动点（一轮内无任何变化）后，做**至多 8 轮**收窄，
  提前稳定则提前停止。
* 含差分约束语句（AssumeDiff/AssertDiff）的 CFG 走**区间 × DBM 简约积**
  引擎：两域在每条语句、每次合流、每条守卫边后交换信息。
* 关系域设有**显式迭代预算** ``loop_budget``：预算内未收敛时不冒充证明，
  本次分析退回到纯区间结果（区间结论照常给出），所有差分断言记
  ``unknown``，结果上以 ``relational_converged=False`` 明确标记。
* 防御性安全阀 ``ascending_budget`` 耗尽仍抛
  :class:`BudgetExhaustedError`，与数据结论 unknown 严格区分。

枚举顺序为入口可达部分的逆后序（RPO），并列时按 ``CFG.blocks`` 插入顺序，
保证结果确定；入口不可达块保持 bottom。
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
)
from .diffs import DiffState
from .errors import BudgetExhaustedError
from .intervals import AbstractState, Interval
from .relational import (
    ProductState,
    edge_state_rel,
    transfer_block_rel,
    transfer_statement_rel,
)
from .transfer import edge_state, transfer_block, transfer_statement

MAX_NARROWING_ROUNDS = 8
DEFAULT_ASCENDING_BUDGET = 10000
# 关系域（DBM）上升迭代的显式预算：矩阵至多 5×5 且加宽保证链有限，
# 实际收敛只需个位数轮次；该预算是"未收敛即 unknown"的明确界限。
DEFAULT_LOOP_BUDGET = 256


# -- 图分析：回边 / 加宽点 / RPO / 前驱表 -------------------------------------

def _dfs_back_edges_and_order(cfg: CFG) -> tuple[list[tuple[str, str]], list[str]]:
    """返回 (回边列表 (源, 目标), 入口可达块的后序)。

    经典三色 DFS：遇到灰色（在当前递归栈中）节点即回边。
    """
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {name: WHITE for name in cfg.blocks}
    back_edges: list[tuple[str, str]] = []
    postorder: list[str] = []

    def visit(name: str) -> None:
        color[name] = GRAY
        for succ in cfg.blocks[name].successors:
            if color[succ] == WHITE:
                visit(succ)
            elif color[succ] == GRAY:
                back_edges.append((name, succ))
        color[name] = BLACK
        postorder.append(name)

    visit(cfg.entry)
    return back_edges, postorder


def _natural_loop(cfg: CFG, src: str, head: str) -> set[str]:
    """回边 (src -> head) 的自然循环：{head} ∪ 不经过 head 能到达 src 的节点。

    反向遍历前驱；head 计入集合但不从它继续扩展（单入口 while 循环）。
    """
    loop = {head, src}
    work = [src]
    while work:
        node = work.pop()
        for pname, block in cfg.blocks.items():
            if node in block.successors and pname not in loop:
                loop.add(pname)
                if pname != head:
                    work.append(pname)
    return loop


def _assigned_target(stmt) -> str | None:
    if isinstance(stmt, (AssignConst, AssignCopy, AssignAdd)):
        return stmt.target
    return None  # AssertRange / AssumeDiff / AssertDiff 都不修改变量


def _widened_variables(cfg: CFG, back_edges: list[tuple[str, str]]) -> dict[str, set[str]]:
    """每个加宽点：其自然循环内被赋值语句修改的变量集合。

    只加宽"在该循环里真正被修改"的变量；仅从循环外流入、循环内不改的
    变量取精确凸包——这是嵌套循环下保持精度且不破坏终止性的标准处理：
    这类变量沿该加宽点的迭代链由外层不动点决定，本身不发散。
    """
    result: dict[str, set[str]] = {}
    by_head: dict[str, list[str]] = {}
    for src, head in back_edges:
        by_head.setdefault(head, []).append(src)
    for head, srcs in by_head.items():
        nodes: set[str] = set()
        for src in srcs:
            nodes |= _natural_loop(cfg, src, head)
        modified: set[str] = set()
        for n in nodes:
            for st in cfg.blocks[n].statements:
                target = _assigned_target(st)
                if target is not None:
                    modified.add(target)
        result[head] = modified
    return result


def _reverse_postorder(cfg: CFG) -> tuple[list[str], set[str]]:
    back_edges, postorder = _dfs_back_edges_and_order(cfg)
    reachable = list(reversed(postorder))
    back_heads = {dst for _, dst in back_edges}
    order = reachable + [n for n in cfg.blocks if n not in set(reachable)]
    return order, back_heads


def _predecessors(cfg: CFG) -> dict[str, list[tuple[str, int]]]:
    preds: dict[str, list[tuple[str, int]]] = {n: [] for n in cfg.blocks}
    for name, block in cfg.blocks.items():
        for i, succ in enumerate(block.successors):
            preds[succ].append((name, i))
    return preds


def _uses_diff(cfg: CFG) -> bool:
    return any(
        isinstance(st, (AssumeDiff, AssertDiff))
        for block in cfg.blocks.values()
        for st in block.statements
    )


# -- 结果结构 -----------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class AssertStatus:
    block: str
    index: int
    statement: AssertRange
    verdict: str  # "proved" | "unknown"
    observed: Interval | None  # 分析到的实际区间；不可达位置为 None
    vacuous: bool = False  # 位置不可达，空真成立

    def to_dict(self) -> dict[str, object]:
        d: dict[str, object] = {
            "block": self.block,
            "index": self.index,
            "target": self.statement.target,
            "required": [self.statement.lower, self.statement.upper],
            "verdict": self.verdict,
        }
        if self.observed is None:
            d["observed"] = None
            d["vacuous"] = self.vacuous
        else:
            d["observed"] = self.observed.to_dict()
            d["vacuous"] = self.vacuous
        return d


@dataclass(frozen=True, slots=True)
class DiffAssertStatus:
    """单条 AssertDiff 的结论；``observed_bound`` 为推出的最紧上界。"""

    block: str
    index: int
    statement: AssertDiff
    verdict: str  # "proved" | "unknown"
    observed_bound: int | None  # DBM 中 left-right 的最紧上界；不可达位置为 None
    vacuous: bool = False

    def to_dict(self) -> dict[str, object]:
        s = self.statement
        return {
            "block": self.block,
            "index": self.index,
            "left": s.left,
            "right": s.right,
            "const": s.const,
            "required": [s.left, s.right, s.const],
            "verdict": self.verdict,
            "observed_bound": self.observed_bound,
            "vacuous": self.vacuous,
        }


@dataclass(frozen=True, slots=True)
class AnalysisResult:
    cfg: CFG
    block_in: dict[str, AbstractState]
    block_out: dict[str, AbstractState]
    asserts: list[AssertStatus] = field(default_factory=list)
    widen_points: tuple[str, ...] = ()
    ascending_rounds: int = 0
    narrowing_rounds: int = 0
    # 收窄前（上升迭代刚稳定时）的快照，用于验证收窄确实带来了改善
    post_widening_in: dict[str, AbstractState] = field(default_factory=dict)
    post_widening_out: dict[str, AbstractState] = field(default_factory=dict)
    # --- 关系域（区间 × 差分约束简约积）附加信息 ---
    relational_enabled: bool = False
    # True = 关系迭代在预算内收敛；False = 未收敛，已退回纯区间，diff 结论 unknown
    relational_converged: bool = True
    relational_budget: int = 0
    diff_asserts: list[DiffAssertStatus] = field(default_factory=list)
    block_in_diff: dict[str, DiffState] = field(default_factory=dict)
    block_out_diff: dict[str, DiffState] = field(default_factory=dict)
    post_widening_diff_in: dict[str, DiffState] = field(default_factory=dict)
    post_widening_diff_out: dict[str, DiffState] = field(default_factory=dict)

    @property
    def narrowing_refined(self) -> bool:
        if self.block_in != self.post_widening_in or self.block_out != self.post_widening_out:
            return True
        if self.relational_enabled and (
            self.block_in_diff != self.post_widening_diff_in
            or self.block_out_diff != self.post_widening_diff_out
        ):
            return True
        return False

    def state_at(self, block: str) -> AbstractState:
        return self.block_in[block]

    def diff_state_at(self, block: str) -> DiffState:
        """该块入口的 DBM 状态；仅收敛的关系分析可用。"""
        if not self.relational_enabled:
            raise ValueError(
                "diff states are only available on a relational analysis "
                "(a CFG containing AssumeDiff/AssertDiff)"
            )
        if not self.relational_converged:
            raise ValueError(
                "relational iteration did not converge within loop_budget; "
                "no diff invariant is available (diff asserts are unknown)"
            )
        return self.block_in_diff[block]

    def to_dict(self) -> dict[str, object]:
        d: dict[str, object] = {
            "entry": self.cfg.entry,
            "widen_points": list(self.widen_points),
            "ascending_rounds": self.ascending_rounds,
            "narrowing_rounds": self.narrowing_rounds,
            "blocks": {
                name: {
                    "in": self.block_in[name].to_dict(),
                    "out": self.block_out[name].to_dict(),
                }
                for name in self.cfg.blocks
            },
            "asserts": [a.to_dict() for a in self.asserts],
        }
        if self.relational_enabled:
            rel: dict[str, object] = {
                "converged": self.relational_converged,
                "loop_budget": self.relational_budget,
                "diff_asserts": [a.to_dict() for a in self.diff_asserts],
            }
            if self.relational_converged:
                rel["diff_blocks"] = {
                    name: {
                        "in": self.block_in_diff[name].to_dict(),
                        "out": self.block_out_diff[name].to_dict(),
                    }
                    for name in self.cfg.blocks
                }
            d["relational"] = rel
        return d


# -- 纯区间引擎（原有行为，逐字保留） -------------------------------------------

def _initial_entry_state(cfg: CFG) -> AbstractState:
    return AbstractState(cfg.variable_tuple, cfg.initial_state_intervals(), False)


def _join_inputs(
    cfg: CFG,
    name: str,
    outs: dict[str, AbstractState],
    preds: dict[str, list[tuple[str, int]]],
    include_initial: bool,
) -> AbstractState:
    """方程右端：各前驱出状态经边守卫过滤后的凸包（入口并入初始状态）。"""
    acc = (
        _initial_entry_state(cfg)
        if include_initial and name == cfg.entry
        else AbstractState.bottom_of(cfg.variable_tuple)
    )
    for pname, edge_index in preds[name]:
        acc = acc.join(edge_state(outs[pname], cfg.blocks[pname], edge_index))
    return acc


def _analyze_intervals(cfg: CFG, ascending_budget: int) -> AnalysisResult:
    order, widen_points = _reverse_postorder(cfg)
    back_edges, _ = _dfs_back_edges_and_order(cfg)
    widened_vars = _widened_variables(cfg, back_edges)
    preds = _predecessors(cfg)
    variables = cfg.variable_tuple
    bottom = AbstractState.bottom_of(variables)

    ins: dict[str, AbstractState] = {n: bottom for n in cfg.blocks}
    outs: dict[str, AbstractState] = {n: bottom for n in cfg.blocks}
    # 每个加宽点已经历的"扩张"次数（前两次 join，第三次起 widen）
    expansions = {n: 0 for n in widen_points}

    # -- 上升迭代 -------------------------------------------------------------
    rounds = 0
    for rounds in range(1, ascending_budget + 1):
        changed = False
        for name in order:
            candidate = _join_inputs(cfg, name, outs, preds, True)
            current = ins[name]
            if name in widen_points:
                if candidate.subseteq(current):
                    new_in = current
                else:
                    expansions[name] += 1
                    if expansions[name] <= 2:
                        # 前两次扩张：凸包（延迟加宽）
                        new_in = current.join(candidate)
                    else:
                        # 第三次扩张起：仅对该循环内被修改的变量标准 widening，
                        # 其余变量取精确凸包（先凸包保证 self ⊆ other）。
                        new_in = current.widen_selective(
                            current.join(candidate), widened_vars[name]
                        )
            else:
                new_in = candidate if current.bottom else current.join(candidate)
            new_out = transfer_block(new_in, cfg.blocks[name])
            if new_in != current or new_out != outs[name]:
                changed = True
            ins[name] = new_in
            outs[name] = new_out
        if not changed:
            break
    else:
        raise BudgetExhaustedError(
            f"ascending iteration did not stabilize within {ascending_budget} rounds",
            rounds=ascending_budget,
            partial={"block_in": ins, "block_out": outs},
        )

    # -- 收窄迭代（至多 MAX_NARROWING_ROUNDS 轮）------------------------------
    post_widening_in = {n: ins[n] for n in order}
    post_widening_out = {n: outs[n] for n in order}
    narrow_rounds = 0
    for narrow_rounds in range(1, MAX_NARROWING_ROUNDS + 1):
        changed = False
        new_ins: dict[str, AbstractState] = {}
        new_outs: dict[str, AbstractState] = {}
        for name in order:
            # 同一轮内已更新的前驱立即生效（混沌收窄）
            visible_outs = {**outs, **new_outs}
            candidate = _join_inputs(cfg, name, visible_outs, preds, True)
            current = ins[name]
            if name in widen_points:
                new_in = (
                    current.narrow_selective(candidate, widened_vars[name])
                    if not current.bottom
                    else current
                )
            else:
                new_in = candidate
            new_out = transfer_block(new_in, cfg.blocks[name])
            if new_in != ins[name] or new_out != outs[name]:
                changed = True
            new_ins[name] = new_in
            new_outs[name] = new_out
        ins, outs = new_ins, new_outs
        if not changed:
            break

    return AnalysisResult(
        cfg=cfg,
        block_in=ins,
        block_out=outs,
        asserts=_evaluate_asserts(cfg, ins),
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in=post_widening_in,
        post_widening_out=post_widening_out,
    )


# -- 区间 × 差分 简约积引擎 ----------------------------------------------------

def _initial_product(cfg: CFG) -> ProductState:
    return ProductState.initial(cfg)


def _product_bottom(cfg: CFG) -> ProductState:
    return ProductState.bottom_of(cfg.variable_tuple)


def _join_inputs_rel(
    cfg: CFG,
    name: str,
    outs: dict[str, ProductState],
    preds: dict[str, list[tuple[str, int]]],
) -> ProductState:
    """积方程右端：入口并入初始积状态，其余为前驱出状态经守卫边过滤后合流。"""
    acc = _initial_product(cfg) if name == cfg.entry else _product_bottom(cfg)
    for pname, edge_index in preds[name]:
        acc = acc.join(
            edge_state_rel(outs[pname], cfg.blocks[pname], edge_index)
        )
    return acc


def _project_intervals(prods: dict[str, ProductState]) -> dict[str, AbstractState]:
    return {n: p.intervals for n, p in prods.items()}


def _project_diffs(prods: dict[str, ProductState]) -> dict[str, DiffState]:
    return {n: p.diffs for n, p in prods.items()}


def _analyze_relational(
    cfg: CFG,
    ascending_budget: int,
    loop_budget: int,
) -> AnalysisResult:
    order, widen_points = _reverse_postorder(cfg)
    back_edges, _ = _dfs_back_edges_and_order(cfg)
    widened_vars = _widened_variables(cfg, back_edges)
    preds = _predecessors(cfg)
    bottom = _product_bottom(cfg)

    ins: dict[str, ProductState] = {n: bottom for n in cfg.blocks}
    outs: dict[str, ProductState] = {n: bottom for n in cfg.blocks}
    expansions = {n: 0 for n in widen_points}
    converged = False

    # 上升预算同时受 loop_budget（未收敛 -> unknown）与防御性
    # ascending_budget（理论不可达，触发即 BudgetExhaustedError）约束。
    effective_budget = min(loop_budget, ascending_budget)
    rounds = 0
    for rounds in range(1, effective_budget + 1):
        changed = False
        for name in order:
            candidate = _join_inputs_rel(cfg, name, outs, preds)
            current = ins[name]
            if name in widen_points:
                if candidate.subseteq(current):
                    new_in = current
                else:
                    expansions[name] += 1
                    if expansions[name] <= 2:
                        new_in = current.join(candidate)
                    else:
                        # 加宽后立即做一次域间简约（含 DBM 重新闭包），
                        # 保证存下来的加宽点不变量是规范闭矩阵。
                        new_in = current.widen_selective(
                            current.join(candidate), widened_vars[name]
                        )
                        if not new_in.bottom:
                            new_in = new_in._reduce()
            else:
                new_in = candidate if current.bottom else current.join(candidate)
            new_out = transfer_block_rel(new_in, cfg.blocks[name])
            if new_in != current or new_out != outs[name]:
                changed = True
            ins[name] = new_in
            outs[name] = new_out
        if not changed:
            converged = True
            break

    if not converged:
        if ascending_budget < loop_budget:
            # 防御性安全阀先于显式循环预算成为约束：维持旧的严格语义。
            raise BudgetExhaustedError(
                f"ascending iteration did not stabilize within {ascending_budget} rounds",
                rounds=ascending_budget,
                partial={
                    "block_in": _project_intervals(ins),
                    "block_out": _project_intervals(outs),
                },
            )
        # 题面行为：显式循环预算内未收敛不冒充证明 —— 退回纯区间结果，
        # 差分断言全部 unknown。
        return _fallback_interval_result(
            cfg, ascending_budget, loop_budget, rounds
        )

    # -- 收窄迭代（至多 MAX_NARROWING_ROUNDS 轮，混沌）------------------------
    post_in, post_out = dict(ins), dict(outs)
    narrow_rounds = 0
    for narrow_rounds in range(1, MAX_NARROWING_ROUNDS + 1):
        changed = False
        new_ins: dict[str, ProductState] = {}
        new_outs: dict[str, ProductState] = {}
        for name in order:
            visible_outs = {**outs, **new_outs}
            candidate = _join_inputs_rel(cfg, name, visible_outs, preds)
            current = ins[name]
            if name in widen_points:
                new_in = (
                    current.narrow_selective(candidate, widened_vars[name])
                    if not current.bottom
                    else current
                )
            else:
                new_in = candidate
            new_out = transfer_block_rel(new_in, cfg.blocks[name])
            if new_in != ins[name] or new_out != outs[name]:
                changed = True
            new_ins[name] = new_in
            new_outs[name] = new_out
        ins, outs = new_ins, new_outs
        if not changed:
            break

    range_asserts, diff_asserts = _evaluate_asserts_rel(cfg, ins)
    return AnalysisResult(
        cfg=cfg,
        block_in=_project_intervals(ins),
        block_out=_project_intervals(outs),
        asserts=range_asserts,
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in=_project_intervals(post_in),
        post_widening_out=_project_intervals(post_out),
        relational_enabled=True,
        relational_converged=True,
        relational_budget=loop_budget,
        diff_asserts=diff_asserts,
        block_in_diff=_project_diffs(ins),
        block_out_diff=_project_diffs(outs),
        post_widening_diff_in=_project_diffs(post_in),
        post_widening_diff_out=_project_diffs(post_out),
    )


def _fallback_interval_result(
    cfg: CFG,
    ascending_budget: int,
    loop_budget: int,
    reached_rounds: int,
) -> AnalysisResult:
    """关系迭代未在预算内收敛：运行纯区间引擎并把差分断言判为 unknown。

    纯区间结果是健全的过近似（AssumeDiff 被当作无信息约束，只会更粗，不会
    漏掉可达状态）；区间可证的断言照常 proved，差分断言一律 unknown，
    不可达位置仍按空真 proved 标记。
    """
    base = _analyze_intervals(cfg, ascending_budget)
    range_asserts, diff_asserts = _evaluate_asserts_rel_fallback(cfg, base.block_in)
    return AnalysisResult(
        cfg=cfg,
        block_in=base.block_in,
        block_out=base.block_out,
        asserts=range_asserts,
        widen_points=base.widen_points,
        ascending_rounds=reached_rounds,
        narrowing_rounds=base.narrowing_rounds,
        post_widening_in=base.post_widening_in,
        post_widening_out=base.post_widening_out,
        relational_enabled=True,
        relational_converged=False,
        relational_budget=loop_budget,
        diff_asserts=diff_asserts,
    )


# -- 断言评估 -----------------------------------------------------------------

def _evaluate_asserts(
    cfg: CFG, ins: dict[str, AbstractState]
) -> list[AssertStatus]:
    statuses: list[AssertStatus] = []
    for name in cfg.blocks:
        block: Block = cfg.blocks[name]
        state = ins[name]
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                if state.bottom:
                    statuses.append(
                        AssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    observed = state.get(stmt.target)
                    required = Interval(stmt.lower, stmt.upper)
                    verdict = "proved" if observed.subseteq(required) else "unknown"
                    statuses.append(
                        AssertStatus(name, i, stmt, verdict, observed, False)
                    )
            else:
                # 推进到下一语句前的状态
                state = transfer_statement(state, stmt)
    return statuses


def _diff_status(
    name: str, i: int, stmt: AssertDiff, state: ProductState
) -> DiffAssertStatus:
    if state.bottom:
        return DiffAssertStatus(name, i, stmt, "proved", None, vacuous=True)
    bound = state.diffs.bound_of(stmt.left, stmt.right)
    verdict = "proved" if state.diffs.implies(stmt.left, stmt.right, stmt.const) else "unknown"
    return DiffAssertStatus(name, i, stmt, verdict, bound, False)


def _evaluate_asserts_rel(
    cfg: CFG, ins: dict[str, ProductState]
) -> tuple[list[AssertStatus], list[DiffAssertStatus]]:
    range_statuses: list[AssertStatus] = []
    diff_statuses: list[DiffAssertStatus] = []
    for name in cfg.blocks:
        block: Block = cfg.blocks[name]
        state = ins[name]
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                if state.bottom:
                    range_statuses.append(
                        AssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    observed = state.intervals.get(stmt.target)
                    required = Interval(stmt.lower, stmt.upper)
                    verdict = "proved" if observed.subseteq(required) else "unknown"
                    range_statuses.append(
                        AssertStatus(name, i, stmt, verdict, observed, False)
                    )
                continue
            if isinstance(stmt, AssertDiff):
                diff_statuses.append(_diff_status(name, i, stmt, state))
                continue
            state = transfer_statement_rel(state, stmt)
    return range_statuses, diff_statuses


def _evaluate_asserts_rel_fallback(
    cfg: CFG, ins: dict[str, AbstractState]
) -> tuple[list[AssertStatus], list[DiffAssertStatus]]:
    """未收敛回退路径：区间断言按区间状态判定，差分断言（非空真）一律 unknown。"""
    range_statuses: list[AssertStatus] = []
    diff_statuses: list[DiffAssertStatus] = []
    for name in cfg.blocks:
        block: Block = cfg.blocks[name]
        state = ins[name]
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                if state.bottom:
                    range_statuses.append(
                        AssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    observed = state.get(stmt.target)
                    required = Interval(stmt.lower, stmt.upper)
                    verdict = "proved" if observed.subseteq(required) else "unknown"
                    range_statuses.append(
                        AssertStatus(name, i, stmt, verdict, observed, False)
                    )
                continue
            if isinstance(stmt, AssertDiff):
                if state.bottom:
                    diff_statuses.append(
                        DiffAssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    diff_statuses.append(
                        DiffAssertStatus(name, i, stmt, "unknown", None, False)
                    )
                continue
            state = transfer_statement(state, stmt)
    return range_statuses, diff_statuses


# -- 公开入口 -----------------------------------------------------------------

def analyze(
    cfg: CFG,
    *,
    ascending_budget: int = DEFAULT_ASCENDING_BUDGET,
    loop_budget: int = DEFAULT_LOOP_BUDGET,
) -> AnalysisResult:
    """对 ``cfg`` 运行抽象解释，返回每块入/出不变量与断言结论。

    :param ascending_budget: 防御性迭代上限；耗尽抛
        :class:`BudgetExhaustedError`（不是证明结论）。
    :param loop_budget: 关系域（区间 × 差分约束）显式迭代预算；含差分语句
        的程序若在该预算内未收敛到不动点，本次分析退回纯区间结果，所有
        差分断言给 ``unknown``，结果标记 ``relational_converged=False``。
    """
    if isinstance(ascending_budget, bool) or not isinstance(ascending_budget, int):
        raise TypeError("ascending_budget must be int")
    if ascending_budget < 1:
        raise ValueError("ascending_budget must be >= 1")
    if isinstance(loop_budget, bool) or not isinstance(loop_budget, int):
        raise TypeError("loop_budget must be int")
    if loop_budget < 1:
        raise ValueError("loop_budget must be >= 1")

    if _uses_diff(cfg):
        return _analyze_relational(cfg, ascending_budget, loop_budget)
    return _analyze_intervals(cfg, ascending_budget)
