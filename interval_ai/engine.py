"""区间不动点引擎：延迟加宽的上升迭代 + 收窄迭代。

策略（本题契约）：

* 加宽点 = 回边目标块（DFS 染色判定回边）。
* 每个加宽点的**前两次扩张取凸包（join），第三次扩张起使用标准区间
  widening**（端点被突破即推到无穷）。
* 上升序列达到后置不动点（一轮内无任何变化）后，做**至多 8 轮**收窄，
  提前稳定则提前停止。
* 迭代预算耗尽抛 :class:`BudgetExhaustedError`，与断言 unknown 严格区分。

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
from .dbm import (
    DiffState,
    ProductState,
    edge_state_product,
    transfer_block_product,
    transfer_statement_product,
)
from .errors import BudgetExhaustedError
from .intervals import AbstractState, Interval
from .transfer import edge_state, transfer_block, transfer_statement

MAX_NARROWING_ROUNDS = 8
DEFAULT_ASCENDING_BUDGET = 10000
# 关系（差分约束）不动点的显式上升轮数预算；超时不冒充证明：关系域整体
# 放弃（退化为纯区间重跑），所有差分断言给 unknown，并置 relation_truncated。
DEFAULT_RELATION_BUDGET = 10000


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
                # 只有赋值类语句写变量；AssertRange 只读，
                # AssumeDiff/AssertDiff 不写入任何变量。
                if isinstance(st, (AssignConst, AssignCopy, AssignAdd)):
                    modified.add(st.target)
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
    """差分约束断言 ``a - b <= c`` 的结论。

    :param observed_bound: 关系域符号推出的最紧上界；推不出为 ``None``。
    :param vacuous: 断言位置不可达，空真成立。
    """

    block: str
    index: int
    statement: AssertDiff
    verdict: str  # "proved" | "unknown"
    observed_bound: int | None
    vacuous: bool = False

    def to_dict(self) -> dict[str, object]:
        s = self.statement
        return {
            "block": self.block,
            "index": self.index,
            "required": [s.a, s.b, s.const],
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
    # --- 差分约束（关系域）扩展；cfg.uses_diff_domain 为 False 时为空/None ---
    # 每个块的关系入/出不变量（差界矩阵的公开视图）。
    diff_in: dict[str, DiffState] | None = None
    diff_out: dict[str, DiffState] | None = None
    # 差分断言结论（AssertDiff 一条一个）。
    diff_asserts: list[DiffAssertStatus] = field(default_factory=list)
    # 关系域是否因迭代预算未收敛而被整体放弃（此时 diff_* 为 None 形态，
    # 所有差分断言为 unknown；区间结论仍然健全）。
    relation_truncated: bool = False
    relation_rounds: int = 0

    @property
    def narrowing_refined(self) -> bool:
        return self.block_in != self.post_widening_in or self.block_out != self.post_widening_out

    def state_at(self, block: str) -> AbstractState:
        return self.block_in[block]

    def diff_at(self, block: str) -> DiffState | None:
        """该块入状态的关系视图；未启用关系域时为 ``None``。"""
        if self.diff_in is None:
            return None
        return self.diff_in[block]

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
        if self.cfg.uses_diff_domain:
            d["relation_truncated"] = self.relation_truncated
            d["relation_rounds"] = self.relation_rounds
            if self.diff_in is not None:
                d["diff_blocks"] = {
                    name: {
                        "in": self.diff_in[name].to_dict(),
                        "out": self.diff_out[name].to_dict(),
                    }
                    for name in self.cfg.blocks
                }
            else:
                d["diff_blocks"] = None
            d["diff_asserts"] = [a.to_dict() for a in self.diff_asserts]
        return d


# -- 引擎 ---------------------------------------------------------------------

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


def analyze(
    cfg: CFG,
    *,
    ascending_budget: int = DEFAULT_ASCENDING_BUDGET,
    relation_budget: int = DEFAULT_RELATION_BUDGET,
) -> AnalysisResult:
    """对 ``cfg`` 运行抽象解释，返回每块入/出不变量与断言结论。

    纯区间程序走区间不动点引擎；含差分约束语句（``AssumeDiff`` /
    ``AssertDiff``）的程序走"区间 × 差界矩阵"归约积引擎，两个域在赋值、
    分支合流、循环入口每一步交换信息。

    :param ascending_budget: 区间上升迭代安全阀（耗尽抛
        :class:`BudgetExhaustedError`，与 unknown 严格区分）。
    :param relation_budget: 关系域上升迭代的显式轮数预算。耗尽时**不**抛
        异常：关系域整体放弃（重跑纯区间分析），所有差分断言给
        ``unknown`` 并置 ``relation_truncated=True``——未收敛不冒充证明。
    """
    if isinstance(ascending_budget, bool) or not isinstance(ascending_budget, int):
        raise TypeError("ascending_budget must be int")
    if ascending_budget < 1:
        raise ValueError("ascending_budget must be >= 1")
    if isinstance(relation_budget, bool) or not isinstance(relation_budget, int):
        raise TypeError("relation_budget must be int")
    if relation_budget < 1:
        raise ValueError("relation_budget must be >= 1")

    if cfg.uses_diff_domain:
        return _analyze_with_relations(cfg, ascending_budget, relation_budget)
    return _analyze_intervals(cfg, ascending_budget)


def _analyze_intervals(cfg: CFG, ascending_budget: int) -> AnalysisResult:
    """纯区间程序的不动点分析（原引擎行为，保持逐字节的公开语义）。"""
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

    ins, outs, narrow_rounds, pw_in, pw_out = _narrow_intervals(
        cfg, order, widen_points, widened_vars, preds, ins, outs
    )

    return AnalysisResult(
        cfg=cfg,
        block_in=ins,
        block_out=outs,
        asserts=_evaluate_range_asserts_interval(cfg, ins),
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in=pw_in,
        post_widening_out=pw_out,
    )


def _narrow_intervals(cfg, order, widen_points, widened_vars, preds, ins, outs):
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
    return ins, outs, narrow_rounds, post_widening_in, post_widening_out


# -- 归约积（区间 × 差界矩阵）引擎 ---------------------------------------------

def _initial_entry_product(cfg: CFG) -> ProductState:
    state = ProductState.from_intervals(
        cfg.variable_tuple, cfg.initial_state_intervals()
    )
    if state is None:  # 入口区间本身非法不可能（Interval 构造期已拒）；防御
        return ProductState.bottom_of(cfg.variable_tuple)
    return state


def _join_product_inputs(
    cfg: CFG,
    name: str,
    outs: dict[str, ProductState],
    preds: dict[str, list[tuple[str, int]]],
) -> ProductState:
    """积状态方程右端：各前驱出状态经守卫边过滤后的凸包（入口并入初态）。"""
    acc = (
        _initial_entry_product(cfg)
        if name == cfg.entry
        else ProductState.bottom_of(cfg.variable_tuple)
    )
    for pname, edge_index in preds[name]:
        acc = acc.join(edge_state_product(outs[pname], cfg.blocks[pname], edge_index))
    return acc


def _analyze_with_relations(
    cfg: CFG, ascending_budget: int, relation_budget: int
) -> AnalysisResult:
    order, widen_points = _reverse_postorder(cfg)
    back_edges, _ = _dfs_back_edges_and_order(cfg)
    widened_vars = {
        head: frozenset(vs) for head, vs in _widened_variables(cfg, back_edges).items()
    }
    preds = _predecessors(cfg)
    variables = cfg.variable_tuple

    p_ins: dict[str, ProductState] = {
        n: ProductState.bottom_of(variables) for n in cfg.blocks
    }
    p_outs: dict[str, ProductState] = {
        n: ProductState.bottom_of(variables) for n in cfg.blocks
    }
    expansions = {n: 0 for n in widen_points}

    # -- 上升迭代（显式关系预算；未收敛 -> unknown 路径，不抛异常）-------------
    rounds = 0
    stabilized = False
    for rounds in range(1, relation_budget + 1):
        changed = False
        for name in order:
            candidate = _join_product_inputs(cfg, name, p_outs, preds)
            current = p_ins[name]
            if name in widen_points:
                if candidate.subseteq(current):
                    new_in = current
                else:
                    expansions[name] += 1
                    if expansions[name] <= 2:
                        new_in = current.join(candidate)
                    else:
                        new_in = current.widen_selective(
                            current.join(candidate), widened_vars[name]
                        )
            else:
                new_in = candidate if current.bottom else current.join(candidate)
            new_out = transfer_block_product(new_in, cfg.blocks[name])
            if new_in != current or new_out != p_outs[name]:
                changed = True
            p_ins[name] = new_in
            p_outs[name] = new_out
        if not changed:
            stabilized = True
            break

    if not stabilized:
        # 未收敛：放弃关系结论，但区间结果仍须给出——重跑纯区间引擎，
        # 差分断言全部 unknown（未收敛不冒充证明）。
        interval_result = _analyze_intervals(cfg, ascending_budget)
        diff_asserts = _all_diff_asserts_unknown(cfg)
        return AnalysisResult(
            cfg=cfg,
            block_in=interval_result.block_in,
            block_out=interval_result.block_out,
            asserts=interval_result.asserts,
            widen_points=interval_result.widen_points,
            ascending_rounds=interval_result.ascending_rounds,
            narrowing_rounds=interval_result.narrowing_rounds,
            post_widening_in=interval_result.post_widening_in,
            post_widening_out=interval_result.post_widening_out,
            diff_in=None,
            diff_out=None,
            diff_asserts=diff_asserts,
            relation_truncated=True,
            relation_rounds=relation_budget,
        )

    # -- 收窄迭代（至多 MAX_NARROWING_ROUNDS 轮，逐边标准 narrowing）-----------
    pw_p_in = {n: p_ins[n] for n in order}
    pw_p_out = {n: p_outs[n] for n in order}
    narrow_rounds = 0
    for narrow_rounds in range(1, MAX_NARROWING_ROUNDS + 1):
        changed = False
        new_ins: dict[str, ProductState] = {}
        new_outs: dict[str, ProductState] = {}
        for name in order:
            visible_outs = {**p_outs, **new_outs}
            candidate = _join_product_inputs(cfg, name, visible_outs, preds)
            current = p_ins[name]
            if name in widen_points and not current.bottom:
                new_in = current.narrow_selective(candidate, widened_vars[name])
            else:
                new_in = candidate
            new_out = transfer_block_product(new_in, cfg.blocks[name])
            if new_in != p_ins[name] or new_out != p_outs[name]:
                changed = True
            new_ins[name] = new_in
            new_outs[name] = new_out
        p_ins, p_outs = new_ins, new_outs
        if not changed:
            break

    ins = {n: p_ins[n].as_abstract_state() for n in cfg.blocks}
    outs = {n: p_outs[n].as_abstract_state() for n in cfg.blocks}
    range_asserts, diff_asserts = _evaluate_product_asserts(cfg, p_ins)
    return AnalysisResult(
        cfg=cfg,
        block_in=ins,
        block_out=outs,
        asserts=range_asserts,
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in={n: pw_p_in[n].as_abstract_state() for n in cfg.blocks},
        post_widening_out={n: pw_p_out[n].as_abstract_state() for n in cfg.blocks},
        diff_in={n: p_ins[n].as_diff_state() for n in cfg.blocks},
        diff_out={n: p_outs[n].as_diff_state() for n in cfg.blocks},
        diff_asserts=diff_asserts,
        relation_truncated=False,
        relation_rounds=rounds,
    )


def _evaluate_range_asserts_interval(
    cfg: CFG, ins: dict[str, AbstractState]
) -> list[AssertStatus]:
    """纯区间视图的范围断言求值（纯区间程序；差分语句在区间视图跳过）。"""
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
            elif isinstance(stmt, (AssumeDiff, AssertDiff)):
                continue  # 区间视图无法表达，跳过且不推进
            else:
                state = transfer_statement(state, stmt)
    return statuses


def _evaluate_product_asserts(
    cfg: CFG, ins: dict[str, ProductState]
) -> tuple[list[AssertStatus], list[DiffAssertStatus]]:
    """在同一条积状态流上逐语句求值两类断言。

    AssumeDiff 是真实路径条件，必须推进状态；AssertRange/AssertDiff 不
    改变状态；观测区间/差界都取自当前积状态（关系约束可收紧单变量区间）。
    """
    range_statuses: list[AssertStatus] = []
    diff_statuses: list[DiffAssertStatus] = []
    for name in cfg.blocks:
        block = cfg.blocks[name]
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
            elif isinstance(stmt, AssertDiff):
                if state.bottom:
                    diff_statuses.append(
                        DiffAssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    bound = state.as_diff_state().bound(stmt.a, stmt.b)
                    verdict = (
                        "proved" if bound is not None and bound <= stmt.const
                        else "unknown"
                    )
                    diff_statuses.append(
                        DiffAssertStatus(name, i, stmt, verdict, bound, False)
                    )
            else:
                state = transfer_statement_product(state, stmt)
    return range_statuses, diff_statuses


def _all_diff_asserts_unknown(cfg: CFG) -> list[DiffAssertStatus]:
    """关系预算耗尽时：差分断言一律 unknown（含不可达位置——未收敛时块
    可达性也不可信，不允许空真 proved，未收敛不冒充任何证明）。"""
    statuses: list[DiffAssertStatus] = []
    for name in cfg.blocks:
        for i, stmt in enumerate(cfg.blocks[name].statements):
            if isinstance(stmt, AssertDiff):
                statuses.append(
                    DiffAssertStatus(name, i, stmt, "unknown", None, False)
                )
    return statuses
