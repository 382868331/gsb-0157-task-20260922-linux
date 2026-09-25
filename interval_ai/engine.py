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
from typing import TYPE_CHECKING

from .cfg import CFG, AssertRange, Block
from .errors import BudgetExhaustedError
from .intervals import AbstractState, Interval
from .transfer import edge_state, transfer_block, transfer_statement

if TYPE_CHECKING:  # 避免循环导入：partition 依赖本模块的图分析辅助
    from .partition import MergeEvent, Partition

MAX_NARROWING_ROUNDS = 8
DEFAULT_ASCENDING_BUDGET = 10000


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
                if not isinstance(st, AssertRange):
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
    # 分区模式下每个可达分区的 (标签文本, 判定)；非分区分析为空
    partition_verdicts: tuple[tuple[str, str], ...] = ()

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
        if self.partition_verdicts:
            d["partitions"] = [
                {"label": label, "verdict": v}
                for label, v in self.partition_verdicts
            ]
        return d


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
    # -- 有限路径分区模式（partition_points 非空时由 partition.py 填充）---------
    partition_points: tuple[str, ...] = ()
    max_partitions: int | None = None
    merges: tuple[MergeEvent, ...] = ()  # 强制合并发生处（块/阶段/被并标签）
    block_partitions_in: dict[str, tuple[Partition, ...]] = field(default_factory=dict)
    block_partitions_out: dict[str, tuple[Partition, ...]] = field(default_factory=dict)

    @property
    def narrowing_refined(self) -> bool:
        return self.block_in != self.post_widening_in or self.block_out != self.post_widening_out

    def state_at(self, block: str) -> AbstractState:
        return self.block_in[block]

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
        if self.partition_points:
            d["partition_points"] = list(self.partition_points)
            d["max_partitions"] = self.max_partitions
            d["merges"] = [m.to_dict() for m in self.merges]
            d["partitions_in"] = {
                name: [p.to_dict() for p in parts]
                for name, parts in self.block_partitions_in.items()
            }
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
    partition_points: tuple[str, ...] | list[str] = (),
    max_partitions: int | None = None,
) -> AnalysisResult:
    """对 ``cfg`` 运行区间抽象解释，返回每块入/出不变量与断言结论。

    :param partition_points: 可选的有限路径分区位置（至多 3 个带守卫的块名；
        见 :mod:`interval_ai.partition`）。为空即旧行为：合并一律取凸包。
    :param max_partitions: 每个块允许的最大分区数（显式上限，默认
        ``DEFAULT_MAX_PARTITIONS``）；超出按标签序合并，不删状态。
    """
    if isinstance(ascending_budget, bool) or not isinstance(ascending_budget, int):
        raise TypeError("ascending_budget must be int")
    if ascending_budget < 1:
        raise ValueError("ascending_budget must be >= 1")

    if partition_points:
        from .partition import DEFAULT_MAX_PARTITIONS, analyze_partitioned

        return analyze_partitioned(
            cfg,
            partition_points,
            DEFAULT_MAX_PARTITIONS if max_partitions is None else max_partitions,
            ascending_budget=ascending_budget,
        )

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


def _evaluate_asserts(cfg: CFG, ins: dict[str, AbstractState]) -> list[AssertStatus]:
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
