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

可选**有限路径分区模式**（``analyze(cfg, track_guards=..., max_partitions=...)``）：
状态按至多 3 个指定块尾条件的"最近一次真假"分组，见
:mod:`interval_ai.partitions`。每个分区独立套用同一套延迟加宽与收窄；
标签在循环中只记录最近一次结果（可覆写）；分区数超显式上限时按标签顺序
强制合并（凸包守恒、冻结冲突槽位），合并事件在结果中逐一报告。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Sequence

from .cfg import CFG, AssertRange, Block
from .errors import BudgetExhaustedError, ValidationError
from .intervals import AbstractState, Interval
from .partitions import (
    MAX_PARTITION_POINTS,
    FALSE,
    TRUE,
    Label,
    MergeEvent,
    PartitionedState,
    coarsen_members,
    fine_grid,
)
from .transfer import edge_state, transfer_block, transfer_statement

MAX_NARROWING_ROUNDS = 8
DEFAULT_ASCENDING_BUDGET = 10000
#: 分区模式下每块分区数的默认显式上限（调用方可覆盖）。
DEFAULT_MAX_PARTITIONS = 8


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
class PartitionAssert:
    """断言在单个可达分区上的观测结果（分区模式）。"""

    label: str  # 标签文本，如 "T.?"
    observed: Interval

    def to_dict(self) -> dict[str, object]:
        return {"label": self.label, "observed": self.observed.to_dict()}


@dataclass(frozen=True, slots=True)
class AssertStatus:
    block: str
    index: int
    statement: AssertRange
    verdict: str  # "proved" | "unknown"
    observed: Interval | None  # 分析到的实际区间（各可达分区凸包）；不可达位置为 None
    vacuous: bool = False  # 位置不可达，空真成立
    # 分区模式：每个可达分区各自的观测（普通模式为空）。
    partitions: tuple[PartitionAssert, ...] = ()

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
        if self.partitions:
            d["partition_observations"] = [p.to_dict() for p in self.partitions]
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
    # -- 有限路径分区（普通模式下为空/None）-----------------------------------
    # 被跟踪的条件位置块名（顺序即标签槽位顺序）。
    track_guards: tuple[str, ...] = ()
    max_partitions: int | None = None
    # 每块入/出的逐分区状态；空 dict 表示普通（不分区）模式。
    partition_in: dict[str, PartitionedState] = field(default_factory=dict)
    partition_out: dict[str, PartitionedState] = field(default_factory=dict)
    # 收窄前的分区快照。
    post_widening_partition_in: dict[str, PartitionedState] = field(default_factory=dict)
    post_widening_partition_out: dict[str, PartitionedState] = field(default_factory=dict)
    # 强制合并事件（按发生先后）。
    merges: tuple[MergeEvent, ...] = ()

    @property
    def partitioned(self) -> bool:
        """是否运行在有限路径分区模式。"""
        return bool(self.track_guards)

    @property
    def narrowing_refined(self) -> bool:
        return self.block_in != self.post_widening_in or self.block_out != self.post_widening_out

    def state_at(self, block: str) -> AbstractState:
        return self.block_in[block]

    def partition_state_at(self, block: str, label: Label) -> AbstractState | None:
        """取某块某标签分区的入状态；该分区不可达时返回 None。"""
        if not self.partitioned:
            raise ValueError("partition_state_at is only available in partition mode")
        return self.partition_in[block].members.get(label)

    def reachable_partitions(self, block: str) -> list[tuple[Label, AbstractState]]:
        """某块所有可达分区（按标签顺序）及各自入状态；仅分区模式可用。"""
        if not self.partitioned:
            raise ValueError("reachable_partitions is only available in partition mode")
        ps = self.partition_in[block]
        return [(label, ps.members[label]) for label in ps.labels]

    def to_dict(self) -> dict[str, object]:
        data: dict[str, object] = {
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
        if self.partitioned:
            data["track_guards"] = list(self.track_guards)
            data["max_partitions"] = self.max_partitions
            data["merges"] = [m.to_dict() for m in self.merges]
            data["partitions"] = {
                name: {
                    "in": {
                        label.text: state.to_dict()
                        for label, state in self.partition_in[name].members.items()
                    },
                    "out": {
                        label.text: state.to_dict()
                        for label, state in self.partition_out[name].members.items()
                    },
                }
                for name in self.cfg.blocks
            }
        return data


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
    track_guards: Sequence[str] | None = None,
    max_partitions: int = DEFAULT_MAX_PARTITIONS,
    ascending_budget: int = DEFAULT_ASCENDING_BUDGET,
) -> AnalysisResult:
    """对 ``cfg`` 运行区间抽象解释，返回每块入/出不变量与断言结论。

    :param track_guards: 可选的分区条件位置（块名，至多
        :data:`~interval_ai.partitions.MAX_PARTITION_POINTS` 个，块必须带
        :class:`~interval_ai.cfg.Guard`）。给出后进入**有限路径分区模式**：
        状态按这些条件最近一次真假分组；空序列/None 为普通凸包模式。
    :param max_partitions: 每个块的显式分区数上限（>=1）；超过时按标签顺序
        强制合并，事件见 ``result.merges``。
    :param ascending_budget: 上升迭代轮数安全阀，耗尽抛
        :class:`BudgetExhaustedError`。
    """
    if isinstance(ascending_budget, bool) or not isinstance(ascending_budget, int):
        raise TypeError("ascending_budget must be int")
    if ascending_budget < 1:
        raise ValueError("ascending_budget must be >= 1")

    points = _validate_track_guards(cfg, track_guards)
    if isinstance(max_partitions, bool) or not isinstance(max_partitions, int):
        raise TypeError("max_partitions must be int")
    if max_partitions < 1:
        raise ValueError("max_partitions must be >= 1")

    if not points:
        return _analyze_plain(cfg, ascending_budget)
    return _analyze_partitioned(cfg, points, max_partitions, ascending_budget)


def _validate_track_guards(cfg: CFG, track_guards: Sequence[str] | None) -> tuple[str, ...]:
    if track_guards is None:
        return ()
    if isinstance(track_guards, (str, bytes)) or not isinstance(track_guards, Sequence):
        raise TypeError("track_guards must be a sequence of block names or None")
    points = tuple(track_guards)
    if not points:
        return ()
    if len(points) > MAX_PARTITION_POINTS:
        raise ValidationError(
            f"too many partition points: {len(points)} > {MAX_PARTITION_POINTS}",
            "analyze.track_guards",
        )
    seen: set[str] = set()
    for i, name in enumerate(points):
        loc = f"analyze.track_guards[{i}]"
        if not isinstance(name, str) or not name:
            raise ValidationError("partition point must be a non-empty block name", loc)
        if name in seen:
            raise ValidationError(f"duplicate partition point {name!r}", loc)
        seen.add(name)
        if name not in cfg.blocks:
            raise ValidationError(f"partition point block {name!r} does not exist", loc)
        block = cfg.blocks[name]
        if block.guard is None or len(block.successors) != 2:
            raise ValidationError(
                f"partition point block {name!r} must end in a 2-way guard", loc
            )
    return points


def _analyze_plain(cfg: CFG, ascending_budget: int) -> AnalysisResult:
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


# -- 有限路径分区引擎 ----------------------------------------------------------
#
# 做法（健全性/终止性依据）：
#
# * 标签语义在**细标签网格**上说明：细标签无冻结槽，每槽取 ?/F/T，
#   k<=3 个位置共 3^k<=27 个。粗标签 L 的具体化集合 gamma(L) 把其冻结槽
#   任取三值（见 partitions.Label.fine_members）；一个粗分区的区间状态
#   对 gamma(L) 中每个细标签都成立（冻结=在该维上故意丢失区分）。
# * 每个块保留一个粗分区表（标签 -> 区间状态），标签彼此允许在细网格上
#   重叠（例如冻结槽的 (? 冻结) 与未冻结细标签 ?）；右端细格被**所有**
#   覆盖它的旧分区接收（重复接收只是冗余，覆盖性因此平凡保持）。
# * 上升迭代的每个块步：
#     1. 右端：对每个前驱粗分区先过守卫边（区间过滤 + 粗标签槽位覆写，
#        冻结槽在 Label.update 中天然不分裂），再把结果按 gamma 展开到
#        细网格，同细格取凸包；入口块并入全 ? 初始细标签。
#     2. 喂回：右端细格被每个覆盖它的旧粗分区接收（加宽点沿用"前两次
#        凸包、第三次起 selective widening"，非加宽点直接凸包累积）；
#        没有任何旧分区覆盖的细格才新建无冻结细分区。旧分区只保留或被
#        按标签顺序合并，从不凭空删除。
#     3. 上限：分区数超过 max_partitions 时 partitions.coarsen_members
#               按标签总序反复 generalize 合并（凸包守恒、冻结冲突槽），
#        报告 MergeEvent；被吸收标签的 gamma 是幸存标签 gamma 的子集。
# * 有界性：细标签至多 27 个/块，被吸收的细格会被幸存粗分区覆盖、不再
#   重生；每个粗标签上的喂入序列是凸包单调链，由标准 widening 收敛；
#   结构（新生/冻结）事件有限。故上升迭代必然终止，预算阀只是防御性
#   安全阀。收窄在稳定结构上做至多 MAX_NARROWING_ROUNDS 轮 selective
#   narrowing。


def _partition_right(
    cfg: CFG,
    name: str,
    outs: dict[str, PartitionedState],
    preds: dict[str, list[tuple[str, int]]],
    slot_of: dict[str, int],
    k: int,
) -> dict[Label, AbstractState]:
    """方程右端的**细网格**像：细标签 -> 区间状态（仅含非空细格）。

    顺序很重要：前驱粗分区必须**先过边**（区间过滤 + 粗标签槽位覆写，
    冻结槽保持冻结），**再** gamma 展开到细网格；反之冻结槽会被重新
    分裂，"丢失的标签"就被错误地恢复了。
    """
    variables = cfg.variable_tuple
    fine = set(fine_grid(k))
    acc: dict[Label, AbstractState] = {}

    def add(label: Label, state: AbstractState) -> None:
        if state.bottom:
            return
        if label in acc:
            acc[label] = acc[label].join(state)
        else:
            acc[label] = state

    if name == cfg.entry:
        add(Label.initial(k), _initial_entry_state(cfg))

    for pname, edge_index in preds[name]:
        pblock = cfg.blocks[pname]
        source = outs[pname]
        if source.is_bottom:
            continue
        slot = slot_of.get(pname)
        for coarse, state in source.members.items():
            # 1) 先在粗分区上过守卫边：区间过滤 + 粗标签槽覆写。
            filtered = edge_state(state, pblock, edge_index)
            if filtered.bottom:
                continue
            if slot is not None and pblock.guard is not None:
                outcome = TRUE if edge_index == 0 else FALSE
                coarse_after = coarse.update(slot, outcome)
            else:
                coarse_after = coarse
            # 2) 再 gamma 展开：冻结槽复制同一区间状态（精度损失真实生效）。
            for f in coarse_after.fine_members():
                assert f in fine
                add(f, filtered)
    return acc


def _analyze_partitioned(
    cfg: CFG,
    points: tuple[str, ...],
    max_partitions: int,
    ascending_budget: int,
) -> AnalysisResult:
    order, widen_points = _reverse_postorder(cfg)
    back_edges, _ = _dfs_back_edges_and_order(cfg)
    widened_vars = _widened_variables(cfg, back_edges)
    preds = _predecessors(cfg)
    variables = cfg.variable_tuple
    k = len(points)
    slot_of = {name: i for i, name in enumerate(points)}
    bottom_map = PartitionedState.bottom_of(variables)

    ins: dict[str, PartitionedState] = {n: bottom_map for n in cfg.blocks}
    outs: dict[str, PartitionedState] = {n: bottom_map for n in cfg.blocks}
    # 每个 (加宽点, 粗标签) 的扩张次数；标签被合并消失后计数自然作废。
    expansions: dict[tuple[str, Label], int] = {}
    merge_events: list[MergeEvent] = []

    # -- 上升迭代 -------------------------------------------------------------
    rounds = 0
    for rounds in range(1, ascending_budget + 1):
        changed = False
        for name in order:
            right = _partition_right(cfg, name, outs, preds, slot_of, k)
            current = ins[name].members

            # 1) 旧粗分区原样占位（本轮无右饲喂入的分区保持不变）。
            fed: dict[Label, AbstractState] = dict(current)
            # 2) 右端细格按宿主聚合喂入凸包；无宿主的细格新建分区。
            feeds: dict[Label, AbstractState] = {}
            newborn: dict[Label, AbstractState] = {}
            for fine_label, rst in right.items():
                hosts = [c for c in current if c.covers_fine(fine_label)]
                if not hosts:
                    if fine_label in newborn:
                        newborn[fine_label] = newborn[fine_label].join(rst)
                    else:
                        newborn[fine_label] = rst
                    continue
                for coarse in hosts:
                    if coarse in feeds:
                        feeds[coarse] = feeds[coarse].join(rst)
                    else:
                        feeds[coarse] = rst
            for fine_label, rst in newborn.items():
                if fine_label in fed:
                    fed[fine_label] = fed[fine_label].join(rst)
                else:
                    fed[fine_label] = rst
            for coarse, feed in feeds.items():
                cur = fed[coarse]
                if name in widen_points:
                    if feed.subseteq(cur):
                        new_state = cur
                    else:
                        ekey = (name, coarse)
                        count = expansions.get(ekey, 0) + 1
                        expansions[ekey] = count
                        if count <= 2:
                            # 前两次扩张：凸包（延迟加宽）
                            new_state = cur.join(feed)
                        else:
                            # 第三次扩张起：仅加宽循环内被修改变量
                            new_state = cur.widen_selective(
                                cur.join(feed), widened_vars[name]
                            )
                else:
                    new_state = cur.join(feed)
                fed[coarse] = new_state

            # 3) 显式上限：按标签顺序强制合并（凸包守恒、只丢标签不删状态）。
            if len(fed) > max_partitions:
                fed, _groups, events = coarsen_members(
                    fed, max_partitions, name, rounds
                )
                merge_events.extend(events)

            new_in = PartitionedState(variables, fed)
            new_out = new_in.transfer_map(cfg.blocks[name])
            if new_in != ins[name] or new_out != outs[name]:
                changed = True
            ins[name] = new_in
            outs[name] = new_out
        if not changed:
            break
    else:
        raise BudgetExhaustedError(
            f"partitioned ascending iteration did not stabilize within "
            f"{ascending_budget} rounds",
            rounds=ascending_budget,
            partial={"partition_in": ins, "partition_out": outs},
        )

    # -- 收窄迭代（结构已稳定；至多 MAX_NARROWING_ROUNDS 轮）------------------
    post_in = {n: ins[n] for n in order}
    post_out = {n: outs[n] for n in order}
    narrow_rounds = 0
    for narrow_rounds in range(1, MAX_NARROWING_ROUNDS + 1):
        changed = False
        new_ins: dict[str, PartitionedState] = {}
        new_outs: dict[str, PartitionedState] = {}
        for name in order:
            right = _partition_right(cfg, name, outs, preds, slot_of, k)
            current = ins[name].members
            members: dict[Label, AbstractState] = {}
            covered: set[Label] = set()
            for coarse, cur in current.items():
                cand: AbstractState | None = None
                for f in coarse.fine_members():
                    if f in right:
                        covered.add(f)
                        cand = right[f] if cand is None else cand.join(right[f])
                if cand is None:
                    members[coarse] = cur  # 本轮该粗分区无右饲喂入
                elif name in widen_points:
                    members[coarse] = cur.narrow_selective(cand, widened_vars[name])
                else:
                    members[coarse] = cand
            # 兜底：结构稳定后不应存在未覆盖细格；若有，保留而非删除
            # （收窄只会缩小可达集，正常不动点下这里不触发）。
            for f, rst in right.items():
                if f not in covered and f not in members:
                    members[f] = rst
            if len(members) > max_partitions:
                members, _groups, _events = coarsen_members(
                    members, max_partitions, name, narrow_rounds
                )
            new_in = PartitionedState(variables, members)
            new_out = new_in.transfer_map(cfg.blocks[name])
            if new_in != ins[name] or new_out != outs[name]:
                changed = True
            new_ins[name] = new_in
            new_outs[name] = new_out
        ins, outs = new_ins, new_outs
        if not changed:
            break

    hull_in = {n: ins[n].convex_hull() for n in order}
    hull_out = {n: outs[n].convex_hull() for n in order}
    return AnalysisResult(
        cfg=cfg,
        block_in=hull_in,
        block_out=hull_out,
        asserts=_evaluate_asserts_partitioned(cfg, ins),
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in={n: post_in[n].convex_hull() for n in order},
        post_widening_out={n: post_out[n].convex_hull() for n in order},
        track_guards=points,
        max_partitions=max_partitions,
        partition_in=ins,
        partition_out=outs,
        post_widening_partition_in=post_in,
        post_widening_partition_out=post_out,
        merges=tuple(merge_events),
    )


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


def _evaluate_asserts_partitioned(
    cfg: CFG, ins: dict[str, PartitionedState]
) -> list[AssertStatus]:
    """逐分区求值断言：每个**可达**分区都能符号包含于要求区间才算 proved。

    判定完全基于符号端点包含，不做任何采样；不可达位置（无任何可达分区）
    仍按空真 proved + vacuous。
    """
    statuses: list[AssertStatus] = []
    for name in cfg.blocks:
        block: Block = cfg.blocks[name]
        live = dict(ins[name].members)
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                if not live:
                    statuses.append(
                        AssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                    continue
                required = Interval(stmt.lower, stmt.upper)
                details: list[PartitionAssert] = []
                hull: Interval | None = None
                all_proved = True
                for label in sorted(live, key=lambda l: l.order_key):
                    observed = live[label].get(stmt.target)
                    details.append(PartitionAssert(label.text, observed))
                    hull = observed if hull is None else hull.join(observed)
                    if not observed.subseteq(required):
                        all_proved = False
                statuses.append(
                    AssertStatus(
                        name,
                        i,
                        stmt,
                        "proved" if all_proved else "unknown",
                        hull,
                        False,
                        partitions=tuple(details),
                    )
                )
            else:
                live = {
                    label: transfer_statement(state, stmt)
                    for label, state in live.items()
                }
    return statuses
