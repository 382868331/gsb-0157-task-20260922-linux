"""可选的有限路径分区模式（bounded path partitioning）。

动机：普通区间分析在合并点一律取凸包，``if`` 两支分别建立的性质在合流后
被磨平。本模式让调用方通过 ``analyze(cfg, partition_points=(...),
max_partitions=n)`` 指定**至多 3 个**条件位置（带守卫的块），分析按"这些
位置最近一次的真/假结果"把每个块处的抽象状态分组：

* 标签是长度 = 分区位置数的元组，逐位为 ``"T"``（最近一次为真）、
  ``"F"``（最近一次为假）、``"?"``（尚未经过该位置，unknown）。
* 数值域**不变**：每个分区仍是原来的逐变量区间状态，不引入关系域。
* 每个分区独立使用原区间转移与循环 widening——加宽按 ``(块, 标签)``
  分别计数（前两次扩张取凸包，第三次起标准 widening）。
* 标签沿边**重写**而非累积：循环再次经过指定条件时，旧真/假被新结果
  覆盖，不会被永久固定成路径事实。
* 一个块的分区数超过显式上限 ``max_partitions`` 时按标签序合并：保留
  最小的 ``max_partitions - 1`` 个具体标签，其余并入一个丢失标签的
  merged 分区（区间凸包），**不删除任何状态**；被合并掉的标签在该块
  不再重新分裂（保证上升迭代终止），每次合并记录到
  ``result.merges``（含发生块与阶段）。
* 断言只有在**每个**可达分区上都被符号包含证明时才判 ``proved``；
  没有任何可达分区时与旧语义一样空真 ``proved``（``vacuous=True``）。

证明仍由分区转移包含性（:mod:`interval_ai.checker` 逐分区独立复核）与
循环后不动点检查支持；独立有限执行（:mod:`interval_ai.concrete`）只能
用于找反例，不能代替上述证明。
"""

from __future__ import annotations

from dataclasses import dataclass

from .cfg import CFG, AssertRange
from .engine import (
    MAX_NARROWING_ROUNDS,
    AnalysisResult,
    AssertStatus,
    _dfs_back_edges_and_order,
    _predecessors,
    _reverse_postorder,
    _widened_variables,
)
from .errors import BudgetExhaustedError, ValidationError
from .intervals import AbstractState, Interval
from .transfer import edge_state, transfer_block, transfer_statement

MAX_PARTITION_POINTS = 3
DEFAULT_MAX_PARTITIONS = 8

UNKNOWN = "?"
# 标签：长度为分区位置数的 "T"/"F"/"?" 元组；None 表示合并后丢失标签的分区。
Label = tuple[str, ...] | None

_LABEL_ORDER = {UNKNOWN: 0, "F": 1, "T": 2}


def _label_sort_key(label: tuple[str, ...]) -> tuple[int, ...]:
    return tuple(_LABEL_ORDER[ch] for ch in label)


def label_text(label: Label) -> str:
    """标签的可读文本；merged 分区（标签已丢失）显示为 ``merged``。"""
    return "merged" if label is None else "".join(label)


# -- 公开结果结构 ---------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Partition:
    """一个块处的一个分区：路径标签 + 该标签下的逐变量区间状态。"""

    label: Label
    state: AbstractState

    @property
    def label_text(self) -> str:
        return label_text(self.label)

    def to_dict(self) -> dict[str, object]:
        return {"label": self.label_text, "state": self.state.to_dict()}


@dataclass(frozen=True, slots=True)
class MergeEvent:
    """一次因超过 ``max_partitions`` 而发生的强制合并（发生处可定位）。"""

    block: str
    phase: str  # "ascending" | "narrowing"
    round: int
    merged_labels: tuple[str, ...]  # 被并入 merged 分区的标签（文本）
    kept_labels: tuple[str, ...]  # 按标签序保留的具体标签（文本）

    def to_dict(self) -> dict[str, object]:
        return {
            "block": self.block,
            "phase": self.phase,
            "round": self.round,
            "merged_labels": list(self.merged_labels),
            "kept_labels": list(self.kept_labels),
        }


# -- 输入校验 -------------------------------------------------------------------


def validate_partitioning(
    cfg: CFG, partition_points: object, max_partitions: object
) -> tuple[str, ...]:
    """校验分区参数，返回规范化后的分区位置元组；非法输入抛 ValidationError。"""
    loc = "partition_points"
    if isinstance(partition_points, (str, bytes)) or not isinstance(
        partition_points, (tuple, list)
    ):
        raise ValidationError(
            f"partition_points must be a tuple/list of block names, "
            f"got {partition_points!r}",
            loc,
        )
    pts = tuple(partition_points)
    if len(pts) > MAX_PARTITION_POINTS:
        raise ValidationError(
            f"too many partition points: {len(pts)} > {MAX_PARTITION_POINTS}",
            loc,
        )
    seen: set[str] = set()
    for i, p in enumerate(pts):
        iloc = f"partition_points[{i}]"
        if not isinstance(p, str) or not p:
            raise ValidationError(
                f"partition point must be a non-empty block name, got {p!r}", iloc
            )
        if p in seen:
            raise ValidationError(f"duplicate partition point {p!r}", iloc)
        seen.add(p)
        if p not in cfg.blocks:
            raise ValidationError(
                f"partition point {p!r} is not a block of the CFG", iloc
            )
        if cfg.blocks[p].guard is None:
            raise ValidationError(
                f"partition point {p!r} must be a block with a Guard "
                f"(exactly 2 successors)",
                iloc,
            )
    if isinstance(max_partitions, bool) or not isinstance(max_partitions, int):
        raise ValidationError(
            f"max_partitions must be an int, got {max_partitions!r}",
            "max_partitions",
        )
    if max_partitions < 1:
        raise ValidationError(
            f"max_partitions must be >= 1, got {max_partitions}", "max_partitions"
        )
    return pts


# -- 分区不动点引擎 ---------------------------------------------------------------


def analyze_partitioned(
    cfg: CFG,
    partition_points: tuple[str, ...] | list[str],
    max_partitions: int,
    *,
    ascending_budget: int,
) -> AnalysisResult:
    """有限路径分区分析；分区数有显式上限，超出按标签序合并（不删状态）。"""
    pts = validate_partitioning(cfg, partition_points, max_partitions)
    order, widen_points = _reverse_postorder(cfg)
    back_edges, _ = _dfs_back_edges_and_order(cfg)
    widened_vars = _widened_variables(cfg, back_edges)
    preds = _predecessors(cfg)
    pos = {name: i for i, name in enumerate(pts)}
    variables = cfg.variable_tuple
    initial_label: Label = tuple(UNKNOWN for _ in pts)

    ins: dict[str, dict[Label, AbstractState]] = {n: {} for n in cfg.blocks}
    outs: dict[str, dict[Label, AbstractState]] = {n: {} for n in cfg.blocks}
    expansions: dict[tuple[str, Label], int] = {}
    # 每个块曾被强制合并掉的标签：不再重新分裂（保证终止），其流入并入 merged
    banned: dict[str, set[tuple[str, ...]]] = {n: set() for n in cfg.blocks}
    merges: list[MergeEvent] = []

    def edge_label(pname: str, label: Label, edge_index: int) -> Label:
        """沿边重写标签：经过分区位置时记录本次真/假（覆盖旧值，不累积）。"""
        if label is None or pname not in pos:
            return label
        lst = list(label)
        lst[pos[pname]] = "T" if edge_index == 0 else "F"
        return tuple(lst)

    def candidates(
        name: str, visible_outs: dict[str, dict[Label, AbstractState]]
    ) -> dict[Label, AbstractState]:
        """方程右端：各前驱各分区经边守卫过滤、按新标签分组取凸包。"""
        cand: dict[Label, AbstractState] = {}

        def add(label: Label, state: AbstractState) -> None:
            if state.bottom:
                return
            prev = cand.get(label)
            cand[label] = state if prev is None else prev.join(state)

        if name == cfg.entry:
            add(
                initial_label,
                AbstractState(variables, cfg.initial_state_intervals(), False),
            )
        for pname, edge_index in preds[name]:
            pblock = cfg.blocks[pname]
            for label, st in visible_outs[pname].items():
                if st.bottom:
                    continue
                add(
                    edge_label(pname, label, edge_index),
                    edge_state(st, pblock, edge_index),
                )
        return cand

    def apply_cap(
        name: str, cand: dict[Label, AbstractState], phase: str, rnd: int
    ) -> dict[Label, AbstractState]:
        """分区数超上限时按标签序合并：丢失标签取凸包，不删除状态。"""
        if banned[name]:
            for label in [l for l in cand if l is not None and l in banned[name]]:
                st = cand.pop(label)
                prev = cand.get(None)
                cand[None] = st if prev is None else prev.join(st)
        if len(cand) <= max_partitions:
            return cand
        concrete = sorted(
            (l for l in cand if l is not None), key=_label_sort_key
        )
        keep = concrete[: max_partitions - 1]
        keep_set = set(keep)
        merged_state = cand.get(None)
        dropped_texts: list[str] = []
        for label in concrete:
            if label in keep_set:
                continue
            st = cand.pop(label)
            merged_state = st if merged_state is None else merged_state.join(st)
            dropped_texts.append(label_text(label))
            banned[name].add(label)
        if dropped_texts:
            cand[None] = merged_state
            merges.append(
                MergeEvent(
                    block=name,
                    phase=phase,
                    round=rnd,
                    merged_labels=tuple(dropped_texts),
                    kept_labels=tuple(label_text(l) for l in keep),
                )
            )
        return cand

    # -- 上升迭代（逐分区延迟加宽）---------------------------------------------
    rounds = 0
    for rounds in range(1, ascending_budget + 1):
        changed = False
        for name in order:
            cand = apply_cap(name, candidates(name, outs), "ascending", rounds)
            current = ins[name]
            if name in widen_points:
                new_map: dict[Label, AbstractState] = {}
                for label, cst in cand.items():
                    cur = current.get(label)
                    key = (name, label)
                    if cur is None:
                        expansions[key] = expansions.get(key, 0) + 1
                        new_map[label] = cst
                    elif cst.subseteq(cur):
                        new_map[label] = cur
                    else:
                        expansions[key] = expansions.get(key, 0) + 1
                        if expansions[key] <= 2:
                            new_map[label] = cur.join(cst)
                        else:
                            new_map[label] = cur.widen_selective(
                                cur.join(cst), widened_vars[name]
                            )
                for label, cur in current.items():
                    if label not in new_map:
                        new_map[label] = cur
                new_map = apply_cap(name, new_map, "ascending", rounds)
            else:
                new_map = dict(current)
                for label, cst in cand.items():
                    prev = new_map.get(label)
                    new_map[label] = cst if prev is None else prev.join(cst)
                new_map = apply_cap(name, new_map, "ascending", rounds)
            new_out_map = {
                label: transfer_block(st, cfg.blocks[name])
                for label, st in new_map.items()
            }
            if new_map != current or new_out_map != outs[name]:
                changed = True
            ins[name] = new_map
            outs[name] = new_out_map
        if not changed:
            break
    else:
        raise BudgetExhaustedError(
            f"ascending iteration did not stabilize within {ascending_budget} rounds",
            rounds=ascending_budget,
            partial={"block_in": ins, "block_out": outs},
        )

    # -- 收窄迭代（逐分区，至多 MAX_NARROWING_ROUNDS 轮）-------------------------
    post_widening_in = {n: _hull(ins[n], variables) for n in order}
    post_widening_out = {n: _hull(outs[n], variables) for n in order}
    narrow_rounds = 0
    for narrow_rounds in range(1, MAX_NARROWING_ROUNDS + 1):
        changed = False
        new_ins: dict[str, dict[Label, AbstractState]] = {}
        new_outs: dict[str, dict[Label, AbstractState]] = {}
        for name in order:
            visible_outs = {**outs, **new_outs}
            cand = apply_cap(
                name, candidates(name, visible_outs), "narrowing", narrow_rounds
            )
            current = ins[name]
            if name in widen_points:
                new_map = {}
                for label, cst in cand.items():
                    cur = current.get(label)
                    new_map[label] = (
                        cst
                        if cur is None
                        else cur.narrow_selective(cst, widened_vars[name])
                    )
                for label, cur in current.items():
                    if label not in new_map:
                        new_map[label] = cur
                new_map = apply_cap(name, new_map, "narrowing", narrow_rounds)
            else:
                new_map = cand
            new_ins[name] = new_map
            new_outs[name] = {
                label: transfer_block(st, cfg.blocks[name])
                for label, st in new_map.items()
            }
            if new_map != ins[name] or new_outs[name] != outs[name]:
                changed = True
        ins, outs = new_ins, new_outs
        if not changed:
            break

    block_in = {n: _hull(ins[n], variables) for n in cfg.blocks}
    block_out = {n: _hull(outs[n], variables) for n in cfg.blocks}

    return AnalysisResult(
        cfg=cfg,
        block_in=block_in,
        block_out=block_out,
        asserts=_evaluate_asserts_partitioned(cfg, ins),
        widen_points=tuple(n for n in order if n in widen_points),
        ascending_rounds=rounds,
        narrowing_rounds=narrow_rounds,
        post_widening_in=post_widening_in,
        post_widening_out=post_widening_out,
        partition_points=pts,
        max_partitions=max_partitions,
        merges=tuple(merges),
        block_partitions_in={n: _sorted_partitions(ins[n]) for n in cfg.blocks},
        block_partitions_out={n: _sorted_partitions(outs[n]) for n in cfg.blocks},
    )


def _hull(
    parts: dict[Label, AbstractState], variables: tuple[str, ...]
) -> AbstractState:
    """各分区的凸包（无任何可达分区时为底）；作为兼容的整块不变量视图。"""
    acc = AbstractState.bottom_of(variables)
    for st in parts.values():
        acc = acc.join(st)
    return acc


def _sorted_partitions(parts: dict[Label, AbstractState]) -> tuple[Partition, ...]:
    items = sorted(
        parts.items(),
        key=lambda kv: (kv[0] is None, _label_sort_key(kv[0]) if kv[0] else ()),
    )
    return tuple(Partition(label, st) for label, st in items)


def _evaluate_asserts_partitioned(
    cfg: CFG, ins: dict[str, dict[Label, AbstractState]]
) -> list[AssertStatus]:
    """断言判定：只有每个可达分区都被符号包含证明时才判 proved。"""
    statuses: list[AssertStatus] = []
    for name in cfg.blocks:
        block = cfg.blocks[name]
        cur = dict(ins[name])
        for i, stmt in enumerate(block.statements):
            if isinstance(stmt, AssertRange):
                required = Interval(stmt.lower, stmt.upper)
                per: list[tuple[str, str]] = []
                observed_hull: Interval | None = None
                all_proved = True
                for part in _sorted_partitions(
                    {l: s for l, s in cur.items() if not s.bottom}
                ):
                    obs = part.state.get(stmt.target)
                    ok = obs.subseteq(required)
                    per.append((part.label_text, "proved" if ok else "unknown"))
                    all_proved = all_proved and ok
                    observed_hull = obs if observed_hull is None else observed_hull.join(obs)
                if not per:
                    statuses.append(
                        AssertStatus(name, i, stmt, "proved", None, vacuous=True)
                    )
                else:
                    verdict = "proved" if all_proved else "unknown"
                    statuses.append(
                        AssertStatus(
                            name, i, stmt, verdict, observed_hull, False, tuple(per)
                        )
                    )
            else:
                cur = {
                    label: transfer_statement(st, stmt)
                    for label, st in cur.items()
                }
    return statuses
