"""有限路径分区（bounded trace partitioning）。

动机：普通区间解释在 if 两支汇合时一律取凸包，像 ``x<=3`` 与 ``x>=4``
两支汇合后只能得到 ``[0,10]``，路径上已知的分流信息被丢掉。本模块允许
调用方指定**至多** :data:`MAX_PARTITION_POINTS` 个块尾条件作为"分区位置"，
状态按这些位置**最近一次**的真假结果分组传播：

* 槽位取值 :data:`TRUE` / :data:`FALSE` / :data:`UNKNOWN`：
  - TRUE/FALSE = 最近一次经过该条件时走了真/假支；
  - UNKNOWN = 还从未经过该条件（路径上确实未知，不是数值顶元素）。
* 标签只记录"最近一次"：循环里再次经过同一条件时槽位被**覆写**，
  旧的真假不会被永久固定成路径事实（例如循环内反复为真、退出时为假，
  退出分区拿到的是假标签，而不是被第一次的真标签永远占据）。
* 本模块**不引入任何关系数值域**：每个分区内部仍是逐变量区间
  (:class:`~interval_ai.intervals.AbstractState`)，合并取区间凸包。

分区数有显式上限（由 :func:`~interval_ai.engine.analyze` 在每个块输入处
强制）。超限时 :meth:`PartitionedState.force_merge` **按标签顺序**合并：
被合并的标签逐槽泛化（一致槽保留，冲突槽抹成 UNKNOWN 并"冻结"），区间
取凸包。冻结槽此后不再被条件覆写而重新分裂——这是上限的代价，也是"丢失
标签"的字面含义；被抹除的槽位在 :class:`MergeEvent` 中报告。状态本身
永不删除：合并前后所有成员的总凸包严格相等（有测试与独立检查器保证）。

冻结的语义可以在**细标签网格**上精确说明：细标签 = 无冻结、每槽取
``?/F/T`` 的标签（k 个位置共 3^k 个，k≤3 即至多 27 个）。标签 L 的
"具体化集合" γ(L)：冻结槽任取 ?/F/T，非冻结槽固定为 L 的槽值。冻结即
把该槽三个细值合并成一个粗单元。引擎据此在粗化结构变动时做确定性的
再分配（见 :func:`fine_grid` / :meth:`Label.fine_members`），这给出上升
迭代的单调性与终止性：粗标签格有限（每槽 T/F/?-未冻结/?-冻结 共 4^k
个），每个标签上的区间链仍由标准 widening 保证有限。
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from .cfg import Block
from .intervals import AbstractState
from .transfer import edge_state, transfer_block

#: 调用方可指定的分区条件位置上限。
MAX_PARTITION_POINTS = 3

#: 槽位真值。
UNKNOWN = -1
FALSE = 0
TRUE = 1

_SLOT_VALUES = (UNKNOWN, FALSE, TRUE)
_VALUE_TEXT = {UNKNOWN: "?", FALSE: "F", TRUE: "T"}
_FINE_GRID_CACHE: dict[int, tuple["Label", ...]] = {}


def fine_grid(k: int) -> tuple[Label, ...]:
    """k 个槽位的全部细标签（无冻结），按标签总序排列；k>=1。"""
    if k not in _FINE_GRID_CACHE:
        labels = tuple(
            Label(values, frozenset())
            for values in product(_SLOT_VALUES, repeat=k)
        )
        _FINE_GRID_CACHE[k] = tuple(sorted(labels, key=lambda l: l.order_key))
    return _FINE_GRID_CACHE[k]


@dataclass(frozen=True, slots=True)
class Label:
    """长度等于分区点数的标签；``values[i]`` 为第 i 个条件的最近结果。

    ``frozen`` 中的槽位已因强制合并被抹除：值恒为 :data:`UNKNOWN`，
    之后经过该条件也不再覆写（标签已在该维度上丢失）。
    """

    values: tuple[int, ...]
    frozen: frozenset[int] = frozenset()

    @classmethod
    def initial(cls, points: int) -> "Label":
        """全 UNKNOWN、无冻结的初始标签（``points>=0``）。"""
        return cls((UNKNOWN,) * points, frozenset())

    def __post_init__(self) -> None:
        if not isinstance(self.values, tuple):
            raise TypeError("Label.values must be a tuple of slot values")
        for v in self.values:
            if v not in _VALUE_TEXT:
                raise TypeError(f"illegal label slot value {v!r}")
        if not isinstance(self.frozen, frozenset):
            object.__setattr__(self, "frozen", frozenset(self.frozen))
        for i in self.frozen:
            if not isinstance(i, int) or isinstance(i, bool) or not (0 <= i < len(self.values)):
                raise TypeError(f"frozen slot index {i!r} out of range")
        for i in self.frozen:
            if self.values[i] is not UNKNOWN:
                raise TypeError("frozen slot must carry UNKNOWN")

    @property
    def order_key(self) -> tuple[tuple[int, ...], tuple[int, ...]]:
        """标签总序：先按槽位字典序（? < F < T），再按冻结集合。"""
        return self.values, tuple(sorted(self.frozen))

    @property
    def text(self) -> str:
        # 冻结槽用独立的 "x" 标记：未经过 "?" 与被合并抹除的 "x" 语义不同，
        # 必须能从文本区分（否则同块两类标签会撞名）。
        out = []
        for i, v in enumerate(self.values):
            out.append("x" if i in self.frozen else _VALUE_TEXT[v])
        return ".".join(out)

    def update(self, slot: int, outcome: int) -> "Label":
        """经过第 ``slot`` 个条件：覆写最近结果；冻结槽不受影响。"""
        if slot in self.frozen:
            return self
        values = list(self.values)
        values[slot] = outcome
        return Label(tuple(values), self.frozen)

    def generalize(self, other: "Label") -> "Label":
        """两标签逐槽泛化（合并用）：一致保留，冲突槽抹成 UNKNOWN 并冻结。"""
        values = list(self.values)
        frozen = set(self.frozen) | set(other.frozen)
        for i, (a, b) in enumerate(zip(self.values, other.values)):
            if i in frozen:
                values[i] = UNKNOWN
            elif a == b:
                values[i] = a
            else:
                values[i] = UNKNOWN
                frozen.add(i)
        return Label(tuple(values), frozenset(frozen))

    def fine_members(self) -> frozenset[Label]:
        """γ(L)：本标签覆盖的细标签集合（冻结槽任取 ?/F/T）。"""
        options = []
        for i, v in enumerate(self.values):
            options.append(_SLOT_VALUES if i in self.frozen else (v,))
        return frozenset(
            Label(tuple(values), frozenset()) for values in product(*options)
        )

    def covers_fine(self, fine: "Label") -> bool:
        """细标签 ``fine`` 是否属于 γ(self)。"""
        for i, v in enumerate(self.values):
            if i not in self.frozen and fine.values[i] != v:
                return False
        return True

    def overlaps(self, other: "Label") -> bool:
        """两个（可能粗的）标签在细网格上是否有公共细标签。"""
        for i, (a, b) in enumerate(zip(self.values, other.values)):
            if i in self.frozen or i in other.frozen:
                continue
            if a != b:
                return False
        return True

    def to_dict(self) -> dict[str, object]:
        return {
            "values": list(self.values),
            "frozen": sorted(self.frozen),
            "text": self.text,
        }


@dataclass(frozen=True, slots=True)
class MergeEvent:
    """一次强制合并（分区数超过显式上限）。

    :param block: 合并发生的块（其输入汇聚处）。
    :param round: 合并发生时的上升迭代轮次。
    :param surviving: 合并后保留的标签（冲突槽已冻结为 UNKNOWN）。
    :param dropped: 本次并入幸存标签的原标签（按标签顺序排列）。
    :param partitions_after: 合并后该块剩余分区数。
    """

    block: str
    surviving: Label
    dropped: tuple[Label, ...]
    partitions_after: int
    round: int = 0

    @property
    def frozen_slots(self) -> tuple[int, ...]:
        """本次合并新抹除（冻结）的槽位（dropped 中此前未冻结者）。"""
        before: set[int] = set()
        for d in self.dropped:
            before |= d.frozen
        return tuple(sorted(self.surviving.frozen - before))

    @property
    def location(self) -> str:
        dropped = ", ".join(d.text for d in self.dropped)
        frozen = self.frozen_slots
        tail = f"；抹除槽位 {list(frozen)}" if frozen else ""
        return (
            f"block {self.block!r} 第 {self.round} 轮: 标签 [{dropped}] 合并为 "
            f"{self.surviving.text}（剩余 {self.partitions_after} 个分区{tail}）"
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "block": self.block,
            "round": self.round,
            "surviving": self.surviving.to_dict(),
            "dropped": [d.to_dict() for d in self.dropped],
            "partitions_after": self.partitions_after,
            "frozen_slots": list(self.frozen_slots),
        }


def coarsen_members(
    members: dict[Label, AbstractState],
    limit: int,
    block_name: str,
    round_no: int = 0,
) -> tuple[dict[Label, AbstractState], dict[Label, list[Label]], list[MergeEvent]]:
    """成员数超过 ``limit`` 时按标签顺序反复合并，直到不超限。

    每次取标签总序中最末两个，逐槽 :meth:`Label.generalize` 为一个幸存
    标签、区间取凸包；若幸存标签已存在则一并并入。合并是凸包守恒的
    （只重组标签、不改总凸包）。返回 (新成员表, 幸存标签 -> 原标签分组,
    合并事件)；未超限时分组即恒等映射、事件为空。
    """
    work = dict(members)
    groups: dict[Label, list[Label]] = {label: [label] for label in work}
    events: list[MergeEvent] = []
    while len(work) > limit:
        ordered = sorted(work, key=lambda l: l.order_key)
        first, second = ordered[-2], ordered[-1]
        surviving = first.generalize(second)
        # 被吸收的目标按值去重：surviving 可能按值等于 first/second
        # （first 已更粗时），也可能是第三个已存在标签。
        targets: list[Label] = [first, second]
        present = {first, second}
        if surviving not in present and surviving in work:
            targets.append(surviving)
            present.add(surviving)
        joined: AbstractState | None = None
        absorbed: list[Label] = []
        for target in targets:
            joined = work[target] if joined is None else joined.join(work[target])
            absorbed.extend(groups[target])
        assert joined is not None
        for target in targets:
            work.pop(target, None)
            groups.pop(target, None)
        work[surviving] = joined
        groups[surviving] = absorbed
        events.append(
            MergeEvent(
                block=block_name,
                surviving=surviving,
                dropped=tuple(targets),
                partitions_after=len(work),
                round=round_no,
            )
        )
    return work, groups, events


@dataclass(frozen=True, slots=True)
class PartitionedState:
    """标签 -> 区间状态的有限映射；**空映射即底（不可达）**。"""

    variables: tuple[str, ...]
    members: dict[Label, AbstractState]

    @classmethod
    def bottom_of(cls, variables: tuple[str, ...]) -> "PartitionedState":
        return cls(tuple(variables), {})

    @property
    def is_bottom(self) -> bool:
        return not self.members

    @property
    def labels(self) -> tuple[Label, ...]:
        return tuple(sorted(self.members, key=lambda l: l.order_key))

    # -- 聚合 / 传播 -----------------------------------------------------------

    def join_map(self, other: "PartitionedState") -> "PartitionedState":
        """逐标签凸包合并两张分区映射。"""
        members = dict(self.members)
        for label, state in other.members.items():
            if label in members:
                members[label] = members[label].join(state)
            else:
                members[label] = state
        return PartitionedState(self.variables, members)

    def transfer_map(self, block: Block) -> "PartitionedState":
        """块内语句转移：标签不变，逐分区做区间转移。"""
        return PartitionedState(
            self.variables,
            {label: transfer_block(state, block) for label, state in self.members.items()},
        )

    def through_edge(
        self, block: Block, succ_index: int, slot: int | None
    ) -> "PartitionedState":
        """源块出状态经到第 ``succ_index`` 个后继的边传播。

        * 先按块尾守卫做区间过滤（该分区下不可达的整支丢弃）；
        * 若源块是第 ``slot`` 个被跟踪条件，存活分区的标签槽位被覆写为
          本次真假（冻结槽除外）；多个旧标签映到同一新标签时取凸包。
        """
        if self.is_bottom or block.guard is None:
            return self
        outcome = TRUE if succ_index == 0 else FALSE
        members: dict[Label, AbstractState] = {}
        for label, state in self.members.items():
            filtered = edge_state(state, block, succ_index)
            if filtered.bottom:
                continue
            new_label = label.update(slot, outcome) if slot is not None else label
            if new_label in members:
                members[new_label] = members[new_label].join(filtered)
            else:
                members[new_label] = filtered
        return PartitionedState(self.variables, members)

    def convex_hull(self) -> AbstractState:
        """所有分区的区间凸包（= 不分区时该块应有的普通区间状态）。"""
        if not self.members:
            return AbstractState.bottom_of(self.variables)
        acc: AbstractState | None = None
        for state in self.members.values():
            acc = state if acc is None else acc.join(state)
        assert acc is not None
        return acc

    # -- 上限强制 ---------------------------------------------------------------

    def force_merge(
        self, limit: int, block_name: str, round_no: int = 0
    ) -> tuple["PartitionedState", list[MergeEvent]]:
        """成员数超过 ``limit`` 时按标签顺序反复合并，直到不超限。"""
        members, _groups, events = coarsen_members(
            self.members, limit, block_name, round_no
        )
        return PartitionedState(self.variables, members), events
