"""控制流图（CFG）公开数据结构与构造期校验。

语言子集（数学整数变量，无除法、无乘法、无表达式混合）：

* ``AssignConst(target, c)``          -- target = c
* ``AssignCopy(target, source)``      -- target = source
* ``AssignAdd(target, source, k)``    -- target = source + k（k 可为负整数）
* ``AssertRange(target, lo, hi)``     -- 断言 lo <= target <= hi（不改变状态）
* ``AssumeDiff(a, b, c)``             -- 假设 a - b <= c（精化状态；不可行则该路径不可达）
* ``AssertDiff(a, b, c)``             -- 断言 a - b <= c（不改变状态；proved/unknown）

差分约束语句把关系域（x-y<=c 的差界矩阵，见 :mod:`interval_ai.dbm`）接入分析，
与逐变量区间构成归约积。含差分语句的 CFG 变量数至多
:data:`MAX_DIFF_VARIABLES`（4）；纯区间程序仍允许至多 :data:`MAX_VARIABLES`（20）。

分支由块尾 :class:`Guard` 表达：``Guard(x, "<=", c)`` 为真走 0 号后继，
为假（整数上即 x >= c+1）走 1 号后继；``">="`` 同理（假支 x <= c-1）。

所有结构在 ``__post_init__``/``CFG`` 构造时一次性校验，非法输入抛
:class:`~interval_ai.errors.ValidationError`（带定位）；构造失败不会产生
半成品对象，分析过程无外部可变状态，满足"失败不留部分变更"。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping, Sequence

from .errors import ValidationError, require_int
from .intervals import Interval

MAX_VARIABLES = 20
MAX_BLOCKS = 40
# 关系（差分约束）域只在至多 4 个变量的程序上启用（题面限定）。
MAX_DIFF_VARIABLES = 4
VALID_OPS = ("<=", ">=")


def _check_name(value: object, location: str, what: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValidationError(
            f"{what} must be a non-empty string, got {value!r}", location
        )
    return value


@dataclass(frozen=True, slots=True)
class AssignConst:
    target: str
    const: int

    def __post_init__(self) -> None:
        require_int(self.const, "AssignConst.const")


@dataclass(frozen=True, slots=True)
class AssignCopy:
    target: str
    source: str


@dataclass(frozen=True, slots=True)
class AssignAdd:
    target: str
    source: str
    const: int

    def __post_init__(self) -> None:
        require_int(self.const, "AssignAdd.const")


@dataclass(frozen=True, slots=True)
class AssertRange:
    """断言 lower <= target <= upper；端点允许为 ``None``（无穷）。

    例如 assert x <= c 写作 ``AssertRange(x, None, c)``，
    assert x >= c 写作 ``AssertRange(x, c, None)``。
    """

    target: str
    lower: int | None
    upper: int | None

    def __post_init__(self) -> None:
        if self.lower is not None:
            require_int(self.lower, "AssertRange.lower")
        if self.upper is not None:
            require_int(self.upper, "AssertRange.upper")
        if (
            self.lower is not None
            and self.upper is not None
            and self.lower > self.upper
        ):
            raise ValidationError(
                f"assert range [{self.lower}, {self.upper}] has lower > upper",
                "AssertRange",
            )


@dataclass(frozen=True, slots=True)
class AssumeDiff:
    """假设 ``a - b <= c``（c 为任意整数，可负）。

    语义为路径条件：把约束并入关系域并做闭包；若与已有约束矛盾，则当前
    路径不可达（后继状态为底），与守卫过滤掉整个整数补集一致。
    两个操作数必须是**已声明的不同变量**（``x - x <= c`` 之类在构造期拒绝）。
    """

    a: str
    b: str
    const: int

    def __post_init__(self) -> None:
        require_int(self.const, "AssumeDiff.const")


@dataclass(frozen=True, slots=True)
class AssertDiff:
    """断言 ``a - b <= c``；检查性语句，不改变抽象状态。

    分析在该语句位置判定关系域是否符号蕴含该差界：蕴含为 ``proved``，
    否则为 ``unknown``（无法证明不是错误，不抛异常）。
    """

    a: str
    b: str
    const: int

    def __post_init__(self) -> None:
        require_int(self.const, "AssertDiff.const")


Statement = (
    AssignConst | AssignCopy | AssignAdd | AssertRange | AssumeDiff | AssertDiff
)


@dataclass(frozen=True, slots=True)
class Guard:
    """块尾条件；successors 必须恰为 (true_block, false_block)。"""

    variable: str
    op: str
    const: int

    def __post_init__(self) -> None:
        if self.op not in VALID_OPS:
            raise ValidationError(
                f"guard op must be one of {VALID_OPS}, got {self.op!r}", "Guard.op"
            )
        require_int(self.const, "Guard.const")


@dataclass(frozen=True, slots=True)
class Block:
    name: str
    statements: tuple[Statement, ...] = ()
    successors: tuple[str, ...] = ()
    guard: Guard | None = None

    def __post_init__(self) -> None:
        _check_name(self.name, "Block.name", "block name")
        if not isinstance(self.statements, tuple):
            object.__setattr__(self, "statements", tuple(self.statements))
        if not isinstance(self.successors, tuple):
            object.__setattr__(self, "successors", tuple(self.successors))


@dataclass(frozen=True, slots=True)
class CFG:
    """完整控制流图。

    :param variables: 变量名序列（互不相同，至多 20 个）。
    :param blocks: ``{块名: Block}``（至多 40 块；插入顺序作为枚举顺序之一）。
    :param entry: 入口块名。
    :param entry_bounds: 入口变量的可选初始区间（缺省全部为 [-∞,+∞]）。
    """

    variables: tuple[str, ...]
    blocks: Mapping[str, Block]
    entry: str
    entry_bounds: Mapping[str, Interval] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self._validate()

    # -- 校验 ----------------------------------------------------------------

    def _validate(self) -> None:
        loc = "CFG"
        if not isinstance(self.variables, (tuple, list)):
            raise ValidationError("variables must be a tuple/list of names", loc)
        variables = tuple(self.variables)
        if not variables:
            raise ValidationError("at least one variable is required", "CFG.variables")
        if len(variables) > MAX_VARIABLES:
            raise ValidationError(
                f"too many variables: {len(variables)} > {MAX_VARIABLES}",
                "CFG.variables",
            )
        seen: set[str] = set()
        for i, v in enumerate(variables):
            _check_name(v, f"CFG.variables[{i}]", "variable name")
            if v in seen:
                raise ValidationError(
                    f"duplicate variable name {v!r}", f"CFG.variables[{i}]"
                )
            seen.add(v)
        vset = set(variables)
        object.__setattr__(self, "variables", variables)

        if not isinstance(self.blocks, Mapping):
            raise ValidationError("blocks must be a mapping name -> Block", "CFG.blocks")
        if not self.blocks:
            raise ValidationError("at least one block is required", "CFG.blocks")
        if len(self.blocks) > MAX_BLOCKS:
            raise ValidationError(
                f"too many blocks: {len(self.blocks)} > {MAX_BLOCKS}", "CFG.blocks"
            )

        # 先扫描语句类型：含差分约束的程序变量数上限为 MAX_DIFF_VARIABLES。
        uses_diff_domain = any(
            isinstance(block, Block)
            and any(isinstance(st, (AssumeDiff, AssertDiff)) for st in block.statements)
            for block in self.blocks.values()
        )
        if uses_diff_domain and len(variables) > MAX_DIFF_VARIABLES:
            raise ValidationError(
                f"programs with difference constraints allow at most "
                f"{MAX_DIFF_VARIABLES} variables, got {len(variables)}",
                "CFG.variables",
            )
        names: set[str] = set()
        for bname, block in self.blocks.items():
            bloc = f"block {bname!r}"
            if not isinstance(block, Block):
                raise ValidationError(
                    f"value must be a Block, got {type(block).__name__}", bloc
                )
            if block.name != bname:
                raise ValidationError(
                    f"mapping key {bname!r} != Block.name {block.name!r}", bloc
                )
            if bname in names:  # dict 自身去重，保留给非 Mapping 构造路径的防御
                raise ValidationError(f"duplicate block name {bname!r}", "CFG.blocks")
            names.add(bname)
            for i, st in enumerate(block.statements):
                self._validate_statement(st, f"{bloc}.stmts[{i}]", vset)
            if block.guard is not None:
                g = block.guard
                if not isinstance(g, Guard):
                    raise ValidationError("guard must be a Guard instance", f"{bloc}.guard")
                if g.variable not in vset:
                    raise ValidationError(
                        f"guard variable {g.variable!r} is not declared",
                        f"{bloc}.guard.variable",
                    )
            nsucc = len(block.successors)
            if nsucc not in (0, 1, 2):
                raise ValidationError(
                    f"block must have 0, 1 or 2 successors, got {nsucc}",
                    f"{bloc}.successors",
                )
            if block.guard is None and nsucc == 2:
                raise ValidationError(
                    "block with 2 successors must declare a Guard", f"{bloc}.guard"
                )
            if block.guard is not None and nsucc != 2:
                raise ValidationError(
                    "block with a Guard must have exactly 2 successors (true, false)",
                    f"{bloc}.successors",
                )
            for j, s in enumerate(block.successors):
                if s not in self.blocks:
                    raise ValidationError(
                        f"successor {s!r} does not exist", f"{bloc}.successors[{j}]"
                    )

        _check_name(self.entry, "CFG.entry", "entry name")
        if self.entry not in self.blocks:
            raise ValidationError(
                f"entry block {self.entry!r} does not exist", "CFG.entry"
            )

        bounds = dict(self.entry_bounds)
        for key, val in bounds.items():
            if key not in vset:
                raise ValidationError(
                    f"entry_bounds variable {key!r} is not declared",
                    f"CFG.entry_bounds[{key!r}]",
                )
            if not isinstance(val, Interval):
                raise ValidationError(
                    f"entry bound must be Interval, got {type(val).__name__}",
                    f"CFG.entry_bounds[{key!r}]",
                )
        object.__setattr__(self, "entry_bounds", bounds)

    def _validate_statement(self, st: object, loc: str, vset: set[str]) -> None:
        if isinstance(st, AssignConst):
            if st.target not in vset:
                raise ValidationError(
                    f"target {st.target!r} is not declared", f"{loc}.target"
                )
        elif isinstance(st, AssignCopy):
            if st.target not in vset:
                raise ValidationError(
                    f"target {st.target!r} is not declared", f"{loc}.target"
                )
            if st.source not in vset:
                raise ValidationError(
                    f"source {st.source!r} is not declared", f"{loc}.source"
                )
        elif isinstance(st, AssignAdd):
            if st.target not in vset:
                raise ValidationError(
                    f"target {st.target!r} is not declared", f"{loc}.target"
                )
            if st.source not in vset:
                raise ValidationError(
                    f"source {st.source!r} is not declared", f"{loc}.source"
                )
        elif isinstance(st, AssertRange):
            if st.target not in vset:
                raise ValidationError(
                    f"target {st.target!r} is not declared", f"{loc}.target"
                )
        elif isinstance(st, (AssumeDiff, AssertDiff)):
            kind = type(st).__name__
            for operand_name, operand in (("a", st.a), ("b", st.b)):
                if not isinstance(operand, str) or not operand:
                    raise ValidationError(
                        f"{kind}.{operand_name} must be a non-empty string, "
                        f"got {operand!r}",
                        f"{loc}.{operand_name}",
                    )
                if operand not in vset:
                    raise ValidationError(
                        f"{kind} operand {operand!r} is not declared",
                        f"{loc}.{operand_name}",
                    )
            if st.a == st.b:
                raise ValidationError(
                    f"{kind} operands must be distinct variables, got {st.a!r} twice",
                    f"{loc}.a",
                )
        else:
            raise ValidationError(
                f"unknown statement type {type(st).__name__}", loc
            )

    # -- 便利访问 -------------------------------------------------------------

    @property
    def variable_tuple(self) -> tuple[str, ...]:
        return tuple(self.variables)

    @property
    def uses_diff_domain(self) -> bool:
        """程序是否含差分约束语句（含则关系域启用、变量数 ≤ 4）。"""
        return any(
            isinstance(st, (AssumeDiff, AssertDiff))
            for block in self.blocks.values()
            for st in block.statements
        )

    def initial_state_intervals(self) -> dict[str, Interval]:
        top = {v: Interval.top() for v in self.variables}
        top.update(self.entry_bounds)
        return top
