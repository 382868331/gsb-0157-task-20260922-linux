"""CFG 公开数据结构与严格输入校验。

程序用 ``Program`` 表示：

* ``variables``：有序变量名列表（<= 20，非空）；
* ``blocks``：``Block`` 列表（<= 40，非空），每个块有唯一名字、若干条
  语句、至多一个出边条件 ``Branch``；
* ``entry``：入口块名；
* ``entry_state``：可选，入口处每个变量的具体初始值（全部变量都要给）；
  不给则全部初始化为 ``[0,0]``。

语句（``Statement``，不可变）四种：

* ``Assign("x", c)``      x := c          常量赋值
* ``Copy("x", "y")``      x := y          复制
* ``AddConst("x", c)``    x := x + c      加常量（c 可为负整数）
* ``AssertRange("x", lo, hi, id=...)``
      断言 x ∈ [lo, hi]，端点可为负；不改变状态；
      分析结果按 id 报告 proved / unknown。

分支（``Branch``）二选一：

* ``Cond("x", "<=", c, taken, skipped)``
      真边 ``taken``（x<=c），假边 ``skipped``（x>c）；
* ``Cond("x", ">=", c, taken, skipped)``
      真边（x>=c），假边（x<c）；
* ``Jump(target)`` 无条件跳转；
* 无分支：块可能无后继（出口块）。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal, Optional

from .errors import (
    DuplicateIdError,
    InconsistentGraphError,
    InvalidOperandError,
    LimitExceededError,
    ProgramStructureError,
)
from .interval import check_int

MAX_VARIABLES = 20
MAX_BLOCKS = 40
MAX_STATEMENTS_PER_BLOCK = 100

CondOp = Literal["<=", ">="]


def _check_name(name: object, what: str, where: str) -> str:
    if not isinstance(name, str) or not name:
        raise ProgramStructureError(
            f"{what}必须是非空 str，得到 {type(name).__name__}: {name!r}",
            where=where,
        )
    return name


class Statement:
    """语句基类；子类为冻结 dataclass，``kind`` 标识种类。"""

    kind: str = "?"

    def is_assert(self) -> bool:
        return False


@dataclass(frozen=True)
class Assign(Statement):
    """x := c（c 为有限 int；拒绝 bool）。"""

    var: str
    value: int
    kind: str = field(default="assign", init=False)

    def __post_init__(self) -> None:
        _check_name(self.var, "赋值目标变量名", "Assign")
        check_int(self.value, where=f"Assign({self.var!r})")


@dataclass(frozen=True)
class Copy(Statement):
    """x := y。"""

    var: str
    src: str
    kind: str = field(default="copy", init=False)

    def __post_init__(self) -> None:
        _check_name(self.var, "赋值目标变量名", "Copy")
        _check_name(self.src, "复制来源变量名", "Copy")


@dataclass(frozen=True)
class AddConst(Statement):
    """x := x + c（c 为有限 int，可为负）。"""

    var: str
    const: int
    kind: str = field(default="add_const", init=False)

    def __post_init__(self) -> None:
        _check_name(self.var, "加常量目标变量名", "AddConst")
        check_int(self.const, where=f"AddConst({self.var!r})")


@dataclass(frozen=True)
class AssertRange(Statement):
    """断言 var ∈ [lo, hi]；lo/hi 为有限 int，lo <= hi。"""

    var: str
    lo: int
    hi: int
    assert_id: str
    kind: str = field(default="assert", init=False)

    def __post_init__(self) -> None:
        _check_name(self.var, "断言变量名", "AssertRange")
        check_int(self.lo, where=f"AssertRange({self.assert_id!r}).lo")
        check_int(self.hi, where=f"AssertRange({self.assert_id!r}).hi")
        _check_name(self.assert_id, "断言 id", "AssertRange")
        if self.lo > self.hi:
            raise InvalidOperandError(
                f"断言 [{self.lo}, {self.hi}] 下界大于上界",
                where=f"AssertRange({self.assert_id!r})",
            )

    def is_assert(self) -> bool:
        return True


@dataclass(frozen=True)
class Jump:
    """无条件跳转。"""

    target: str
    kind: str = field(default="jump", init=False)

    def __post_init__(self) -> None:
        _check_name(self.target, "跳转目标块名", "Jump")


@dataclass(frozen=True)
class Cond:
    """条件分支：op 为 ``"<="`` 或 ``">="``。

    taken 为条件成立时的后继，skipped 为条件不成立（取反）时的后继。
    """

    var: str
    op: CondOp
    const: int
    taken: str
    skipped: str
    kind: str = field(default="cond", init=False)

    def __post_init__(self) -> None:
        _check_name(self.var, "条件变量名", "Cond")
        if self.op not in ("<=", ">="):
            raise ProgramStructureError(
                f"条件算符只允许 '<=' / '>='，得到 {self.op!r}",
                where="Cond",
            )
        check_int(self.const, where=f"Cond({self.var!r} {self.op})")
        _check_name(self.taken, "真边目标块名", "Cond")
        _check_name(self.skipped, "假边目标块名", "Cond")


Branch = Jump | Cond


@dataclass(frozen=True)
class Block:
    """基本块：名字 + 语句序列 + 可选出边。"""

    name: str
    statements: tuple[Statement, ...]
    branch: Optional[Branch] = None

    def __post_init__(self) -> None:
        _check_name(self.name, "块名", "Block")
        if not isinstance(self.statements, (tuple, list)):
            raise ProgramStructureError(
                f"statements 必须是 tuple/list，得到 {type(self.statements).__name__}",
                where=f"Block({self.name!r})",
            )
        # dataclass frozen：用 object.__setattr__ 归一化为 tuple
        stmts = tuple(self.statements)
        for i, st in enumerate(stmts):
            if not isinstance(st, Statement):
                raise ProgramStructureError(
                    f"第 {i} 条语句必须是 Statement，得到 {type(st).__name__}",
                    where=f"Block({self.name!r})",
                )
        if len(stmts) > MAX_STATEMENTS_PER_BLOCK:
            raise LimitExceededError(
                f"单块语句数 {len(stmts)} 超过上限 {MAX_STATEMENTS_PER_BLOCK}",
                where=f"Block({self.name!r})",
            )
        object.__setattr__(self, "statements", stmts)
        if self.branch is not None and not isinstance(self.branch, (Jump, Cond)):
            raise ProgramStructureError(
                f"branch 必须是 Jump/Cond/None，得到 {type(self.branch).__name__}",
                where=f"Block({self.name!r})",
            )

    @property
    def successors(self) -> tuple[str, ...]:
        """后继块名（去重；真/假边目标相同只列一次）。"""
        if self.branch is None:
            return ()
        if isinstance(self.branch, Jump):
            return (self.branch.target,)
        return tuple(dict.fromkeys((self.branch.taken, self.branch.skipped)))


@dataclass(frozen=True)
class Program:
    """完整 CFG 程序；构造时做全部结构校验，非法即抛、不产生半成品。"""

    variables: tuple[str, ...]
    blocks: tuple[Block, ...]
    entry: str
    entry_state: Optional[tuple[int, ...]] = None

    def __post_init__(self) -> None:
        self._validate()

    # ---- 校验（全部在构造期完成，失败即对象不存在，无部分变更）----
    def _validate(self) -> None:
        where = "Program"
        if not isinstance(self.variables, (tuple, list)) or not self.variables:
            raise ProgramStructureError("variables 必须是非空 tuple/list", where=where)
        variables = tuple(self.variables)
        for v in variables:
            _check_name(v, "变量名", where)
        if len(set(variables)) != len(variables):
            dup = _first_duplicate(variables)
            raise DuplicateIdError(f"变量名重复: {dup!r}", where=where)
        if len(variables) > MAX_VARIABLES:
            raise LimitExceededError(
                f"变量数 {len(variables)} 超过上限 {MAX_VARIABLES}", where=where
            )

        if not isinstance(self.blocks, (tuple, list)) or not self.blocks:
            raise ProgramStructureError("blocks 必须是非空 tuple/list", where=where)
        blocks = tuple(self.blocks)
        for b in blocks:
            if not isinstance(b, Block):
                raise ProgramStructureError(
                    f"块必须是 Block，得到 {type(b).__name__}", where=where
                )
        names = [b.name for b in blocks]
        if len(set(names)) != len(names):
            dup = _first_duplicate(names)
            raise DuplicateIdError(f"块名重复: {dup!r}", where=where)
        if len(blocks) > MAX_BLOCKS:
            raise LimitExceededError(
                f"块数 {len(blocks)} 超过上限 {MAX_BLOCKS}", where=where
            )
        name_set = set(names)
        _check_name(self.entry, "入口块名", where)
        if self.entry not in name_set:
            raise InconsistentGraphError(
                f"入口块 {self.entry!r} 不在块列表中", where=where
            )

        var_set = set(variables)
        seen_assert: set[str] = set()
        for b in blocks:
            for i, st in enumerate(b.statements):
                w = f"Block({b.name!r}).stmts[{i}]"
                if isinstance(st, (Assign, AddConst, AssertRange)) and st.var not in var_set:
                    raise InconsistentGraphError(
                        f"引用未声明变量 {st.var!r}", where=w
                    )
                if isinstance(st, Copy) and (st.var not in var_set or st.src not in var_set):
                    raise InconsistentGraphError(
                        f"引用未声明变量 (目标 {st.var!r}, 来源 {st.src!r})", where=w
                    )
                if isinstance(st, AssertRange):
                    if st.assert_id in seen_assert:
                        raise DuplicateIdError(
                            f"断言 id 重复: {st.assert_id!r}", where=w
                        )
                    seen_assert.add(st.assert_id)
            for succ in b.successors:
                if succ not in name_set:
                    raise InconsistentGraphError(
                        f"块 {b.name!r} 的后继 {succ!r} 不存在",
                        where=f"Block({b.name!r})",
                    )
            if isinstance(b.branch, Cond) and b.branch.var not in var_set:
                raise InconsistentGraphError(
                    f"条件引用未声明变量 {b.branch.var!r}",
                    where=f"Block({b.name!r})",
                )

        if self.entry_state is not None:
            if not isinstance(self.entry_state, (tuple, list)):
                raise ProgramStructureError(
                    "entry_state 必须是 tuple/list/None", where=where
                )
            vals = tuple(self.entry_state)
            if len(vals) != len(variables):
                raise ProgramStructureError(
                    f"entry_state 长度 {len(vals)} != 变量数 {len(variables)}",
                    where=where,
                )
            for i, val in enumerate(vals):
                check_int(val, where=f"entry_state[{variables[i]!r}]")
            object.__setattr__(self, "entry_state", vals)
        object.__setattr__(self, "variables", variables)
        object.__setattr__(self, "blocks", blocks)

    # ---- 便捷查询 ----
    @property
    def block_map(self) -> dict[str, Block]:
        return {b.name: b for b in self.blocks}

    @property
    def var_index(self) -> dict[str, int]:
        return {v: i for i, v in enumerate(self.variables)}

    @property
    def assert_ids(self) -> tuple[str, ...]:
        ids: list[str] = []
        for b in self.blocks:
            for st in b.statements:
                if isinstance(st, AssertRange):
                    ids.append(st.assert_id)
        return tuple(ids)


def _first_duplicate(items: list[str]) -> str:
    seen: set[str] = set()
    for x in items:
        if x in seen:
            return x
        seen.add(x)
    raise RuntimeError("unreachable")  # pragma: no cover
