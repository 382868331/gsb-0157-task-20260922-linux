"""不动点分析器：循环头延迟 widening + 最多 8 轮 narrowing。

迭代协议（仅对 DFS 识别出的回边目标——循环头——做加宽/收窄）：

* 上升阶段按逆后序（RPO）做混沌迭代。循环头的入状态每次真正变大
  记一次“扩张”：第 1、2 次扩张用普通凸包 join；**第 3 次扩张起**
  使用经典区间 widening（变化的端点直接推到 ±∞）。其余块每轮
  直接重算入状态。
* 全局稳定（达到后置不动点）后进入下降阶段：循环头用经典
  narrowing 收回无穷端点，其余块随前驱收紧而重算；**最多 8 轮**，
  任一轮全局无变化即提前停止。
* widening 保证有限变量的区间链有限步终止；预算耗尽抛
  :class:`AnalyzerBudgetExhausted`，与结论 unknown 严格区分。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from .cfg import (
    AddConst,
    AssertRange,
    Assign,
    Block,
    Copy,
    Program,
)
from .errors import AnalyzerBudgetExhausted
from .semantics import apply_block_body, apply_statement, branch_outputs
from .state import State

DEFAULT_MAX_ROUNDS = 200
DEFAULT_MAX_NARROWING = 8


@dataclass(frozen=True)
class AssertResult:
    """单条 assert 的结论。

    status: ``"proved"``（区间被包含于断言范围；不可达块中按空真
    亦为 proved，此时 reachable=False）或 ``"unknown"``（无法证明，
    不表示断言为错）。
    """

    assert_id: str
    block: str
    var: str
    lo: int
    hi: int
    status: str
    reachable: bool
    observed: Optional[dict]

    def to_dict(self) -> dict:
        return {
            "assert_id": self.assert_id,
            "block": self.block,
            "var": self.var,
            "range": {"lo": self.lo, "hi": self.hi},
            "status": self.status,
            "reachable": self.reachable,
            "observed_interval": self.observed,
        }


@dataclass(frozen=True)
class AnalysisResult:
    """分析结果：每块入/出不变量、边状态、assert 结论、迭代统计。"""

    program: Program
    in_states: dict[str, State]
    out_states: dict[str, State]
    edge_states: dict[tuple[str, str], State]
    assertions: tuple[AssertResult, ...]
    loop_headers: tuple[str, ...]
    back_edges: tuple[tuple[str, str], ...]
    ascending_rounds: int
    narrowing_rounds: int
    widen_expansions: dict[str, int]

    def block_invariant(self, name: str) -> dict:
        return {
            "block": name,
            "is_loop_header": name in self.loop_headers,
            "entry": self.in_states[name].to_dict(self.program),
            "exit": self.out_states[name].to_dict(self.program),
        }

    def all_invariants(self) -> list[dict]:
        return [self.block_invariant(b.name) for b in self.program.blocks]

    def status_of(self, assert_id: str) -> str:
        for a in self.assertions:
            if a.assert_id == assert_id:
                return a.status
        raise KeyError(assert_id)

    def to_dict(self) -> dict:
        return {
            "loop_headers": list(self.loop_headers),
            "back_edges": [[a, b] for a, b in self.back_edges],
            "ascending_rounds": self.ascending_rounds,
            "narrowing_rounds": self.narrowing_rounds,
            "widen_expansions": dict(self.widen_expansions),
            "blocks": self.all_invariants(),
            "edges": [
                {
                    "from": a,
                    "to": b,
                    "state": s.to_dict(self.program),
                }
                for (a, b), s in self.edge_states.items()
            ],
            "assertions": [a.to_dict() for a in self.assertions],
        }


class Analyzer:
    """区间抽象解释分析器（一次性使用，每次 analyze 全新建表）。"""

    def __init__(
        self,
        program: Program,
        *,
        max_rounds: int = DEFAULT_MAX_ROUNDS,
        max_narrowing: int = DEFAULT_MAX_NARROWING,
    ) -> None:
        if isinstance(max_rounds, bool) or not isinstance(max_rounds, int):
            raise TypeError("max_rounds 必须是 int")
        if isinstance(max_narrowing, bool) or not isinstance(max_narrowing, int):
            raise TypeError("max_narrowing 必须是 int")
        if max_rounds < 1 or not (0 <= max_narrowing <= 8):
            raise ValueError("max_rounds>=1 且 0<=max_narrowing<=8")
        self.program = program
        self.max_rounds = max_rounds
        self.max_narrowing = max_narrowing

        self.blocks = program.blocks
        self.block_map = program.block_map
        self.preds: dict[str, list[str]] = {b.name: [] for b in self.blocks}
        for b in self.blocks:
            for s in dict.fromkeys(b.successors):  # 去重：真/假边可能同目标
                self.preds[s].append(b.name)

        self.back_edges, self.headers, order = _dfs_structure(program)
        # RPO 后补上从 entry 不可达的块（保持声明顺序），它们恒为 bottom。
        reachable = set(order)
        for b in self.blocks:
            if b.name not in reachable:
                order.append(b.name)
        self.order: list[str] = order
        self.header_set = set(self.headers)

        # 局部化 widening：每个循环头只加宽“本循环回边路径上被赋值”
        # 的变量。循环体由回边源反向 BFS（不跨入头本身）得到。
        self.header_masks: dict[str, tuple[bool, ...]] = {}
        written = _block_written_vars(program)
        for h in self.headers:
            body_nodes = _loop_body_nodes(h, self.back_edges, self.preds)
            names = set()
            for node in body_nodes:
                names |= written[node]
            self.header_masks[h] = tuple(v in names for v in program.variables)

        self.in_states: dict[str, State] = {}
        self.out_body: dict[str, State] = {}
        self.edges: dict[tuple[str, str], State] = {}
        self.expansions: dict[str, int] = {h: 0 for h in self.headers}

    # ---- 主入口 ----
    def analyze(self) -> AnalysisResult:
        entry_init = State.entry_state(self.program)
        bottom = lambda: State.bottom(self.program)
        self.in_states = {b.name: bottom() for b in self.blocks}
        self.out_body = {b.name: bottom() for b in self.blocks}
        self.edges = {
            (b.name, s): bottom() for b in self.blocks for s in b.successors
        }

        # ===== 上升阶段 =====
        rounds = 0
        while True:
            rounds += 1
            if rounds > self.max_rounds:
                raise AnalyzerBudgetExhausted(
                    f"上升迭代 {self.max_rounds} 轮后仍未稳定"
                    f"（最后处理顺序: {' -> '.join(self.order)}）",
                    where="Analyzer.analyze",
                )
            changed = False
            for name in self.order:
                new_in = self._ascending_incoming(name, entry_init)
                if new_in != self.in_states[name]:
                    self.in_states[name] = new_in
                    changed = True
                self._recompute_out(name)
            if not changed:
                break

        ascending_rounds = rounds

        # ===== 下降（narrowing）阶段 =====
        narrowing_rounds = 0
        for nr in range(1, self.max_narrowing + 1):
            changed = False
            for name in self.order:
                new_in = self._descending_incoming(name, entry_init)
                if new_in != self.in_states[name]:
                    self.in_states[name] = new_in
                    changed = True
                self._recompute_out(name)
            narrowing_rounds = nr
            if not changed:
                break

        assertions = self._collect_asserts()
        return AnalysisResult(
            program=self.program,
            in_states=dict(self.in_states),
            out_states=dict(self.out_body),
            edge_states=dict(self.edges),
            assertions=assertions,
            loop_headers=tuple(h for h in self.headers),
            back_edges=tuple(self.back_edges),
            ascending_rounds=ascending_rounds,
            narrowing_rounds=narrowing_rounds,
            widen_expansions=dict(self.expansions),
        )

    # ---- 入状态计算 ----
    def _join_incoming(self, name: str, entry_init: State) -> State:
        contribs: list[State] = []
        if name == self.program.entry:
            contribs.append(entry_init)
        for p in self.preds[name]:
            contribs.append(self.edges[(p, name)])
        if not contribs:
            return State.bottom(self.program)
        acc = contribs[0]
        for c in contribs[1:]:
            acc = State.join(acc, c)
        return acc

    def _ascending_incoming(self, name: str, entry_init: State) -> State:
        incoming = self._join_incoming(name, entry_init)
        if name not in self.header_set:
            return incoming
        cur = self.in_states[name]
        if not cur.reachable:
            return incoming  # 第一次到达
        if incoming <= cur:
            return cur  # 无扩张
        self.expansions[name] += 1
        if self.expansions[name] >= 3:
            # 第 3 次扩张起标准 widening（局部化到本循环修改的变量）。
            return State.widen(
                cur,
                State.join(cur, incoming),
                self.header_masks[name],
            )
        return State.join(cur, incoming)

    def _descending_incoming(self, name: str, entry_init: State) -> State:
        incoming = self._join_incoming(name, entry_init)
        if name not in self.header_set:
            return incoming
        cur = self.in_states[name]
        if not cur.reachable:
            return incoming
        # 后置不动点上 F(cur) ⊆ cur；各前驱的新贡献分别都 ⊆ cur。
        return State.narrow(cur, incoming)

    def _recompute_out(self, name: str) -> None:
        block = self.block_map[name]
        out = apply_block_body(self.in_states[name], block, self.program)
        self.out_body[name] = out
        edge_outs = branch_outputs(out, block, self.program)
        for succ, st in edge_outs.items():
            self.edges[(name, succ)] = st

    # ---- assert 结论 ----
    def _collect_asserts(self) -> tuple[AssertResult, ...]:
        results: list[AssertResult] = []
        for block in self.blocks:
            cur = self.in_states[block.name]
            for st in block.statements:
                if isinstance(st, AssertRange):
                    reachable = cur.reachable
                    if reachable:
                        iv = cur.get(st.var, self.program)
                        obs = iv.to_dict()
                        lo_ok = iv.lo is not None and iv.lo >= st.lo
                        hi_ok = iv.hi is not None and iv.hi <= st.hi
                        proved = lo_ok and hi_ok
                    else:
                        obs = None
                        proved = True  # 空真：不可达路径上的断言平凡成立
                    results.append(
                        AssertResult(
                            assert_id=st.assert_id,
                            block=block.name,
                            var=st.var,
                            lo=st.lo,
                            hi=st.hi,
                            status="proved" if proved else "unknown",
                            reachable=reachable,
                            observed=obs,
                        )
                    )
                cur = apply_statement(cur, st, self.program)
        return tuple(results)


def _dfs_structure(program: Program) -> tuple[list[tuple[str, str]], list[str], list[str]]:
    """DFS：返回 (回边列表, 循环头（回边目标，保持发现顺序）, RPO)。

    三色 DFS：指向 GRAY（当前 DFS 栈中）祖先的边为回边。
    """
    block_map = program.block_map
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {b.name: WHITE for b in program.blocks}
    back: list[tuple[str, str]] = []
    header_order: list[str] = []
    header_seen: set[str] = set()
    rpo: list[str] = []

    def visit(name: str) -> None:
        color[name] = GRAY
        for succ in block_map[name].successors:
            if color[succ] == WHITE:
                visit(succ)
            elif color[succ] == GRAY:
                back.append((name, succ))
                if succ not in header_seen:
                    header_seen.add(succ)
                    header_order.append(succ)
            # BLACK -> 前向/交叉边，忽略
        color[name] = BLACK
        rpo.append(name)

    visit(program.entry)
    rpo.reverse()
    return back, header_order, rpo


def _block_written_vars(program: Program) -> dict[str, set[str]]:
    """每个块内被赋值（Assign/Copy/AddConst）的变量集合。"""
    written: dict[str, set[str]] = {}
    for b in program.blocks:
        names = {
            st.var
            for st in b.statements
            if isinstance(st, (Assign, Copy, AddConst))
        }
        written[b.name] = names
    return written


def _loop_body_nodes(
    header: str,
    back_edges: list[tuple[str, str]],
    preds: dict[str, list[str]],
) -> set[str]:
    """由所有指向 header 的回边源出发，沿前驱反向 BFS。

    不跨入 header 自身。得到的节点集合即“能沿本循环回到 header”的
    循环体节点（嵌套内层循环整体包含在内）。
    """
    starts = [src for src, dst in back_edges if dst == header]
    seen: set[str] = set()
    stack = list(starts)
    while stack:
        node = stack.pop()
        if node in seen or node == header:
            continue
        seen.add(node)
        for p in preds.get(node, ()):
            if p not in seen and p != header:
                stack.append(p)
    return seen


def analyze(program: Program, **kwargs) -> AnalysisResult:
    """便捷函数：对 program 跑一遍区间抽象解释。"""
    return Analyzer(program, **kwargs).analyze()
