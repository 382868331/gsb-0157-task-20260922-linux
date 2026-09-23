"""确定性测试夹具：仓库内代码构造的固定 CFG（无外部数据、无随机）。

这些构造函数同时供单元测试与 demo 使用，保证示例程序可复现。
"""

from interval_ai import (
    AssertDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssumeDiff,
    Block,
    CFG,
    Guard,
    Interval,
)


def bounded_count_program(n: int = 4) -> CFG:
    """i = 0; while (i <= n) { assert 0<=i<=n; i = i+1 }; assert i == n+1.

    有界循环：具体执行有限；加宽后 exit 为 [n+1, +inf)，收窄改善为 [n+1, n+1]。
    """
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (),
                ("body", "exit"),
                Guard("i", "<=", n),
            ),
            "body": Block(
                "body",
                (AssertRange("i", 0, n), AssignAdd("i", "i", 1)),
                ("head",),
            ),
            "exit": Block(
                "exit",
                (AssertRange("i", n + 1, n + 1),),
                (),
            ),
        },
        entry="init",
    )


def unbounded_growth_program() -> CFG:
    """i = 0; while (i >= 0) { assert i>=0 (proved); assert i<=5 (unknown); i++ }.

    退出支不可达；循环头稳定在 [0, +inf)。
    """
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", 0, None), AssertRange("i", None, 5)),
                ("body", "exit"),
                Guard("i", ">=", 0),
            ),
            "body": Block("body", (AssignAdd("i", "i", 1),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def unreachable_branch_program() -> CFG:
    """x = 0; if (x >= 5) -> dead else cont；dead 块不可达。"""
    return CFG(
        variables=("x",),
        blocks={
            "init": Block("init", (AssignConst("x", 0),), ("fork",)),
            "fork": Block("fork", (), ("dead", "cont"), Guard("x", ">=", 5)),
            "dead": Block("dead", (AssertRange("x", 100, 200),), ()),
            "cont": Block("cont", (AssertRange("x", 0, 0),), ()),
        },
        entry="init",
    )


def two_backedges_program() -> CFG:
    """循环头有两个回边：l2 使 i+1，l3 使 i+2（由不相关变量 j 分派）。

    i = 0; while (i <= 9) { if (j >= 0) {i += 1} else {i += 2} }
    """
    return CFG(
        variables=("i", "j"),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", 0, 11),),
                ("fork", "exit"),
                Guard("i", "<=", 9),
            ),
            "fork": Block("fork", (), ("step1", "step2"), Guard("j", ">=", 0)),
            "step1": Block("step1", (AssignAdd("i", "i", 1),), ("head",)),
            "step2": Block("step2", (AssignAdd("i", "i", 2),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def copy_program() -> CFG:
    """覆盖复制语句与加负常量：a=3; b=a; c=b-1; assert c==2。"""
    from interval_ai import AssignCopy

    return CFG(
        variables=("a", "b", "c"),
        blocks={
            "start": Block(
                "start",
                (
                    AssignConst("a", 3),
                    AssignCopy("b", "a"),
                    AssignAdd("c", "b", -1),
                    AssertRange("c", 2, 2),
                ),
                (),
            ),
        },
        entry="start",
    )


# -- 差分约束（关系域）夹具 ----------------------------------------------------

def diff_copy_guard_program() -> CFG:
    """区间单独无法表达的变量差值：y = x 后在守卫 x<=0 真支上推出 y<=0。

    s: y = x;
    g: if (x <= 0) -> t else f;
    t: assert y - x <= 0; assert y <= 0; assert y - x <= 1（未知，放宽1）;
    f: skip
    """
    from interval_ai import AssignCopy

    return CFG(
        variables=("x", "y"),
        blocks={
            "s": Block("s", (AssignCopy("y", "x"),), ("g",)),
            "g": Block("g", (), ("t", "f"), Guard("x", "<=", 0)),
            "t": Block(
                "t",
                (
                    AssertDiff("y", "x", 0),
                    AssertRange("y", None, 0),
                    AssertDiff("y", "x", 1),
                ),
                (),
            ),
            "f": Block("f", (), ()),
        },
        entry="s",
    )


def diff_transitive_chain_program() -> CFG:
    """传递闭包：assume x-y<=1; assume y-z<=1。

    可证 x-z<=2；x-z<=1 不可证（unknown）。
    """
    return CFG(
        variables=("x", "y", "z"),
        blocks={
            "b": Block(
                "b",
                (
                    AssumeDiff("x", "y", 1),
                    AssumeDiff("y", "z", 1),
                    AssertDiff("x", "z", 2),
                    AssertDiff("x", "z", 1),
                ),
                (),
            ),
        },
        entry="b",
    )


def diff_contradiction_program() -> CFG:
    """矛盾假设使路径不可达：assume x-y<=0; assume y-x<=-1。"""
    return CFG(
        variables=("x", "y"),
        blocks={
            "b": Block(
                "b",
                (
                    AssumeDiff("x", "y", 0),
                    AssumeDiff("y", "x", -1),
                    AssertRange("x", 0, 0),
                    AssertDiff("x", "y", 5),
                ),
                (),
            ),
        },
        entry="b",
    )


def diff_merge_program() -> CFG:
    """分支合流：真支 x-y<=0、假支 x-y<=2，合流后只能证 x-y<=2。

    t ∈ [0,1]（入口区间）保证两支都可达。
    """
    return CFG(
        variables=("x", "y", "t"),
        blocks={
            "s": Block("s", (), ("g",)),
            "g": Block("g", (), ("a", "b2"), Guard("t", "<=", 0)),
            "a": Block("a", (AssumeDiff("x", "y", 0),), ("m",)),
            "b2": Block("b2", (AssumeDiff("x", "y", 2),), ("m",)),
            "m": Block(
                "m", (AssertDiff("x", "y", 2), AssertDiff("x", "y", 1)), ()
            ),
        },
        entry="s",
        entry_bounds={"t": Interval(0, 1)},
    )


def diff_loop_program() -> CFG:
    """有界关系循环：x=0; y=2; while(x<=3){ assert y-x==2; x++; y++ }。

    循环头关系不变量 y-x==2 在加宽/收窄后保持；exit 处 x==4、y==6。
    具体执行有限，可与抽象结果做覆盖性对照。
    """
    return CFG(
        variables=("x", "y"),
        blocks={
            "init": Block(
                "init",
                (AssignConst("x", 0), AssignConst("y", 2)),
                ("head",),
            ),
            "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 3)),
            "body": Block(
                "body",
                (
                    AssertDiff("y", "x", 2),
                    AssertDiff("x", "y", -2),
                    AssignAdd("x", "x", 1),
                    AssignAdd("y", "y", 1),
                ),
                ("head",),
            ),
            "exit": Block(
                "exit",
                (
                    AssertRange("x", 4, 4),
                    AssertRange("y", 6, 6),
                    AssertDiff("y", "x", 2),
                ),
                (),
            ),
        },
        entry="init",
    )


def diff_loop_initial_store() -> dict:
    return {"x": 0, "y": 2}


def diff_outer_invariant_program() -> CFG:
    """循环内不改的变量间关系不被加宽冲掉。

    i=0; x=7; y=x; while(i<=2){ assert y-x<=0; assert x-y<=0; i++ }。
    循环只修改 i；y==x 的差界在 init 建立、沿循环头合流，选择性加宽必须
    保留它（相关边不触及被加宽变量 i，取精确凸包而非推到 +∞）。
    """
    from interval_ai import AssignCopy

    return CFG(
        variables=("i", "x", "y"),
        blocks={
            "init": Block(
                "init",
                (AssignConst("i", 0), AssignConst("x", 7), AssignCopy("y", "x")),
                ("head",),
            ),
            "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 2)),
            "body": Block(
                "body",
                (
                    AssertDiff("y", "x", 0),
                    AssertDiff("x", "y", 0),
                    AssignAdd("i", "i", 1),
                ),
                ("head",),
            ),
            "exit": Block(
                "exit", (AssertDiff("y", "x", 0), AssertRange("y", 7, 7)), ()
            ),
        },
        entry="init",
    )
