"""确定性测试夹具：仓库内代码构造的固定 CFG（无外部数据、无随机）。

这些构造函数同时供单元测试与 demo 使用，保证示例程序可复现。
"""

from interval_ai import (
    AssertRange,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
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
