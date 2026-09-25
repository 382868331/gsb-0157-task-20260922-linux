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


def correlated_branches_program() -> CFG:
    """两分支分别设置不同区间、之后按同一条件再判断（分区模式的核心示例）。

    if (y >= 0) x = 1 else x = 2;
    if (y >= 0) assert x <= 1 else assert x >= 2

    凸包合并后 x ∈ [1,2] 且 y 的相关性丢失，两条断言都只能 unknown；
    以 sw1 为分区位置后，T 分区记住 y>=0、F 分区记住 y<=-1，第二个同样的
    守卫会把"走错支"的分区过滤成底，两条断言都可证。
    """
    return CFG(
        variables=("x", "y"),
        blocks={
            "sw1": Block("sw1", (), ("t1", "f1"), Guard("y", ">=", 0)),
            "t1": Block("t1", (AssignConst("x", 1),), ("sw2",)),
            "f1": Block("f1", (AssignConst("x", 2),), ("sw2",)),
            "sw2": Block("sw2", (), ("t2", "f2"), Guard("y", ">=", 0)),
            "t2": Block("t2", (AssertRange("x", None, 1),), ()),
            "f2": Block("f2", (AssertRange("x", 2, None),), ()),
        },
        entry="sw1",
    )


def loop_flip_program() -> CFG:
    """循环内指定条件的真/假每次迭代翻转（标签必须被更新而非固定）。

    i = 0; f = 0;
    while (i <= 2) {
        if (f >= 1) { x = 1; f = 0 } else { x = 0; f = 1 }   // sw：分区位置
        i = i + 1
    }
    assert 0 <= x <= 1
    """
    return CFG(
        variables=("i", "f", "x"),
        blocks={
            "init": Block(
                "init", (AssignConst("i", 0), AssignConst("f", 0)), ("head",)
            ),
            "head": Block("head", (), ("sw", "exit"), Guard("i", "<=", 2)),
            "sw": Block("sw", (), ("tt", "ff"), Guard("f", ">=", 1)),
            "tt": Block(
                "tt", (AssignConst("x", 1), AssignConst("f", 0)), ("step",)
            ),
            "ff": Block(
                "ff", (AssignConst("x", 0), AssignConst("f", 1)), ("step",)
            ),
            "step": Block("step", (AssignAdd("i", "i", 1),), ("head",)),
            "exit": Block("exit", (AssertRange("x", 0, 1),), ()),
        },
        entry="init",
    )


def merge_pressure_program() -> CFG:
    """三个顺序条件位置：2^3 = 8 种标签组合，用于强制合并测试。

    if (a >= 0) x = 1 else x = 2;
    if (b >= 0) y = 1 else y = 2;
    if (c >= 0) z = 1 else z = 2;
    assert 1<=x<=2; assert 1<=y<=2; assert 1<=z<=2
    """
    return CFG(
        variables=("a", "b", "c", "x", "y", "z"),
        blocks={
            "s1": Block("s1", (), ("t1", "f1"), Guard("a", ">=", 0)),
            "t1": Block("t1", (AssignConst("x", 1),), ("s2",)),
            "f1": Block("f1", (AssignConst("x", 2),), ("s2",)),
            "s2": Block("s2", (), ("t2", "f2"), Guard("b", ">=", 0)),
            "t2": Block("t2", (AssignConst("y", 1),), ("s3",)),
            "f2": Block("f2", (AssignConst("y", 2),), ("s3",)),
            "s3": Block("s3", (), ("t3", "f3"), Guard("c", ">=", 0)),
            "t3": Block("t3", (AssignConst("z", 1),), ("end",)),
            "f3": Block("f3", (AssignConst("z", 2),), ("end",)),
            "end": Block(
                "end",
                (
                    AssertRange("x", 1, 2),
                    AssertRange("y", 1, 2),
                    AssertRange("z", 1, 2),
                ),
                (),
            ),
        },
        entry="s1",
    )
