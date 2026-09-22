"""确定性测试夹具：全部程序在代码内构造，无外部数据。"""

from interval_ai.cfg import (
    AddConst,
    AssertRange,
    Assign,
    Block,
    Cond,
    Copy,
    Jump,
    Program,
)


def bounded_two_branch_program() -> Program:
    """有界、两层条件、两条回边均被走过的程序（具体状态有限）。

    entry: x=0,y=0 -> h
    h:     x<=5 ? body : done
    body:  x+=1; x<=3 ? addY : h
    addY:  y+=1; assert x∈[1,6] -> h
    done:  assert x==6 (a_x)；y==3 与 y∈[0,3] 均 unknown

    具体执行：x 恒为 6 退出，y 恒为 3。区间域能经 narrowing 证明
    x==6，但 y 的自增受 x 上的条件保护，非关系域丢失相关性，
    h:y 抽象为 [0,+∞)——两个 y 断言只能 unknown（不是判错）。
    """
    return Program(
        variables=("x", "y"),
        blocks=(
            Block("entry", (Assign("x", 0), Assign("y", 0)), Jump("h")),
            Block("h", (), Cond("x", "<=", 5, "body", "done")),
            Block(
                "body",
                (AddConst("x", 1),),
                Cond("x", "<=", 3, "addY", "h"),
            ),
            Block(
                "addY",
                (AddConst("y", 1), AssertRange("x", 1, 6, "a_addy_x")),
                Jump("h"),
            ),
            Block(
                "done",
                (
                    AssertRange("x", 6, 6, "a_x"),
                    AssertRange("y", 3, 3, "a_y_exact"),
                    AssertRange("y", 0, 3, "a_y_wide"),
                ),
                None,
            ),
        ),
        entry="entry",
    )


def infinite_growth_program() -> Program:
    """无界增长：i=0; while(i>=0) i++; end（end 实际不可达）。

    h 处 i 抽象为 [0,+inf)，narrowing 也无法收紧；end 不可达。
    具体执行无界（参考器必须预算耗尽而非假装跑完）。
    end 中的断言按空真标 proved，reachable=False。
    """
    return Program(
        variables=("i",),
        blocks=(
            Block("entry", (Assign("i", 0),), Jump("h")),
            Block("h", (), Cond("i", ">=", 0, "body", "end")),
            Block("body", (AddConst("i", 1),), Jump("h")),
            Block("end", (AssertRange("i", -100, 100, "a_dead"),), None),
        ),
        entry="entry",
    )


def correlated_loop_program() -> Program:
    """经典非关系损失：x,y 同步增长，出口只按 x 过滤。

    x=0,y=0; while(x<=10){x++;y++;} 之后 x 恰为 11 可证，
    y 实际也是 11，但区间域给 y∈[0,11]：y==11 unknown，y∈[0,11] proved。
    """
    return Program(
        variables=("x", "y"),
        blocks=(
            Block("entry", (Assign("x", 0), Assign("y", 0)), Jump("h")),
            Block("h", (), Cond("x", "<=", 10, "body", "done")),
            Block("body", (AddConst("x", 1), AddConst("y", 1)), Jump("h")),
            Block(
                "done",
                (
                    AssertRange("x", 11, 11, "a_x"),
                    AssertRange("y", 11, 11, "a_y_exact"),
                    AssertRange("y", 0, 11, "a_y_wide"),
                ),
                None,
            ),
        ),
        entry="entry",
    )


def two_back_edges_program() -> Program:
    """两个回边的有界循环。

    h: i<=10 ? mid : end
    mid: i<=5 ? small(i+=1 ->h) : big(i+=2 ->h)
    出口 i ∈ {11,12}。回边 small->h、big->h 共两条。
    """
    return Program(
        variables=("i",),
        blocks=(
            Block("entry", (Assign("i", 0),), Jump("h")),
            Block("h", (), Cond("i", "<=", 10, "mid", "end")),
            Block("mid", (), Cond("i", "<=", 5, "small", "big")),
            Block("small", (AddConst("i", 1),), Jump("h")),
            Block("big", (AddConst("i", 2),), Jump("h")),
            Block("end", (AssertRange("i", 11, 12, "a_exit"),), None),
        ),
        entry="entry",
    )


def unreachable_branch_program() -> Program:
    """含恒假分支：x=0; if(x>=5) dead else live。

    dead 块不可达，其中断言按空真 proved；live 中 x 仍为 0。
    """
    return Program(
        variables=("x",),
        blocks=(
            Block("entry", (Assign("x", 0),), Cond("x", ">=", 5, "dead", "live")),
            Block("dead", (AssertRange("x", 999, 1000, "a_dead"),), None),
            Block("live", (AssertRange("x", 0, 0, "a_live"),), None),
        ),
        entry="entry",
    )


def copy_program() -> Program:
    """覆盖 Copy 语句：a=7; b=a; b+=3; assert b==10。"""
    return Program(
        variables=("a", "b"),
        blocks=(
            Block(
                "entry",
                (Assign("a", 7), Copy("b", "a"), AddConst("b", 3),
                 AssertRange("b", 10, 10, "a_b")),
                None,
            ),
        ),
        entry="entry",
    )


def nested_loop_program() -> Program:
    """两层计数循环：i=0; while i<=2 { j=0; while j<=2 j++; i++ }。

    出口 i 恰为 3（可证）。用来检验局部化 widening：内层头 hj 加宽
    时不得把外层变量 i 推到 +∞。
    """
    return Program(
        variables=("i", "j"),
        blocks=(
            Block("entry", (Assign("i", 0),), Jump("hi")),
            Block("hi", (), Cond("i", "<=", 2, "body", "done")),
            Block("body", (Assign("j", 0),), Jump("hj")),
            Block("hj", (), Cond("j", "<=", 2, "bj", "bi")),
            Block("bj", (AddConst("j", 1),), Jump("hj")),
            Block("bi", (AddConst("i", 1),), Jump("hi")),
            Block("done", (AssertRange("i", 3, 3, "a_i"),), None),
        ),
        entry="entry",
    )


def negative_counter_program() -> Program:
    """负向计数：i=0; while(i>=-5) i--; 出口 i 恰为 -6。

    检验下端点 widening（推到 -∞）与 narrowing 把它收回 -6。
    """
    return Program(
        variables=("i",),
        blocks=(
            Block("entry", (Assign("i", 0),), Jump("h")),
            Block("h", (), Cond("i", ">=", -5, "b", "d")),
            Block("b", (AddConst("i", -1),), Jump("h")),
            Block("d", (AssertRange("i", -6, -6, "a_i"),), None),
        ),
        entry="entry",
    )


def entry_is_header_program() -> Program:
    """入口块本身就是循环头：初值由 entry_state=(0,) 给定。"""
    return Program(
        variables=("i",),
        blocks=(
            Block("h", (), Cond("i", "<=", 3, "b", "d")),
            Block("b", (AddConst("i", 1),), Jump("h")),
            Block("d", (AssertRange("i", 4, 4, "a_i"),), None),
        ),
        entry="h",
        entry_state=(0,),
    )
