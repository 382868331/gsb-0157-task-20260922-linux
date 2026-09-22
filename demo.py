#!/usr/bin/env python3
"""固定输入演示：区间抽象解释的 proved 与 unknown，以及一个真实触发的拒绝。

运行：``python demo.py``（约毫秒级，无 sleep、无网络、无预录结果）。

程序（确定性地在本文件内构造）::

    x = 0; y = 0
    while x <= 10:
        x = x + 1
        y = y + 1
    # 出口：x 恰为 11；y 运行时也恰为 11，但区间域丢失 x,y 的相关性
    assert x == 11      # 期望 proved（narrowing 把 +∞ 收回 11）
    assert y == 11      # 期望 unknown（非关系域，不判为错误）
    assert y <= 11      # 同样 unknown（y 连有限上界都得不到）

结尾再真实构造一个非法输入（把 bool 当整数常量），展示可定位拒绝。
"""

from __future__ import annotations

from interval_ai import (
    AddConst,
    AssertRange,
    Assign,
    Block,
    Cond,
    InvalidOperandError,
    Jump,
    Program,
    analyze,
    check_analysis,
)
from interval_ai.interval import Interval


def build_program() -> Program:
    return Program(
        variables=("x", "y"),
        blocks=(
            Block("entry", (Assign("x", 0), Assign("y", 0)), Jump("head")),
            Block("head", (), Cond("x", "<=", 10, "body", "done")),
            Block("body", (AddConst("x", 1), AddConst("y", 1)), Jump("head")),
            Block(
                "done",
                (
                    AssertRange("x", 11, 11, "assert_x_eq_11"),
                    AssertRange("y", 11, 11, "assert_y_eq_11"),
                    AssertRange("y", 0, 11, "assert_y_le_11"),
                ),
                None,
            ),
        ),
        entry="entry",
    )


def fmt_iv(iv: Interval | None) -> str:
    if iv is None:
        return "  BOTTOM(不可达)"
    lo = "-inf" if iv.lo is None else str(iv.lo)
    hi = "+inf" if iv.hi is None else str(iv.hi)
    return f"[{lo:>4}, {hi:>4}]"


def main() -> None:
    prog = build_program()
    result = analyze(prog)

    print("=" * 68)
    print("演示程序： x=0,y=0; while(x<=10){x+=1;y+=1}")
    print("=" * 68)
    print(
        f"回边 {list(result.back_edges)}；循环头 {list(result.loop_headers)}；"
        f"上升 {result.ascending_rounds} 轮，收窄 {result.narrowing_rounds} 轮"
        f"（上限 8），head 扩张计数 {result.widen_expansions}"
    )
    print("-" * 68)
    print(f"{'块':<7} {'入/出':<4} {'x':<14} {'y':<14}")
    for block in prog.blocks:
        for side, state in (("入", result.in_states[block.name]),
                            ("出", result.out_states[block.name])):
            if not state.reachable:
                print(f"{block.name:<7} {side:<4} {'BOTTOM':<14} {'BOTTOM':<14}")
                continue
            d = state.to_dict(prog)
            x = Interval(d["x"]["lo"], d["x"]["hi"])
            y = Interval(d["y"]["lo"], d["y"]["hi"])
            print(f"{block.name:<7} {side:<4} {fmt_iv(x):<14} {fmt_iv(y):<14}")
    print("-" * 68)
    print("断言结论（unknown 表示无法证明，不代表断言为错）：")
    for a in result.assertions:
        obs = "不可达" if a.observed is None else (
            f"观察到 {a.var}∈[{a.observed['lo']}, {a.observed['hi']}]"
        )
        print(f"  {a.assert_id:<16} -> {a.status.upper():<7} ({obs})")

    assert result.status_of("assert_x_eq_11") == "proved"
    assert result.status_of("assert_y_eq_11") == "unknown"
    assert result.status_of("assert_y_le_11") == "unknown"

    # 独立局部转移包含性证书检查（符号证明，非采样）
    report = check_analysis(prog, result)
    print("-" * 68)
    print(f"独立包含性证书检查：{'全部通过（证书可靠）' if report.holds else '失败'}")
    print(f"证明方式：{report.proof_method}；检查条目数：{len(report.items)}")
    assert report.holds

    # ---- 真实触发的拒绝边界：bool 不允许冒充整数常量 ----
    print("=" * 68)
    print("非法输入边界：尝试 x := True（bool 不是本题意义上的整数）")
    try:
        Assign("x", True)
    except InvalidOperandError as e:
        print(f"  如预期拒绝 -> {type(e).__name__}: {e}")
    else:  # pragma: no cover
        raise RuntimeError("非法输入未被拒绝")

    # 同样拒绝 float NaN（数值输入拒绝 NaN/Infinity）
    try:
        AddConst("x", float("nan"))
    except InvalidOperandError as e:
        print(f"  如预期拒绝 -> {type(e).__name__}: {e}")

    print("=" * 68)
    print("演示完成：1 个 proved、2 个 unknown，2 个可定位的非法输入拒绝。")


if __name__ == "__main__":
    main()
