"""固定输入演示：整数循环的区间抽象解释 + 差分约束关系域。

运行：``python demo.py``（Python 3.14，仅标准库；无网络、无 sleep、无预录结果）。

演示内容：
1. 有界循环：每块入/出不变量、断言 proved、收窄改善（[n+1,+inf) -> [n+1,n+1]）；
2. 无界增长循环：同一点位断言只能给出 unknown（不是错误）；
3. 独立符号包含性检查器复核结果；
4. 独立具体执行器对有界程序做覆盖性对照；
5. 新增 x-y<=c 差分约束：赋值、分支合流、循环入口三处与区间交换信息，
   证明区间单独无法表达的变量差值关系；并展示未在迭代预算内收敛时
   差分断言明确返回 unknown（不冒充证明）；
6. 真实触发的拒绝边界：bool 常量与超规模差分组分别被 ValidationError 拒绝。
"""

from __future__ import annotations

from interval_ai import (
    AssertDiff,
    AssumeDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    IntervalAIError,
    analyze,
    check_local_soundness,
    run_bounded,
)


def bounded_loop(n: int) -> CFG:
    # i = 0; while (i <= n) { assert 0 <= i <= n; i = i + 1 }; assert i == n + 1
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block("head", (), ("body", "exit"), Guard("i", "<=", n)),
            "body": Block(
                "body",
                (AssertRange("i", 0, n), AssignAdd("i", "i", 1)),
                ("head",),
            ),
            "exit": Block("exit", (AssertRange("i", n + 1, n + 1),), ()),
        },
        entry="init",
    )


def unbounded_loop() -> CFG:
    # i = 0; while (i >= 0) { assert i <= 5; i = i + 1 }
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", None, 5),),
                ("body", "exit"),
                Guard("i", ">=", 0),
            ),
            "body": Block("body", (AssignAdd("i", "i", 1),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def diff_loop() -> CFG:
    # x = 0; y = 1;
    # while (x <= 4) { assert y - x <= 1; assert x - y <= -1; x++; y++ }
    # assert y - x <= 1（循环出口仍成立）；区间无法单独推出任何跨变量界。
    return CFG(
        variables=("x", "y"),
        blocks={
            "init": Block(
                "init", (AssignConst("x", 0), AssignConst("y", 1)), ("head",)
            ),
            "head": Block("head", (), ("body", "exit"), Guard("x", "<=", 4)),
            "body": Block(
                "body",
                (
                    AssertDiff("y", "x", 1),
                    AssertDiff("x", "y", -1),
                    AssignAdd("x", "x", 1),
                    AssignAdd("y", "y", 1),
                ),
                ("head",),
            ),
            "exit": Block("exit", (AssertDiff("y", "x", 1),), ()),
        },
        entry="init",
    )


def diff_merge() -> CFG:
    # x = 0; if (j >= 0) { y = 0 } else { y = 1 }; 合流后 x - y <= 0。
    # 区间合流只得到 y in [0,1]；两支的 DBM 界（0 与 -1）合流为 0。
    return CFG(
        variables=("x", "y", "j"),
        blocks={
            "s": Block("s", (AssignConst("x", 0),), ("g",)),
            "g": Block("g", (), ("a", "b"), Guard("j", ">=", 0)),
            "a": Block("a", (AssignConst("y", 0),), ("m",)),
            "b": Block("b", (AssignConst("y", 1),), ("m",)),
            "m": Block(
                "m",
                (AssertRange("y", 0, 1), AssertDiff("x", "y", 0)),
                (),
            ),
        },
        entry="s",
    )


def print_result(title: str, result) -> None:
    print(f"--- {title}")
    print(f"加宽点: {list(result.widen_points)}；"
          f"上升 {result.ascending_rounds} 轮，收窄 {result.narrowing_rounds} 轮")
    for name in result.cfg.blocks:
        print(f"  {name:5} 入 {result.block_in[name].text}")
        print(f"  {'':5} 出 {result.block_out[name].text}")
    for a in result.asserts:
        req_lo = "-inf" if a.statement.lower is None else a.statement.lower
        req_hi = "+inf" if a.statement.upper is None else a.statement.upper
        observed = a.observed.text if a.observed is not None else "(不可达)"
        extra = "（不可达位置，空真）" if a.vacuous else ""
        print(
            f"  assert {a.statement.target} in [{req_lo}, {req_hi}] "
            f"观测={observed} -> {a.verdict.upper()}{extra}"
        )
    for a in getattr(result, "diff_asserts", []):
        rv = "0" if a.statement.right is None else a.statement.right
        bound = "(不可达)" if a.observed_bound is None else f"{a.observed_bound}"
        extra = "（不可达位置，空真）" if a.vacuous else ""
        print(
            f"  assert {a.statement.left} - {rv} <= {a.statement.const} "
            f"最紧上界={bound} -> {a.verdict.upper()}{extra}"
        )


def main() -> None:
    print("=== 1) 有界循环（正常结果：断言可证 + 收窄改善）===")
    cfg = bounded_loop(4)
    result = analyze(cfg)
    print_result("i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5", result)
    before = result.post_widening_in["exit"].text
    after = result.block_in["exit"].text
    print(f"收窄改善：exit 入不变量 {before}  ->  {after}")
    report = check_local_soundness(result)
    print(f"独立符号包含性检查器复核：{'通过（局部健全）' if report.ok else report.violations}")

    print()
    print("=== 2) 独立具体执行器对照（有界程序覆盖性）===")
    concrete = run_bounded(cfg, [{"i": 0}])
    lo = concrete.var_min["body"]["i"]
    hi = concrete.var_max["body"]["i"]
    abstract_body = result.block_in["body"].get("i")
    covered = abstract_body.contains_int(lo) and abstract_body.contains_int(hi)
    print(f"具体枚举 body 块 i 的 min/max = {lo}/{hi}，截断={concrete.truncated}；"
          f"被抽象区间 {abstract_body.text} 覆盖：{covered}")
    print(f"具体断言违反数：{len(concrete.assert_violations)}")

    print()
    print("=== 3) 无界增长循环（无法证明 -> unknown，不判错误）===")
    unb = analyze(unbounded_loop())
    print_result("i=0; while(i>=0){assert i<=5; i++}", unb)
    verdict = unb.asserts[0].verdict
    print(f"结论：{verdict}（区间分析只能给出 {unb.asserts[0].observed.text}，"
          f"不满足子集包含，按契约输出 unknown）")
    print(f"独立检查器复核：{'通过' if check_local_soundness(unb).ok else '失败'}")

    print()
    print("=== 4) 差分约束 x-y<=c：赋值/分支合流/循环入口与区间交换信息 ===")
    dm = analyze(diff_merge())
    print_result("x=0; if(j>=0){y=0}else{y=1}; assert x-y<=0", dm)
    print("合流点 DBM（入状态）：", dm.diff_state_at("m").text())
    print(f"独立检查器复核：{'通过' if check_local_soundness(dm).ok else '失败'}")

    dl = analyze(diff_loop())
    print()
    print_result("x=0;y=1; while(x<=4){assert y-x<=1; assert x-y<=-1; x++;y++}", dl)
    head_diff = dl.diff_state_at("head")
    print("循环头 DBM 中跨变量界：",
          f"y-x<={head_diff.bound_of('y', 'x')}；",
          f"x-y<={head_diff.bound_of('x', 'y')}")
    print("（区间视图只能给出 x:[0,5], y:[1,6]，无法表达上述差值不变量）")
    concrete2 = run_bounded(diff_loop(), [{"x": 0, "y": 1}])
    print(f"独立具体执行器：截断={concrete2.truncated}，"
          f"差分断言违反数={len(concrete2.diff_violations)}，"
          f"区间断言违反数={len(concrete2.assert_violations)}")
    print(f"独立检查器复核：{'通过' if check_local_soundness(dl).ok else '失败'}")

    print()
    print("=== 5) 显式迭代预算内未收敛 -> 差分断言 unknown（不冒充证明）===")
    fb = analyze(diff_loop(), loop_budget=1)
    print(f"关系域收敛标记：{fb.relational_converged}（预算 {fb.relational_budget} 轮）")
    for a in fb.diff_asserts:
        print(f"  assert {a.statement.left}-{a.statement.right}<= {a.statement.const}"
              f" -> {a.verdict.upper()}（已退回纯区间结果）")
    print("区间结论仍有效：exit 处 x =", fb.block_in["exit"].get("x").text)
    print(f"独立检查器复核：{'通过' if check_local_soundness(fb).ok else '失败'}")

    print()
    print("=== 6) 实际触发的拒绝边界（非法输入必须报错且可定位）===")
    try:
        # bool 是 int 的子类，但契约明确拒绝 bool 充当整数常量
        CFG(
            variables=("i",),
            blocks={
                "init": Block("init", (AssignConst("i", True),), ("init",)),
            },
            entry="init",
        )
    except IntervalAIError as exc:
        print(f"捕获 {type(exc).__name__}: {exc}")
        print("（非法输入被拒绝，未产生任何半成品对象）")

    try:
        # 差分约束限定至多 4 个变量：5 个变量 + AssumeDiff 必须被拒绝
        CFG(
            variables=tuple("abcde"),
            blocks={"b": Block("b", (AssumeDiff("a", "b", 0),), ())},
            entry="b",
        )
    except IntervalAIError as exc:
        print(f"捕获 {type(exc).__name__}: {exc}")


if __name__ == "__main__":
    main()
