"""固定输入演示：整数循环的区间抽象解释（含 x-y<=c 差分约束关系域）。

运行：``python demo.py``（Python 3.14，仅标准库；无网络、无 sleep、无预录结果）。

演示内容：
1. 有界循环：每块入/出不变量、断言 proved、收窄改善（[n+1,+inf) -> [n+1,n+1]）；
2. 无界增长循环：同一点位断言只能给出 unknown（不是错误）；
3. 独立符号包含性检查器复核结果；
4. 独立具体执行器对有界程序做覆盖性对照；
5. 真实触发的拒绝边界：bool 常量被 ValidationError 拒绝（可定位错误）；
6. 差分约束（关系域）：y=x 后在守卫 x<=0 真支上推出区间单独得不到的 y<=0；
   传递差界、分支合流取弱界、关系循环不变量 y-x==2，以及无法证明给 unknown。
"""

from __future__ import annotations

from interval_ai import (
    AssertDiff,
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignCopy,
    AssumeDiff,
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


def diff_copy_guard() -> CFG:
    # y = x; if (x <= 0) { assert y-x<=0; assert y<=0; assert y-x<=1(过宽) }
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


def diff_loop() -> CFG:
    # x=0; y=2; while(x<=3){ assert y-x==2; x++; y++ }; assert x==4,y==6
    return CFG(
        variables=("x", "y"),
        blocks={
            "init": Block(
                "init", (AssignConst("x", 0), AssignConst("y", 2)), ("head",)
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


def print_diff_asserts(result) -> None:
    for a in result.diff_asserts:
        bound = "推不出" if a.observed_bound is None else f"{a.observed_bound}"
        extra = "（不可达位置，空真）" if a.vacuous else ""
        print(
            f"  assert {a.statement.a}-{a.statement.b}<={a.statement.const} "
            f"最紧上界={bound} -> {a.verdict.upper()}{extra}"
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
    print_diff_asserts(result)


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
    print("=== 4) 实际触发的拒绝边界（非法输入必须报错且可定位）===")
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

    print()
    print("=== 5) 差分约束：y=x 后守卫 x<=0 真支推出 y<=0（区间单独得不到）===")
    dres = analyze(diff_copy_guard())
    print_result("y=x; if(x<=0){assert y-x<=0; assert y<=0; assert y-x<=1}", dres)
    ty = dres.block_in["t"].get("y")
    fy = dres.block_in["f"].get("y")
    print(f"真支 t 的 y 区间 = {ty.text}（由 y==x 与 x<=0 经差界闭包推出）；"
          f"假支 f 的 y 区间 = {fy.text}")
    print(f"独立积检查器复核：{'通过（局部健全）' if check_local_soundness(dres).ok else '失败'}")

    print()
    print("=== 6) 关系循环不变量 y-x==2（赋值/合流/循环入口全程交换信息）===")
    dl = analyze(diff_loop())
    print_result("x=0;y=2; while(x<=3){assert y-x==2; x++;y++}; assert x==4,y==6", dl)
    print(f"循环头差界 y-x<= {dl.diff_at('head').bound('y','x')}；"
          f"上升 {dl.relation_rounds} 轮，收窄 {dl.narrowing_rounds} 轮，"
          f"未截断={not dl.relation_truncated}")
    dconcrete = run_bounded(diff_loop(), [{"x": 0, "y": 2}])
    pairs = sorted({(s["x"], s["y"]) for s in dconcrete.in_stores["body"]})
    offsets = {y - x for x, y in pairs}
    print(f"独立具体枚举 body 的 (x,y) 差值集合 = {sorted(offsets)}，"
          f"截断={dconcrete.truncated}，违反数={len(dconcrete.assert_violations)}")
    print(f"独立积检查器复核：{'通过' if check_local_soundness(dl).ok else '失败'}")

    print()
    print("=== 7) 差分约束无法证明（边界：最紧界不满足要求 -> unknown）===")
    weak = CFG(
        variables=("x", "y"),
        blocks={"b": Block(
            "b", (AssumeDiff("x", "y", 2), AssertDiff("x", "y", 1)), ()
        )},
        entry="b",
    )
    wres = analyze(weak)
    print_result("assume x-y<=2; assert x-y<=1", wres)
    print("结论：只能推出 x-y<=2，推不出 <=1，按契约输出 UNKNOWN（不判错误）")

    print()
    print("=== 8) 关系迭代预算耗尽（边界：未收敛 -> unknown，不冒充证明）===")
    full = analyze(diff_loop())
    cut = analyze(diff_loop(), relation_budget=1)
    print(f"预算充足：截断标记={full.relation_truncated}，"
          f"差分断言结论={[a.verdict for a in full.diff_asserts]}")
    print(f"预算=1 轮：截断标记={cut.relation_truncated}，关系不变量已放弃，"
          f"差分断言结论={[a.verdict for a in cut.diff_asserts]}")
    print(f"区间结论仍独立给出（x==4）："
          f"{[a.verdict for a in cut.asserts if a.block == 'exit']}；"
          f"独立检查器复核：{'通过' if check_local_soundness(cut).ok else '失败'}")

    print()
    print("=== 9) 差分语句非法输入（实际错误：同变量操作数被拒绝）===")
    try:
        CFG(
            variables=("x", "y"),
            blocks={"b": Block("b", (AssumeDiff("x", "x", 0),), ())},
            entry="b",
        )
    except IntervalAIError as exc:
        print(f"捕获 {type(exc).__name__}: {exc}")
        print("（构造期完整校验失败，不返回任何半成品 CFG 对象）")


if __name__ == "__main__":
    main()
