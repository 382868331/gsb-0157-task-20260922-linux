"""固定输入演示：整数循环的区间抽象解释。

运行：``python demo.py``（Python 3.14，仅标准库；无网络、无 sleep、无预录结果）。

演示内容：
1. 有界循环：每块入/出不变量、断言 proved、收窄改善（[n+1,+inf) -> [n+1,n+1]）；
2. 无界增长循环：同一点位断言只能给出 unknown（不是错误）；
3. 独立符号包含性检查器复核结果；
4. 独立具体执行器对有界程序做覆盖性对照；
5. 真实触发的拒绝边界：bool 常量被 ValidationError 拒绝（可定位错误）。
"""

from __future__ import annotations

from interval_ai import (
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


if __name__ == "__main__":
    main()
