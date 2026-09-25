"""固定输入演示：整数循环的区间抽象解释 + 可选有限路径分区。

运行：``python demo.py``（Python 3.14，仅标准库；无网络、无 sleep、无预录结果）。

演示内容：
1. 有界循环：每块入/出不变量、断言 proved、收窄改善（[n+1,+inf) -> [n+1,n+1]）；
2. 无界增长循环：同一点位断言只能给出 unknown（不是错误）；
3. 独立符号包含性检查器复核结果；
4. 独立具体执行器对有界程序做覆盖性对照；
5. 真实触发的拒绝边界：bool 常量被 ValidationError 拒绝（可定位错误）；
6. 有限路径分区（新能力）：两分支分别设置不同区间后再判断，普通凸包
   unknown、分区 proved（关联信息被保留）；
7. 循环内条件翻转：标签只记"最近一次"真假，退出分区得到最后一次结果；
8. 强制合并：分区数超显式上限时按标签顺序合并、凸包守恒、报告发生位置。
"""

from __future__ import annotations

from interval_ai import (
    AssertRange,
    AssignAdd,
    AssignConst,
    Block,
    CFG,
    Guard,
    Interval,
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


def branch_correlation_program() -> CFG:
    # x in [0,10]
    # if (x <= 3) { y = 0 } else { y = 10 }
    # if (y >= 5) { assert x >= 4 }   <- 能进这里的必来自第一条件假支
    return CFG(
        variables=("x", "y"),
        blocks={
            "fork1": Block("fork1", (), ("then1", "else1"), Guard("x", "<=", 3)),
            "then1": Block("then1", (AssignConst("y", 0),), ("fork2",)),
            "else1": Block("else1", (AssignConst("y", 10),), ("fork2",)),
            "fork2": Block("fork2", (), ("hot", "skip"), Guard("y", ">=", 5)),
            "hot": Block("hot", (AssertRange("x", 4, None),), ()),
            "skip": Block("skip", (), ()),
        },
        entry="fork1",
        entry_bounds={"x": Interval(0, 10)},
    )


def loop_flip_program() -> CFG:
    # x=0; while (x<=4) { if (x>=3) flag=100 else flag=0; x++ }; assert flag==100
    return CFG(
        variables=("x", "flag"),
        blocks={
            "init": Block(
                "init", (AssignConst("x", 0), AssignConst("flag", 0)), ("head",)
            ),
            "head": Block("head", (), ("inner", "exit"), Guard("x", "<=", 4)),
            "inner": Block("inner", (), ("hi", "lo"), Guard("x", ">=", 3)),
            "hi": Block("hi", (AssignConst("flag", 100),), ("step",)),
            "lo": Block("lo", (AssignConst("flag", 0),), ("step",)),
            "step": Block("step", (AssignAdd("x", "x", 1),), ("head",)),
            "exit": Block("exit", (AssertRange("flag", 100, 100),), ()),
        },
        entry="init",
    )


def three_guard_tree() -> CFG:
    # 三个串行独立守卫，全开区间入口，汇合后实际有 4 个可达细标签
    return CFG(
        variables=("x",),
        blocks={
            "g1": Block("g1", (), ("a1", "b1"), Guard("x", "<=", 1)),
            "a1": Block("a1", (), ("g2",)),
            "b1": Block("b1", (), ("g2",)),
            "g2": Block("g2", (), ("a2", "b2"), Guard("x", "<=", 2)),
            "a2": Block("a2", (), ("g3",)),
            "b2": Block("b2", (), ("g3",)),
            "g3": Block("g3", (), ("a3", "b3"), Guard("x", "<=", 3)),
            "a3": Block("a3", (), ("join",)),
            "b3": Block("b3", (), ("join",)),
            "join": Block("join", (), ()),
        },
        entry="g1",
        entry_bounds={"x": Interval(0, 10)},
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

    print()
    print("=== 5) 有限路径分区：两支设不同区间后再判断（unknown -> PROVED）===")
    bcfg = branch_correlation_program()
    plain = analyze(bcfg)
    print("程序: x∈[0,10]; if(x<=3){y=0}else{y=10}; if(y>=5){assert x>=4}")
    print(f"普通凸包: hot 块 x = {plain.block_in['hot'].get('x').text} "
          f"-> {plain.asserts[0].verdict.upper()}（两支 y 关联在 join 处丢失）")
    part = analyze(bcfg, track_guards=("fork1",))
    for label, state in part.reachable_partitions("fork2"):
        print(f"  分区 {label.text}: x = {state.get('x').text}, y = {state.get('y').text}")
    label, hot_state = part.reachable_partitions("hot")[0]
    print(f"分区后 hot 仅来自标签 {label.text}（第一条件为假）: x = {hot_state.get('x').text}")
    print(f"逐分区断言 -> {part.asserts[0].verdict.upper()}；"
          f"独立检查器复核：{'通过' if check_local_soundness(part).ok else '失败'}")
    concrete = run_bounded(bcfg, [{"x": x, "y": 0} for x in range(11)])
    print(f"具体枚举对照：hot 块 x min/max = {concrete.interval_observed('hot', 'x')}"
          f"（仅覆盖性对照，证明来自符号包含）")

    print()
    print("=== 6) 循环内条件翻转：标签只记最近一次真假 ===")
    lcfg = loop_flip_program()
    lplain = analyze(lcfg)
    lpart = analyze(lcfg, track_guards=("inner",))
    print("程序: x=0; while(x<=4){ if(x>=3) flag=100 else flag=0; x++ }; assert flag==100")
    print(f"普通凸包: exit flag = {lplain.block_in['exit'].get('flag').text} "
          f"-> {lplain.asserts[0].verdict.upper()}")
    for text in ("?", "F", "T"):
        hit = [(l, s) for l, s in lpart.reachable_partitions("inner") if l.text == text]
        if hit:
            print(f"  inner 分区 {text}: x = {hit[0][1].get('x').text}（标签随迭代覆写）")
    elabel, estate = lpart.reachable_partitions("exit")[0]
    print(f"退出分区标签 = {elabel.text}（最后一次 x=4 为真，未被首次的假固定）"
          f": flag = {estate.get('flag').text}")
    print(f"逐分区断言 -> {lpart.asserts[0].verdict.upper()}；"
          f"独立检查器复核：{'通过' if check_local_soundness(lpart).ok else '失败'}")

    print()
    print("=== 7) 强制合并：超显式上限按标签顺序合并（凸包守恒、给出位置）===")
    tcfg = three_guard_tree()
    full = analyze(tcfg, track_guards=("g1", "g2", "g3"), max_partitions=8)
    capped = analyze(tcfg, track_guards=("g1", "g2", "g3"), max_partitions=3)
    print("程序: 三个串行守卫 x<=1 / x<=2 / x<=3；x∈[0,10]，汇合块 4 个可达细标签")
    print(f"上限 8：join 分区 = {sorted(l.text for l, _ in full.reachable_partitions('join'))}，"
          f"总凸包 x = {full.block_in['join'].get('x').text}")
    print(f"上限 3：join 分区 = {sorted(l.text for l, _ in capped.reachable_partitions('join'))}")
    for ev in capped.merges:
        print(f"  合并发生处 -> {ev.location}")
    print(f"合并后总凸包 x = {capped.block_in['join'].get('x').text}"
          f"（与上限 8 完全相等：只丢标签、不删状态）")
    print(f"独立检查器复核（含合并事件结构）："
          f"{'通过' if check_local_soundness(capped).ok else '失败'}")


if __name__ == "__main__":
    main()
