"""区间 + 同余联合域的固定输入演示。

运行：``python demo_iteration.py``。所有结果现场计算，不 sleep、不读取预录答案。
"""

from __future__ import annotations

from interval_ai import (
    AssignAdd,
    AssignConst,
    AssignMul,
    Block,
    CFG,
    Congruence,
    Guard,
    Interval,
    IntervalAIError,
    analyze,
    check_edge_guard,
    check_local_soundness,
    run_bounded,
)


def step_two_cfg() -> CFG:
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block("head", (), ("body", "exit"), Guard("i", "<=", 4)),
            "body": Block("body", (AssignAdd("i", "i", 2),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def different_steps_cfg() -> CFG:
    return CFG(
        variables=("i", "j"),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block("head", (), ("fork", "exit"), Guard("i", "<=", 9)),
            "fork": Block("fork", (), ("step2", "step3"), Guard("j", ">=", 0)),
            "step2": Block("step2", (AssignAdd("i", "i", 2),), ("head",)),
            "step3": Block("step3", (AssignAdd("i", "i", 3),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def negative_cfg() -> CFG:
    return CFG(
        variables=("x", "y"),
        blocks={
            "init": Block(
                "init",
                (AssignConst("y", 0), AssignConst("x", -3), AssignMul("y", "x", -2)),
                ("head",),
            ),
            "head": Block("head", (), ("body", "dead"), Guard("x", ">=", -4)),
            "body": Block("body", (AssignAdd("x", "x", 2),), ("head",)),
            "dead": Block("dead", (), ()),
        },
        entry="init",
    )


def impossible_entry_cfg() -> CFG:
    return CFG(
        variables=("i",),
        blocks={"b": Block("b", (), ())},
        entry="b",
        entry_bounds={"i": Interval(0, 0)},
        entry_congruences={"i": Congruence(2, 1)},
    )


def print_invariants(title: str, result) -> None:
    print(f"--- {title}")
    for name in result.cfg.blocks:
        print(f"  {name:7} IN  {result.block_in[name].text}")
        print(f"  {'':7} OUT {result.block_out[name].text}")


def check_edges(result) -> None:
    for name, block in result.cfg.blocks.items():
        for edge_index, succ in enumerate(block.successors):
            if block.guard is None:
                continue
            report = check_edge_guard(
                block.guard,
                edge_index == 0,
                result.block_out[name],
                result.block_in[succ],
            )
            side = "true" if edge_index == 0 else "false"
            verdict = "ok" if report.ok else f"BAD {report.violations}"
            print(f"  edge {name} --{side}--> {succ}: {verdict}")


def main() -> None:
    print("=== 1) 步长 2：区间外包含奇数，但同余证书排除奇数 ===")
    result = analyze(step_two_cfg())
    print_invariants("i=0; while i<=4 { i += 2 }", result)
    check_edges(result)
    concrete = run_bounded(step_two_cfg(), [{"i": 0}])
    print(
        "小范围具体执行补充：body 可达 i = "
        + ", ".join(str(s["i"]) for s in concrete.in_stores["body"])
        + f"；truncated={concrete.truncated}"
    )
    print(f"整体局部转移包含检查：{'通过' if check_local_soundness(result).ok else '失败'}")

    print()
    print("=== 2) 两条路径步长不同：合流取 gcd(2,3)=1，不能硬留 2 的模数 ===")
    result2 = analyze(different_steps_cfg())
    print_invariants("路径 A: i+=2；路径 B: i+=3", result2)
    check_edges(result2)
    print(f"整体局部转移包含检查：{'通过' if check_local_soundness(result2).ok else '失败'}")

    print()
    print("=== 3) 负起点、负系数和永不进入的分支 ===")
    result3 = analyze(negative_cfg())
    print_invariants("x=-3; y=-2*x; while x>=-4 { x += 2 }", result3)
    check_edges(result3)
    print(
        f"永不进入分支 dead.bottom={result3.block_in['dead'].bottom}；"
        f"整体检查：{'通过' if check_local_soundness(result3).ok else '失败'}"
    )

    print()
    print("=== 4) 归约后区间内无合法同余点：入口直接判空 ===")
    result4 = analyze(impossible_entry_cfg())
    print(f"  b IN {result4.block_in['b'].text}")
    print(f"整体检查：{'通过' if check_local_soundness(result4).ok else '失败'}")

    print()
    print("=== 5) 异常路径：负模数被拒绝 ===")
    try:
        Congruence(-2, 0)
    except IntervalAIError as exc:
        print(f"捕获 {type(exc).__name__}: {exc}")


if __name__ == "__main__":
    main()
