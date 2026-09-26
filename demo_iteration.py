"""区间 + 同余不变量演示（Python 3.14，仅标准库）。"""

from __future__ import annotations

from interval_ai import (
    AssertRange,
    AssignAdd,
    AssignConst,
    AssignMul,
    Block,
    CFG,
    Congruence,
    Guard,
    analyze,
    check_local_soundness,
    run_bounded,
)


def even_counter_cfg(start: int) -> CFG:
    parity = Congruence(2, start % 2)
    body_lower = start if start <= 9 else None
    return CFG(
        variables=("i",),
        blocks={
            "init": Block("init", (AssignConst("i", start),), ("head",)),
            "head": Block(
                "head",
                (AssertRange("i", None, None, parity),),
                ("body", "exit"),
                Guard("i", "<=", 9),
            ),
            "body": Block(
                "body",
                (AssertRange("i", body_lower, 9, parity), AssignAdd("i", "i", 2)),
                ("head",),
            ),
            "exit": Block(
                "exit",
                (AssertRange("i", None, None, parity),),
                (),
            ),
        },
        entry="init",
    )


def different_steps_cfg(steps: tuple[int, int]) -> CFG:
    return CFG(
        variables=("i", "p"),
        blocks={
            "init": Block("init", (AssignConst("i", 0),), ("head",)),
            "head": Block(
                "head",
                (),
                ("fork", "exit"),
                Guard("i", "<=", 9),
            ),
            "fork": Block("fork", (), ("a", "b"), Guard("p", ">=", 0)),
            "a": Block("a", (AssignAdd("i", "i", steps[0]),), ("head",)),
            "b": Block("b", (AssignAdd("i", "i", steps[1]),), ("head",)),
            "exit": Block("exit", (), ()),
        },
        entry="init",
    )


def negative_multiplication_cfg() -> CFG:
    return CFG(
        variables=("x", "y"),
        blocks={
            "start": Block(
                "start",
                (
                    AssignConst("y", 2),
                    AssignMul("x", "y", -3),
                    AssertRange("x", -6, -6, Congruence.exact(-6)),
                ),
                (),
            )
        },
        entry="start",
    )


def print_points(title: str, result) -> None:
    print(f"--- {title}")
    for name in result.cfg.blocks:
        print(f"  {name:5} in : {result.block_in[name].text}")
        print(f"  {'':5} out: {result.block_out[name].text}")
    for status in result.asserts:
        congruence = status.observed_congruence.text if status.observed_congruence else "bottom"
        print(f"  assert@{status.block}: {congruence} -> {status.verdict.upper()}")
    report = check_local_soundness(result)
    print(f"  独立局部转移/边包含检查: {'PASS' if report.ok else report.violations}")


def main() -> None:
    print("=== 1) 步长 2：偶数计数，区间外壳内的奇数不进入结果 ===")
    even = analyze(even_counter_cfg(0))
    print_points("i=0; while(i<=9) i+=2", even)
    concrete = run_bounded(even.cfg, [{"i": 0}], max_visited_states=100)
    print(
        "  小范围具体执行补充：body 取值 "
        + str(sorted({store['i'] for store in concrete.in_stores['body']}))
        + f"，truncated={concrete.truncated}"
    )

    print()
    print("=== 2) 负起点：规范余数对负数一致，仍为奇同余类 ===")
    negative_start = analyze(even_counter_cfg(-3))
    print_points("i=-3; while(i<=9) i+=2", negative_start)

    print()
    print("=== 3) 两条回边步长不同：合流模数取 gcd，不保留单边模数 ===")
    compatible = analyze(different_steps_cfg((2, 4)))
    print_points("路径 i+=2 或 i+=4", compatible)
    incompatible = analyze(different_steps_cfg((2, 3)))
    print_points("路径 i+=2 或 i+=3", incompatible)
    print(
        "  head 同余：2/4 合流为 "
        + compatible.block_in["head"].get_congruence("i").text
        + "；2/3 合流为 "
        + incompatible.block_in["head"].get_congruence("i").text
    )

    print()
    print("=== 4) 永不进入的循环体与负常量乘法 ===")
    skipped = analyze(even_counter_cfg(10))
    print_points("i=10; while(i<=9) i+=2（body 不可达）", skipped)
    multiplication = analyze(negative_multiplication_cfg())
    print_points("y=2; x=-3*y", multiplication)


if __name__ == "__main__":
    main()
