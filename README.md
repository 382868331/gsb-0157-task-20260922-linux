# 整数循环的区间抽象解释（interval_ai）

一个从零实现、仅依赖标准库的**区间 + 同余积域抽象解释**可复用题库：输入小型
控制流图（CFG，变量为数学整数），输出每个基本块的入/出两部分不变量：闭整数
区间与 `x ≡ r (mod m)` 同余信息，并保留循环加宽/收窄迭代过程。断言可同时检查
范围和同余，结论为 `proved` / `unknown`。另含一个**独立**的局部转移包含性检查器
（符号端点与同余证明，不做有限采样）和一个**独立**的确定性具体执行器
（仅用于有界程序的覆盖性对照）。

## 运行环境

- Python **3.14.7**（不使用 3.14 之外的新语法外特性；3.10+ 的 `X | Y` 注解可用）。
- **无第三方依赖**，安装 Python 后直接运行；核心、测试、demo 全部离线，
  不访问网络、不需要账号/密钥/数据库/中间件/Docker。
- Linux 原生运行验证。

```bash
# 可选：创建并启用标准库 venv（也可直接使用已安装的 Python 3.14.7）
python3.14 -m venv .venv
source .venv/bin/activate

# 必要测试
python -m unittest discover -s tests -v

# 基线区间演示
python demo.py

# 同余迭代演示（约 0.05 秒，远小于 90 秒预算；真实计算，无 sleep、无预录结果）
python demo_iteration.py
```

## 语言子集与输入上限

| 项目 | 契约 |
|---|---|
| 变量数 | 1 ≤ 变量 ≤ **20** |
| 基本块数 | 1 ≤ 块 ≤ **40** |
| 语句 | `x = c`、`x = y`、`x = y + c`、`x = c*y`（c 为任意整数，可负/可为 0）、`assert lo <= x <= hi` 且可选同余 |
| 块尾条件 | `x <= c`、`x >= c`；真支走第 0 个后继，假支（整数补集）走第 1 个后继 |
| 后继数 | 0（终止块）、1（无条件）、2（必须带守卫） |
| 数值域 | 数学整数（Python 任意精度 `int`），无溢出、无除法/函数调用 |

守卫的整数补集：`x <= c` 为假 ⇔ `x >= c+1`；`x >= c` 为假 ⇔ `x <= c-1`。

## 公开接口与数据结构

```python
from interval_ai import (
    # CFG
    CFG, Block, Guard,
    AssignConst, AssignCopy, AssignAdd, AssignMul, AssertRange,
    # 域
    Interval, Congruence, AbstractState,
    # 分析
    analyze, AnalysisResult, AssertStatus, MAX_NARROWING_ROUNDS,
    # 局部转移（也可单独复用）
    transfer_statement, transfer_block, edge_state, guard_interval,
    # 独立检查器
    check_local_soundness, check_transfer_step, check_edge_guard,
    ContainmentViolation,
    # 独立具体执行参考
    run_bounded,
    # 错误
    IntervalAIError, ValidationError, BudgetExhaustedError,
)
```

- `Interval(lower, upper)`：闭整数区间；`None` 表示无穷端点
  （`Interval(0, None)` = [0,+∞)）。提供 `join`（凸包）、`intersect`、
  `subseteq`、`add`、`widen`、`narrow`。
- `Congruence(modulus, residue)`：规范同余类；`m=0` 为精确常量 `{r}`，
  `m=1` 为任意整数。构造时把余数规范到 `0 <= r < m`，负数使用 Python 数学余数；
  提供 `join`（gcd 合流）、`shift`、`scale`、`has_point_within`。
- `CFG(variables, blocks, entry, entry_bounds=None, entry_congruences=None)`：构造时一次性校验，
  非法输入抛 `ValidationError`（异常 `location` 可定位到块/语句/参数）。
- `result = analyze(cfg)`：
  - `result.block_in[name]` / `result.block_out[name]`：`AbstractState`
    （每个变量含区间与同余，`bottom=True` 表示不可达）；
  - `result.asserts`：每个 `AssertRange` 一条 `AssertStatus`，
    `verdict ∈ {"proved","unknown"}`；不可达位置的断言为空真 `proved`
    且 `vacuous=True`；
  - `result.widen_points`、`ascending_rounds`、`narrowing_rounds`：
    加宽点与实际迭代轮数；
  - `result.post_widening_in/out` 与 `result.narrowing_refined`：
    收窄前快照与"收窄是否确实改善"。
- `check_local_soundness(result) -> CheckReport`：独立符号检查
  入口包含、块转移精确性、每条守卫边包含、每个 `proved` 断言的包含；
  失败可 `report.raise_if_bad()`。
- `run_bounded(cfg, initial_stores)`：独立具体语义枚举，
  仅对有界程序完备，状态超预算时 `truncated=True`（明确标记、不冒充证明）。

`AssertRange(target, lo, hi, Congruence(2, 0))` 表示目标还必须是偶数；第四个参数缺省为
`Congruence(1, 0)`。完整机读结果可用 `result.to_dict()`，其中同时包含 `bounds` 与
`congruences`。

## 同余积域语义

- 赋值常量得到 `m=0` 精确同余；复制同时复制两个分量；`y+c` 平移区间和余数；
  `c*y` 按 `m' = gcd(c,m)`、`r' = c*r mod m'` 更新（精确输入在乘后仍精确）。
- 合流不保留某一边的模数：`r_a (mod m_a)` 与 `r_b (mod m_b)` 的最强公共限制为
  `r_a (mod gcd(m_a,m_b,r_a-r_b))`。例如步长 2/4 保留偶数，步长 2/3 退化为任意整数。
- 守卫仍先切区间；归约时检查该区间内是否存在满足同余的整数点。单元素区间会归约为
  `m=0`，无合法同余点则状态为 `bottom`。
- 循环扩大时同余只在有限除数链上合流，天然终止；区间仍按原延迟加宽策略保证包含全部
  可达状态，随后最多 8 轮有限收窄。
- 断言同时要求区间内所有满足观测同余的点均落入要求范围与同余类；具体执行器也会检查
  断言同余，但它只作为小范围补充。

## 分析算法（设计取舍）

1. **控制流**：DFS 三色法识别回边，回边目标为加宽点；枚举顺序为入口可达
   部分的逆后序（RPO，插入顺序打破并列），结果确定。
2. **上升迭代（延迟加宽）**：每个加宽点的**前两次扩张取凸包 join**，
   **第三次扩张起使用标准区间 widening**——某端点一旦被新迭代值突破就
   推到相应无穷。加宽是**逐变量选择性**的：只加宽该回边自然循环内被
   赋值修改的变量；循环内不改、只从外层流入的变量（典型如嵌套循环里
   外层计数器）取精确凸包，避免被无谓推到无穷且收窄无法恢复。非加宽点
   直接做方程右端的凸包。上升到后置不动点（一整轮无变化）为止。
3. **收窄迭代**：上升稳定后做**至多 8 轮**混沌收窄
   （`MAX_NARROWING_ROUNDS = 8`），只允许把无穷端点替换为新方程值的
   有限端点（标准 narrowing，保证不放宽已证结论），提前稳定则提前停。
4. **断言判定**：在断言所在语句位置检查区间分量和同余分量是否均符号包含于
   要求；包含为 `proved`，否则为 `unknown`（无法证明不是错误，不抛异常、
   不输出 violation）。
5. **独立性**：检查器（`checker.py`）与具体执行器（`concrete.py`）均不
   import 被测核心（`transfer`/`engine`），端点算术与守卫补集各自重新
   实现；测试用 AST 扫描强制该约束。期望值来自手算或独立具体语义，
   不用被测核心算期望值；往返一致仅作补充。
6. **预算与无解分离**：区间 widening 保证上升链有限，数学上必然终止；
   `ascending_budget`（默认 10000）只是防御性安全阀，耗尽抛
   `BudgetExhaustedError`（携带 `partial`，但明确不是已验证不动点），
   与 `unknown`（正常数据结论）严格区分。
7. **失败原子性**：CFG 为冻结结构且构造期完整校验，校验失败不返回对象；
   分析过程不修改 CFG，预算异常后 CFG 仍与调用前完全一致
   （有测试保证），无未说明的部分变更。

## 数值与误差口径

- 全部计算使用 Python **任意精度整数**，不存在浮点结果，因此**无舍入误差、
  无容差**；端点比较是精确整数/符号比较，不用宽容差掩盖边界错误。
- 输入侧显式拒绝：`NaN`、`±Infinity`、非整数浮点、以及用 `bool`
  冒充整数（`True`/`False` 虽是 `int` 子类，按契约一律拒绝）。
- 本库只实现本题规定的有限数学子集（无除法、无数组/堆、无过程调用、
  无整数溢出模型），**不宣称兼容任何行业标准分析框架**。

## demo 会真实展示什么

`python demo.py` 固定构造两个程序并真实求解：

1. 有界循环 `i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5`：
   每块入/出不变量、两条断言 **PROVED**，以及收窄改善
   `exit: [5,+inf) → [5,5]`；独立检查器复核通过；独立具体执行器枚举
   body 块具体值域 [0,4] 并确认被抽象区间覆盖。
2. 无界增长循环 `i=0; while(i>=0){assert i<=5; i++}`：循环头
   `[0,+inf)`、退出支不可达（bottom），断言输出 **UNKNOWN**（非错误）。
3. 真实触发一个拒绝边界：`AssignConst("i", True)` 抛带定位的
   `ValidationError`。

`python demo_iteration.py` 固定构造同余积域程序并真实求解，展示步长 2、负起点、
两条路径步长 2/4 与 2/3、永不进入的循环体以及负常量乘法；每个程序点同时打印
区间与同余，独立检查器逐条复核块转移和边包含。

## 已知限制

- 非关系型积域仍无法推导一般变量间关系；复制只能传递同一份单变量区间和同余，
  更复杂的关系命题存在固有精度损失，部分真命题只能得到 `unknown`。
- 区间合流仍取凸包：`x=0` 与 `x=10` 合并为 `[0,10]`，同余可排除其中部分点，
  但不表示析取集合或完整枚举路径。
- 仅支持五种语句与两种守卫；入口不可达块（从 entry 不可达）保持 bottom，
  不参与分析。
- 具体执行器仅适合有界小程序对照；对无界循环会在状态预算处截断并显式
  标记 `truncated=True`，无界情形的健全性由符号检查器承担。
- 加宽阈值（前两次 join）与收窄上限（8 轮）按题面固定，未做阈值自适应。

## 目录

```
interval_ai/
  congruence.py 同余域（规范余数/gcd 合流/平移与常量乘法）
  errors.py    错误类型与整数参数校验（NaN/Infinity/bool 拒绝）
  intervals.py 区间与逐变量抽象状态（join/widen/narrow/包含）
  cfg.py       CFG/Block/Guard/语句 数据结构与构造期校验
  transfer.py  局部抽象转移（语句、守卫边过滤）
  engine.py    RPO 不动点引擎：延迟加宽 + 至多 8 轮收窄
  checker.py   独立符号包含性检查器（不采样、不依赖核心）
  concrete.py  独立确定性具体执行器（有界程序对照）
tests/         unittest 用例（积域/引擎/检查器/错误语义/具体覆盖）
demo.py        固定输入演示
demo_iteration.py 同余迭代固定输入演示
```
