# 整数循环的区间抽象解释（interval_ai）

一个从零实现、仅依赖标准库的**区间域抽象解释**可复用题库：输入小型控制流图
（CFG，变量为数学整数），输出每个基本块的入/出区间不变量、循环加宽/收窄
迭代过程，并对范围断言给出 `proved` / `unknown` 结论。另含一个**独立**的
局部转移包含性检查器（符号端点证明，不做有限采样）和一个**独立**的确定性
具体执行器（仅用于有界程序的覆盖性对照/找反例）。

可选的**有限路径分区模式**：调用方指定至多 3 个条件位置，状态按这些位置
最近一次真/假结果分组（未经过标 `?`），缓解 `if` 合流时凸包丢失分支信息
的问题；分区数有显式上限，超出按标签序合并（丢失标签取凸包，不删状态）。

## 运行环境

- Python **3.14.7**（不使用 3.14 之外的新语法外特性；3.10+ 的 `X | Y` 注解可用）。
- **无第三方依赖**，安装 Python 后直接运行；核心、测试、demo 全部离线，
  不访问网络、不需要账号/密钥/数据库/中间件/Docker。
- Linux 原生运行验证。

```bash
# 必要测试
python -m unittest discover -s tests -v

# 固定输入演示（约 0.05 秒，远小于 8 秒预算；真实计算，无 sleep、无预录结果）
python demo.py
```

## 语言子集与输入上限

| 项目 | 契约 |
|---|---|
| 变量数 | 1 ≤ 变量 ≤ **20** |
| 基本块数 | 1 ≤ 块 ≤ **40** |
| 语句 | `x = c`、`x = y`、`x = y + c`（c 为任意整数，可负）、`assert lo <= x <= hi`（端点可无穷） |
| 块尾条件 | `x <= c`、`x >= c`；真支走第 0 个后继，假支（整数补集）走第 1 个后继 |
| 后继数 | 0（终止块）、1（无条件）、2（必须带守卫） |
| 数值域 | 数学整数（Python 任意精度 `int`），无溢出、无除法/乘法/函数调用 |
| 分区位置 | 可选，0–**3** 个带守卫的块（`partition_points`） |
| 分区数上限 | 每块 ≤ `max_partitions`（默认 8），超限按标签序合并 |

守卫的整数补集：`x <= c` 为假 ⇔ `x >= c+1`；`x >= c` 为假 ⇔ `x <= c-1`。

## 公开接口与数据结构

```python
from interval_ai import (
    # CFG
    CFG, Block, Guard,
    AssignConst, AssignCopy, AssignAdd, AssertRange,
    # 域
    Interval, AbstractState,
    # 分析
    analyze, AnalysisResult, AssertStatus, MAX_NARROWING_ROUNDS,
    # 有限路径分区
    Partition, MergeEvent, MAX_PARTITION_POINTS, DEFAULT_MAX_PARTITIONS,
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
- `CFG(variables, blocks, entry, entry_bounds=None)`：构造时一次性校验，
  非法输入抛 `ValidationError`（异常 `location` 可定位到块/语句/参数）。
- `result = analyze(cfg)`：
  - `result.block_in[name]` / `result.block_out[name]`：`AbstractState`
    （`bottom=True` 表示不可达）；
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

完整机读结果可用 `result.to_dict()`。

## 可选：有限路径分区模式

```python
result = analyze(cfg, partition_points=("sw1",), max_partitions=4)
```

- `partition_points`：至多 **3** 个（`MAX_PARTITION_POINTS`）带守卫的块名；
  缺省为空，即旧行为（合并一律取凸包），结果与未分区完全一致。
- **标签**：长度 = 分区位置数的元组，逐位为 `"T"`（最近一次经过该位置
  为真）、`"F"`（为假）、`"?"`（尚未经过，unknown）。标签沿边**重写**：
  循环再次经过指定条件时用新结果覆盖旧值，旧真/假不会被永久固定成
  路径事实。
- **数值域不变**：每个分区仍是原来的逐变量区间状态，不引入关系域；
  每个 `(块, 标签)` 独立做延迟加宽（前两次凸包、第三次起 widening）
  与至多 8 轮收窄。
- `max_partitions`：每个块允许的最大分区数（显式上限，默认
  `DEFAULT_MAX_PARTITIONS = 8`）。超限时**按标签序合并**：保留最小的
  `max_partitions - 1` 个具体标签，其余并入一个丢失标签的 merged
  分区（区间凸包），**不删除任何状态**；被合并的标签在该块不再重新
  分裂（保证终止）。每次合并记录为 `MergeEvent`（块/阶段/轮次/被并
  标签），见 `result.merges`——合并发生处可定位。
- **断言判定**：只有**每个**可达分区都被符号包含证明时才判 `proved`；
  逐分区结论见 `AssertStatus.partition_verdicts`。无可达分区时与旧
  语义一样空真 `proved`（`vacuous=True`）。
- 结果新增字段：`partition_points`、`max_partitions`、`merges`、
  `block_partitions_in` / `block_partitions_out`（`Partition(label,
  state)` 元组，`label=None` 即 merged 分区）；`block_in` / `block_out`
  仍是各分区的凸包视图，旧接口不受影响。
- 证明仍由**分区转移包含性**（`check_local_soundness` 逐分区独立复核
  块转移、守卫边与断言）与**循环后不动点**检查支持；独立有限执行
  （`run_bounded`）只能用于找反例，不能用采样代替证明。
- 非法分区参数抛可定位的 `ValidationError`：超过 3 个位置、重复、
  未知块、无守卫的块、`max_partitions` 非正整数或 bool。


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
4. **断言判定**：在断言所在语句位置的状态上检查观测区间是否**符号包含**
   于要求区间；包含为 `proved`，否则为 `unknown`（无法证明不是错误，
   不抛异常、不输出 violation）。
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
- 本库只实现本题规定的有限数学子集（无乘除、无数组/堆、无过程调用、
  无整数溢出模型），**不宣称兼容任何行业标准分析框架**。

## demo 会真实展示什么

`python demo.py` 固定构造若干程序并真实求解：

1. 有界循环 `i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5`：
   每块入/出不变量、两条断言 **PROVED**，以及收窄改善
   `exit: [5,+inf) → [5,5]`；独立检查器复核通过；独立具体执行器枚举
   body 块具体值域 [0,4] 并确认被抽象区间覆盖。
2. 无界增长循环 `i=0; while(i>=0){assert i<=5; i++}`：循环头
   `[0,+inf)`、退出支不可达（bottom），断言输出 **UNKNOWN**（非错误）。
3. 有限路径分区：`if (y>=0) x=1 else x=2; if (y>=0) assert x<=1 else
   assert x>=2`——凸包模式两条断言 UNKNOWN，以第一个 `if` 为分区位置
   后两条均 **PROVED**（T/F 分区各自记住 y 的符号，"走错支"的分区被
   第二个守卫过滤成底）。
4. 强制合并：三个顺序条件位置（2^3=8 种标签组合）在 `max_partitions=2`
   下触发合并，打印每次合并的发生处与被并标签，断言仍全部 PROVED。
5. 真实触发一个拒绝边界：`AssignConst("i", True)` 抛带定位的
   `ValidationError`。

## 已知限制

- 非关系型区间域：无法推导变量间关系（如 `y = x` 后 `x <= y` 之外的
  关联），存在固有精度损失，部分真命题只能得到 `unknown`。分区模式只
  按指定条件的最近真/假分组，不引入关系数值域，不能代替关系域。
- 缺省（未启用分区）时合并一律取凸包：`x=0` 与 `x=10` 合并为 `[0,10]`；
  分区模式也只保留至多 3 个指定位置、每块至多 `max_partitions` 个分区，
  超限即丢失标签退回凸包。
- 仅支持四种语句与两种守卫；入口不可达块（从 entry 不可达）保持 bottom，
  不参与分析。
- 具体执行器仅适合有界小程序对照/找反例；对无界循环会在状态预算处截断
  并显式标记 `truncated=True`，无界情形的健全性由符号检查器承担。
- 加宽阈值（前两次 join）与收窄上限（8 轮）按题面固定，未做阈值自适应。

## 目录

```
interval_ai/
  errors.py    错误类型与整数参数校验（NaN/Infinity/bool 拒绝）
  intervals.py 区间与逐变量抽象状态（join/widen/narrow/包含）
  cfg.py       CFG/Block/Guard/语句 数据结构与构造期校验
  transfer.py  局部抽象转移（语句、守卫边过滤）
  engine.py    RPO 不动点引擎：延迟加宽 + 至多 8 轮收窄
  partition.py 可选有限路径分区：标签分组、超上限按标签序合并
  checker.py   独立符号包含性检查器（不采样、不依赖核心；逐分区复核）
  concrete.py  独立确定性具体执行器（有界程序对照/找反例）
tests/         98 个 unittest 用例（域/引擎/分区/检查器/错误语义/具体覆盖）
demo.py        固定输入演示
```
