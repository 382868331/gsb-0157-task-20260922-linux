# 整数循环的区间抽象解释（interval_ai）

一个从零实现、仅依赖标准库的**区间域抽象解释**可复用题库：输入小型控制流图
（CFG，变量为数学整数），输出每个基本块的入/出区间不变量、循环加宽/收窄
迭代过程，并对范围断言给出 `proved` / `unknown` 结论。另含一个**独立**的
局部转移包含性检查器（符号端点证明，不做有限采样）和一个**独立**的确定性
具体执行器（仅用于有界程序的覆盖性对照/找反例）。

**可选有限路径分区模式**：调用方可指定至多 3 个块尾条件作为"分区位置"，
状态按这些位置最近一次真假分组传播，保留两支汇合后被凸包丢掉的路径信息
（非关系域不变），同时分区数有显式上限，超限按标签顺序强制合并、只丢标签
不删状态。

## 运行环境

- Python **3.14.7**（3.10+ 的 `X | Y` 注解可用）。
- **无第三方依赖**，安装 Python 后直接运行；核心、测试、demo 全部离线，
  不访问网络、不需要账号/密钥/数据库/中间件/Docker。
- Linux 原生运行验证。

```bash
# 必要测试（114 个用例）
./.venv/bin/python -m unittest discover -s tests -v

# 固定输入演示（约 0.1 秒，远小于 90 秒预算；真实计算，无 sleep、无预录结果）
./.venv/bin/python demo.py
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
    Label, PartitionedState, MergeEvent, PartitionAssert,
    MAX_PARTITION_POINTS, DEFAULT_MAX_PARTITIONS, TRUE, FALSE, UNKNOWN,
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

## 有限路径分区模式（可选）

普通模式在每个汇合点对所有前驱取区间凸包，路径上"哪个条件走了哪支"的
信息被丢掉。分区模式允许调用方指定**至多 3 个条件位置**：

```python
result = analyze(cfg, track_guards=("fork1", "fork2"), max_partitions=8)
```

- `track_guards`：块名序列（1–3 个，块必须恰有两路后继且带 `Guard`；
  重复/不存在/非守卫块抛带定位的 `ValidationError`）。`None`/`()` 为普通模式。
- `max_partitions`：**每个块**分区数的显式上限（`int >= 1`，默认 8）。

**标签**：长度等于分区点数，每槽记录该位置**最近一次**经过时的真假：

| 值 | 含义 |
|---|---|
| `TRUE` / `FALSE` | 最近一次经过该条件走真/假支 |
| `UNKNOWN`(`?`) | 还从未经过该条件（路径上确实未知） |
| 冻结槽（文本 `x`） | 该槽因强制合并被抹除，值回退为未知且此后不再分裂 |

标签只记"最近一次"：循环再次经过被跟踪条件时槽位被**覆写**，旧真假不会
被永久固定成路径事实。注意文本里未经过 `?` 与被合并抹除 `x` 是两种不同
状态（例如同块并存时分别显示 `?.?` 与 `x.x`）。每个分区内部仍是逐变量区间（**不引入关系域**），
转移、循环 widening（前两次凸包、第三次起标准 widening）与收窄（至多 8 轮）
逐分区沿用同一套机制。

**结果访问**：

- `result.partitioned`、`result.track_guards`、`result.max_partitions`；
- `result.partition_in[block]` / `partition_out[block]`：`PartitionedState`，
  其 `.members` 为 `{Label: AbstractState}`，空映射 = 不可达；
- `result.reachable_partitions(block)`：`[(Label, AbstractState), ...]`（按标签顺序）；
- `result.partition_state_at(block, label)`；
- `result.merges`：`MergeEvent` 元组（见下）；
- `result.block_in/out` 仍是各分区的**凸包视图**（与普通模式同形状），
  校验保证它恰好等于各分区凸包（不删状态、不凭空放宽）；
- 每条 `AssertStatus` 在分区模式下带 `.partitions`（每个可达分区各自的观测）。

**断言判定**：一个位置只有在其**每个可达分区**上观测区间都符号包含于
要求区间时才 `proved`；不可达位置（无任何可达分区）仍为空真 `proved` +
`vacuous=True`。判定是符号端点包含，不采样。

**超上限强制合并**：某块分区数超过 `max_partitions` 时，按标签总序取最末
两个逐槽泛化（槽值一致则保留，冲突则抹成 `?` 并**冻结**该槽），区间取凸包；
被冻结的槽此后经过该条件不再重新分裂（这是上限的精度代价，也是"丢失标签"
的字面含义）。**只丢标签、不删状态**：合并前后所有分区的总凸包严格相等。
每次合并产生一个 `MergeEvent`（`block` / `round` / `surviving` / `dropped` /
`partitions_after`，`.location` 给出"在哪个块第几轮、哪些标签并成什么"）。

**健全性/终止性依据**：标签语义在无冻结细网格（k≤3 共 3^k≤27 格）上用
具体化集合 γ 说明（冻结槽任取三值）；上升迭代在细网格上累积、被覆盖细格
喂给所有覆盖它的粗分区、无宿主才新建，超限时合并（被吸收标签的 γ 是幸存
标签 γ 的子集）。结构事件（新生/冻结）有限，每个标签上的区间链由标准
widening 收敛，故必然终止。独立检查器（下）在细网格上复核边包含、cap、
合并事件结构与逐分区断言——它**不**导入 `engine`/`partitions`/`transfer`。

**已知精度边界**：分区只在指定位置、只记最近一次结果；不跟踪条件之间的
任意逻辑组合，也不区分同一标签下的更早历史。`max_partitions=1` 会把路径
信息全部冻结，结果与普通模式一致（有测试保证）。

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

`./.venv/bin/python demo.py` 固定构造程序并真实求解（约 0.1 秒）：

1. 有界循环 `i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5`：
   每块入/出不变量、两条断言 **PROVED**，以及收窄改善
   `exit: [5,+inf) → [5,5]`；独立检查器复核通过；独立具体执行器枚举
   body 块具体值域 [0,4] 并确认被抽象区间覆盖。
2. 无界增长循环 `i=0; while(i>=0){assert i<=5; i++}`：循环头
   `[0,+inf)`、退出支不可达（bottom），断言输出 **UNKNOWN**（非错误）。
3. 真实触发一个拒绝边界：`AssignConst("i", True)` 抛带定位的
   `ValidationError`。
4. **分区提升**：`x∈[0,10]; if(x<=3){y=0}else{y=10}; if(y>=5){assert x>=4}`
   普通凸包 **UNKNOWN**（hot 块 x 回到 [0,10]），跟踪第一条件后
   **PROVED**（hot 只来自假支 x∈[4,10]）；具体枚举仅作覆盖性对照。
5. **循环翻转**：`while(x<=4){ if(x>=3) flag=100 else flag=0; x++ }` 后
   `assert flag==100`：标签随迭代覆写，退出分区拿到最后一次（真）结果，
   普通 **UNKNOWN**、分区 **PROVED**。
6. **强制合并**：三个串行守卫汇合（4 个可达细标签），`max_partitions=3`
   时报告合并发生的块/轮次/标签，合并后总凸包不变（只丢标签、不删状态）。

## 已知限制

- 非关系型区间域：无法推导变量间的算术关系（如 `x = y + z` 后 `x` 与
  `y,z` 的线性约束）。可选分区模式恢复的只是"指定条件最近一次真假"这条
  **守卫历史**信息，**不引入任何关系数值域**。
- 普通模式合并一律取凸包：`x=0` 与 `x=10` 合并为 `[0,10]`，不含析取；
  需要路径精度时由调用方显式打开分区模式并指定位置（至多 3 个、只记最近
  一次、上限内合并）。
- 仅支持四种语句与两种守卫；入口不可达块（从 entry 不可达）保持 bottom，
  不参与分析。
- 具体执行器仅适合有界小程序对照、找反例；对无界循环会在状态预算处截断并
  显式标记 `truncated=True`。**证明只来自分区转移包含性 + 循环后不动点
  检查**（符号端点），独立有限执行不能代替证明。
- 加宽阈值（前两次 join）与收窄上限（8 轮）按题面固定，未做阈值自适应。
- 分区只按"最近一次"结果分组：不表达条件间的任意布尔组合、不保留更早
  历史；分区数超上限的合并是有意的精度损失（冻结槽在结果与 `MergeEvent`
  中显式可见）。

## 目录

```
interval_ai/
  errors.py      错误类型与整数参数校验（NaN/Infinity/bool 拒绝）
  intervals.py   区间与逐变量抽象状态（join/widen/narrow/包含）
  cfg.py         CFG/Block/Guard/语句 数据结构与构造期校验
  transfer.py    局部抽象转移（语句、守卫边过滤）
  partitions.py  有限路径分区：Label(含冻结γ)/PartitionedState/强制合并
  engine.py      RPO 不动点引擎：延迟加宽 + 至多 8 轮收窄 + 分区路径
  checker.py     独立符号包含性检查器（含细网格分区复核；不采样、不依赖核心）
  concrete.py    独立确定性具体执行器（有界程序对照/找反例）
tests/           114 个 unittest 用例（域/引擎/检查器/错误/具体/分区）
demo.py          固定输入演示（普通结果 + 分区三项能力 + 拒绝边界）
```
