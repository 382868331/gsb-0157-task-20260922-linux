# 整数循环的区间抽象解释 + 差分约束（interval_ai）

一个从零实现、仅依赖标准库的**区间域抽象解释**可复用题库：输入小型控制流图
（CFG，变量为数学整数），输出每个基本块的入/出区间不变量、循环加宽/收窄
迭代过程，并对范围断言给出 `proved` / `unknown` 结论。另含一个**独立**的
局部转移包含性检查器（符号端点证明，不做有限采样）和一个**独立**的
确定性具体执行器（仅用于有界程序的覆盖性对照）。

本次迭代在区间域之外加入 **`x - y <= c` 差分约束关系域**（difference-bound
matrix，DBM），与区间域组成**简约积**：两个域在赋值、分支合流、循环入口
处交换信息，从而证明区间单独无法表达的**变量差值关系**。

## 运行环境

- Python **3.14.7**（不使用 3.14 之外的新语法外特性；3.10+ 的 `X | Y` 注解可用）。
- **无第三方依赖**，安装 Python 后直接运行；核心、测试、demo 全部离线，
  不访问网络、不需要账号/密钥/数据库/中间件/Docker。
- Linux 原生运行验证。

```bash
# 必要测试
python -m unittest discover -s tests -v

# 固定输入演示（约 0.05 秒，远小于 90 秒预算；真实计算，无 sleep、无预录结果）
python demo.py
```

## 语言子集与输入上限

| 项目 | 契约 |
|---|---|
| 变量数 | 1 ≤ 变量 ≤ **20**；**含差分语句时变量 ≤ 4** |
| 基本块数 | 1 ≤ 块 ≤ **40** |
| 语句 | `x = c`、`x = y`、`x = y + c`（c 为任意整数，可负）、`assert lo <= x <= hi`（端点可无穷）、**`assume x - y <= c`**、**`assert x - y <= c`** |
| 块尾条件 | `x <= c`、`x >= c`；真支走第 0 个后继，假支（整数补集）走第 1 个后继 |
| 后继数 | 0（终止块）、1（无条件）、2（必须带守卫） |
| 数值域 | 数学整数（Python 任意精度 `int`），无溢出、无除法/乘法/函数调用 |

差分语句：

- `AssumeDiff(x, y, c)`：假设 `x - y <= c`。`y=None` 表示右端取零常数节点
  （即 `x <= c`）；`x=None` 表示左端取零（`-y <= c` ⇔ `y >= -c`）。
  假设与已有约束矛盾（Floyd–Warshall 闭包出现负环）时，该路径不可达。
- `AssertDiff(x, y, c)`：断言 `x - y <= c`，不改变状态，结论 `proved`/
  `unknown`；不可达位置空真 `proved` 且 `vacuous=True`。
- 两端不得同时为零节点，`x` 与 `y` 不得是同一变量；含任一差分语句的
  CFG 变量数超过 4 时构造期抛 `ValidationError`（DBM 为 5×5 小矩阵）。

守卫的整数补集：`x <= c` 为假 ⇔ `x >= c+1`；`x >= c` 为假 ⇔ `x <= c-1`。

## 公开接口与数据结构

```python
from interval_ai import (
    # CFG
    CFG, Block, Guard,
    AssignConst, AssignCopy, AssignAdd, AssertRange,
    AssumeDiff, AssertDiff,          # 差分约束（新增）
    MAX_DIFF_VARIABLES,              # = 4
    # 域
    Interval, AbstractState, DiffState,
    # 分析
    analyze, AnalysisResult, AssertStatus, DiffAssertStatus,
    MAX_NARROWING_ROUNDS, DEFAULT_LOOP_BUDGET,
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

- `Interval(lower, upper)`：闭整数区间；`None` 表示无穷端点。提供 `join`
  （凸包）、`intersect`、`subseteq`、`add`、`widen`、`narrow`。
- `DiffState(variables, matrix)`：闭包后的差分界矩阵（内部含零常数节点）。
  常用观测：`bound_of(x, y)`（已推出的最紧 `x-y` 上界，`None` 为 +∞）、
  `implies(x, y, c)`、`interval_of(x)`；转移：`assume`、`assign_const`、
  `assign_copy`、`assign_add`、`join`、`widen_selective`、`narrow_selective`。
- `CFG(variables, blocks, entry, entry_bounds=None)`：构造时一次性校验，
  非法输入抛 `ValidationError`（异常 `location` 可定位到块/语句/参数）。
- `result = analyze(cfg, *, loop_budget=256)`：
  - `result.block_in[name]` / `result.block_out[name]`：`AbstractState`
    （`bottom=True` 表示不可达）；
  - `result.asserts`：每个 `AssertRange` 一条 `AssertStatus`；
  - `result.diff_asserts`：每个 `AssertDiff` 一条 `DiffAssertStatus`
    （`verdict ∈ {"proved","unknown"}`、`observed_bound`、`vacuous`）；
  - `result.block_in_diff` / `result.block_out_diff`：每块入/出的 `DiffState`；
    便捷读取用 `result.diff_state_at(name)`；
  - `result.relational_enabled`：该 CFG 是否含差分语句；
  - `result.relational_converged`：关系迭代是否在 `loop_budget` 内收敛
    （`False` 表示未收敛，已退回纯区间结果，**所有非空真差分断言为
    `unknown`**，此时 `diff_state_at` 抛 `ValueError`）；
  - `result.widen_points`、`ascending_rounds`、`narrowing_rounds`、
    `post_widening_in/out`、`narrowing_refined`：加宽点、迭代轮数与收窄改善。
- `check_local_soundness(result) -> CheckReport`：独立符号检查入口包含、
  块转移精确性（区间与 DBM 两域）、每条守卫边包含、每类 `proved` 断言的
  包含；失败可 `report.raise_if_bad()`。
- `run_bounded(cfg, initial_stores)`：独立具体语义枚举，
  仅对有界程序完备；状态超预算时 `truncated=True`。报告新增
  `diff_violations`（违反 `AssertDiff` 的位置），`AssumeDiff` 不成立的
  具体路径被剪枝。

完整机读结果可用 `result.to_dict()`（关系结果额外带 `relational` 段）。

## 分析算法（设计取舍）

1. **控制流**：DFS 三色法识别回边，回边目标为加宽点；枚举顺序为入口可达
   部分的逆后序（RPO，插入顺序打破并列），结果确定。
2. **简约积与信息交换**：含差分语句的 CFG 在每个程序点同时维护区间状态与
   闭包 DBM。每条语句（含赋值最强后条件）、每次合流（DBM 逐表项取最大界
   = 标准合流）、每条守卫边之后做一次双向简约：区间端点并入 DBM 重新
   Floyd–Warshall 闭包，DBM 推出的端点再回写区间。不含差分语句的 CFG
   仍走原有纯区间引擎，行为与结果不变。
3. **赋值最强后条件**：`x = c` 加入 `x<=c / -x<=-c`；`x = y + k` 先在闭
   矩阵上保存 y 的整行整列、遗忘 x 的行列，再按 `new_x = v_y + k` 回填
   （`x=y` 自增也正确：旧关系经保存的行列传播，如循环中 `x++;y++` 后
   `y-x` 的界不变），最后重新闭包。
4. **上升迭代（延迟加宽）**：每个加宽点的**前两次扩张取凸包 join**，
   **第三次扩张起使用标准加宽**；区间与 DBM 都只加宽"该自然循环内被
   赋值修改"的变量（DBM 中即行或列命中这些变量的表项），其余取精确合流。
5. **收窄迭代**：上升稳定后做**至多 8 轮**混沌收窄（
   `MAX_NARROWING_ROUNDS = 8`），只允许把 +∞ 界换成新方程值的有限界，
   提前稳定则提前停。
6. **显式循环预算 / 未收敛语义**：关系上升迭代设明确预算 `loop_budget`
   （默认 `DEFAULT_LOOP_BUDGET = 256`）。预算内未收敛**不冒充证明**：
   本次分析退回纯区间结果（区间断言照常判定），非空真差分断言一律
   `unknown`，结果标记 `relational_converged=False`。另有防御性安全阀
   `ascending_budget`（默认 10000）：仅当它先于循环预算成为约束时抛
   `BudgetExhaustedError`（携带 `partial`，明确不是已验证不动点），
   与数据结论 `unknown` 严格区分。
7. **断言判定**：区间断言看观测区间是否符号包含于要求区间；差分断言看
   闭 DBM 的 `M[left][right] <= c`。无法证明即 `unknown`，不判为错误。
8. **独立性**：检查器（`checker.py`）与具体执行器（`concrete.py`）均不
   import 被测核心（`transfer`/`engine`/`relational`/`diffs`），端点算术、
   Floyd–Warshall 闭包、守卫补集各自重新实现；测试用 AST/模块扫描强制
   该约束。期望值来自手算或独立具体语义，不用被测核心算期望值。
9. **失败原子性**：CFG 为冻结结构且构造期完整校验，校验失败不返回对象；
   分析过程不修改 CFG，预算异常后 CFG 仍与调用前完全一致（有测试保证）。

## 数值与误差口径

- 全部计算使用 Python **任意精度整数**，不存在浮点结果，因此**无舍入误差、
  无容差**；端点与 DBM 界都是精确整数/符号比较，不用宽容差掩盖边界错误。
- 输入侧显式拒绝：`NaN`、`±Infinity`、非整数浮点、以及用 `bool`
  冒充整数（`True`/`False` 虽是 `int` 子类，按契约一律拒绝）。
- 本库只实现本题规定的有限数学子集（无乘除、无数组/堆、无过程调用、
  无整数溢出模型），**不宣称兼容任何行业标准分析框架**。

## demo 会真实展示什么

`python demo.py` 固定构造程序并真实求解（约 0.05 秒）：

1. 有界循环 `i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5`：
   入/出不变量、两条断言 **PROVED**、收窄改善 `exit: [5,+inf) → [5,5]`；
   独立检查器与独立具体执行器复核。
2. 无界增长循环 `i=0; while(i>=0){assert i<=5; i++}`：**UNKNOWN**（非错误）。
3. **分支合流的差值关系**：`x=0; if(j>=0){y=0}else{y=1}` 合流后区间只知
   `y∈[0,1]`，DBM 合流仍证 `x-y<=0` **PROVED**（区间单独无法表达）。
4. **循环入口的差值不变量**：`x=0;y=1; while(x<=4){assert y-x<=1;
   assert x-y<=-1; x++;y++}`——加宽后循环头仍保持两条差值界 **PROVED**，
   并有独立具体枚举对照零违反。
5. **未在迭代预算内收敛**（`loop_budget=1`）：差分断言明确 **UNKNOWN**，
   区间结论照常有效，检查器认可该保守回退。
6. 真实触发两个拒绝边界：`AssignConst("i", True)` 与"5 个变量 + 差分语句"
   均抛带定位的 `ValidationError`。

## 已知限制

- 差分区是 **DBM（x-y<=c）而非完整多面形域**：不能表达三项及以上的线性
  约束（如 `x+y<=c`），也不区分严格/非严格（本题变量是整数，`<=` 已够用）。
- 非关系型信息仍有固有精度损失：合流取凸包、无析取/路径分裂；部分真命题
  即使有了 DBM 仍只能得到 `unknown`。
- 差分语句限定至多 **4 个变量**（题面约定的小规模范围）；超过即拒绝，
  不做更大矩阵的性能扩展。未收敛只在显式预算被调小时实际发生（加宽保证
  DBM 上升链有限，正常程序个位数轮次即收敛）。
- 仅支持六种语句与两种守卫；入口不可达块保持 bottom，不参与分析。
- 具体执行器仅适合有界小程序对照；对无界循环会在状态预算处截断并显式
  标记 `truncated=True`，健全性由符号检查器承担。
- 加宽阈值（前两次 join）与收窄上限（8 轮）按题面固定，未做阈值自适应。

## 目录

```
interval_ai/
  errors.py      错误类型与整数参数校验（NaN/Infinity/bool 拒绝）
  intervals.py   区间与逐变量抽象状态（join/widen/narrow/包含）
  diffs.py       差分界矩阵 DBM：闭包、赋值最强后条件、join/widen/narrow
  cfg.py         CFG/Block/Guard/语句（含 AssumeDiff/AssertDiff）与构造期校验
  transfer.py    区间局部抽象转移（语句、守卫边过滤）
  relational.py  区间 × DBM 简约积（语句/合流/守卫后的双向信息交换）
  engine.py      RPO 不动点引擎：延迟加宽 + 至多 8 轮收窄 + 循环预算回退
  checker.py     独立符号包含性检查器（区间与 DBM 各自重写，不采样）
  concrete.py    独立确定性具体执行器（有界程序对照；差分假设剪枝）
tests/           unittest 用例（域/DBM/引擎/简约积/枚举对照/检查器/错误语义）
demo.py          固定输入演示
```
