# 整数循环的区间抽象解释（interval_ai）

一个从零实现、仅依赖标准库的**区间域抽象解释**可复用题库：输入小型控制流图
（CFG，变量为数学整数），输出每个基本块的入/出区间不变量、循环加宽/收窄
迭代过程，并对范围断言给出 `proved` / `unknown` 结论。另含一个**独立**的
局部转移包含性检查器（符号端点证明，不做有限采样）和一个**独立**的确定性
具体执行器（仅用于有界程序的覆盖性对照）。

本次迭代在区间域之上接入了 **`x - y <= c` 差分约束关系域（DBM 差界矩阵）**：
关系域与区间域构成**归约积（reduced product）**，在赋值、分支合流、循环
入口每一步双向交换信息，可证明纯区间域无法表达的变量差值关系。

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
| 变量数 | 纯区间程序 1 ≤ 变量 ≤ **20**；**含差分约束语句时 ≤ 4** |
| 基本块数 | 1 ≤ 块 ≤ **40** |
| 语句 | `x = c`、`x = y`、`x = y + c`（c 为任意整数，可负）、`assert lo <= x <= hi`（端点可无穷）、`assume x - y <= c`、`assert x - y <= c` |
| 块尾条件 | `x <= c`、`x >= c`；真支走第 0 个后继，假支（整数补集）走第 1 个后继 |
| 后继数 | 0（终止块）、1（无条件）、2（必须带守卫） |
| 数值域 | 数学整数（Python 任意精度 `int`），无溢出、无除法/乘法/函数调用 |
| 差分操作数 | 必须是两个**已声明且互不相同**的变量；`c` 为任意整数（可负），拒绝 bool/浮点 |

守卫的整数补集：`x <= c` 为假 ⇔ `x >= c+1`；`x >= c` 为假 ⇔ `x <= c-1`。

`assume x - y <= c` 是路径条件（不是断言）：与已有约束矛盾时该路径不可达
（后继状态为底，与守卫过滤整个整数补集一致）；`assert x - y <= c` 不改变
状态，只给 `proved` / `unknown`。

## 公开接口与数据结构

```python
from interval_ai import (
    # CFG
    CFG, Block, Guard,
    AssignConst, AssignCopy, AssignAdd, AssertRange,
    AssumeDiff, AssertDiff,          # 差分约束（关系域语句）
    # 域
    Interval, AbstractState,
    DiffState, ProductState,         # 差界矩阵视图 / 区间×差界 归约积
    # 分析
    analyze, AnalysisResult, AssertStatus, DiffAssertStatus,
    MAX_NARROWING_ROUNDS, DEFAULT_RELATION_BUDGET,
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
  - **差分约束**（仅 `cfg.uses_diff_domain=True` 时）：
    - `result.diff_in[name]` / `result.diff_out[name]`：`DiffState`
      （闭包后的差界矩阵；`bottom=True` 不可达），`d.bound("x","y")`
      返回可符号推出的最紧 `x-y` 上界（推不出为 `None`），
      `d.entails("x","y",c)` 判定蕴含，`d.interval_of("x")` 投影回区间；
    - `result.diff_asserts`：每个 `AssertDiff` 一条 `DiffAssertStatus`
      （`verdict`、`observed_bound`、`vacuous`）；
    - `result.relation_truncated` / `result.relation_rounds`：关系域是否
      因迭代预算未收敛而被放弃、实际上升轮数。
- `analyze(cfg, *, ascending_budget=10000, relation_budget=10000)`：
  `relation_budget` 是关系域上升迭代的显式轮数预算。**耗尽时不抛异常、
  不冒充证明**：关系域整体放弃（`diff_in/out` 为 `None`、
  `relation_truncated=True`），重跑纯区间分析给出区间结论，全部差分断言
  为 `unknown`（含不可达位置——未收敛时可达性也不可信）。区间
  `ascending_budget` 仍是防御性安全阀，耗尽抛 `BudgetExhaustedError`。
- `check_local_soundness(result) -> CheckReport`：独立符号检查
  入口包含、块转移精确性、每条守卫边包含、每个 `proved` 断言的包含；
  对关系程序额外在独立重写的"区间 × 差界矩阵"积参考上逐差界比较；
  截断模式下仍复核区间部分且拒绝任何差分 `proved`。
  失败可 `report.raise_if_bad()`。
- `run_bounded(cfg, initial_stores)`：独立具体语义枚举，
  仅对有界程序完备，状态超预算时 `truncated=True`（明确标记、不冒充证明）。
  `AssumeDiff` 不成立时该具体路径被剪掉，`AssertDiff` 违例记入
  `assert_violations`。

完整机读结果可用 `result.to_dict()`。

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
5. **关系域（DBM 差界矩阵）**：节点 0 是值恒 0 的参考点，节点 i≥1 对应
   变量；`M[i][j]` 是最紧的 `x_i - x_j <= M[i][j]`（`None` 为 +∞），
   矩阵始终保持 Floyd-Warshall 最短路径闭包，对角线 < 0 即负环（不可达）。
   - **归约积**：每步把区间端点注入零节点两条边 → 闭包 → 把被关系压紧的
     端点抽回区间，一次闭包即到归约不动点（`y=x` 后守卫 `x<=0` 真支上
     自动推出 `y<=0`；`x-y<=0` 且 `x>=4` 推出 `y>=4`）。
   - **赋值**：`x=c` 重建 x 的零节点两边；`y=x` 加两条 0 边；
     `y=x+k` 加 `(k, -k)` 两边；`x=x+k` 用行/列平移保留与第三变量的
     已有差界；重赋值先 forget 旧变量全部入射/出射边。
   - **合流**：DBM 合并取逐边最弱界（点态取弱后重新闭包）。
   - **循环**：DBM 加宽/收窄逐边且**选择性**——只有端点触及该循环被修改
     变量的边允许推到 +∞（与区间选择性加宽同一张"循环内被修改变量表"），
     循环内不改的变量间精确关系（如 `y==x`）取精确凸包、不被冲掉。
   - **预算**：关系上升迭代有独立的显式轮数预算 `relation_budget`
     （默认 10000）；未收敛即放弃关系域、差分断言全 `unknown`，与
     `proved` 严格分离，详见接口小节。
6. **独立性**：检查器（`checker.py`）与具体执行器（`concrete.py`）均不
   import 被测核心（`transfer`/`engine`/`dbm`），DBM 闭包、赋值、守卫
   过滤都在 checker 中平行重写；测试用 AST 扫描强制 checker/concrete 不
   依赖核心。期望值来自手算、独立 DBM 参考或独立具体语义，不用被测核心
   算期望值；往返一致仅作补充。
7. **预算与无解分离**：区间 widening 保证上升链有限，数学上必然终止；
   `ascending_budget`（默认 10000）只是防御性安全阀，耗尽抛
   `BudgetExhaustedError`（携带 `partial`，但明确不是已验证不动点），
   与 `unknown`（正常数据结论）严格区分。关系预算耗尽是另一种语义：
   **不抛异常**，置 `relation_truncated` 并给所有差分断言 `unknown`。
8. **失败原子性**：CFG 为冻结结构且构造期完整校验，校验失败不返回对象；
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

`python demo.py` 固定构造若干程序并真实求解（约 0.05 秒，远小于 90 秒预算）：

1. 有界循环 `i=0; while(i<=4){assert 0<=i<=4; i++}; assert i==5`：
   每块入/出不变量、两条断言 **PROVED**，以及收窄改善
   `exit: [5,+inf) → [5,5]`；独立检查器复核通过；独立具体执行器枚举
   body 块具体值域 [0,4] 并确认被抽象区间覆盖。
2. 无界增长循环 `i=0; while(i>=0){assert i<=5; i++}`：循环头
   `[0,+inf)`、退出支不可达（bottom），断言输出 **UNKNOWN**（非错误）。
3. 真实触发一个拒绝边界：`AssignConst("i", True)` 抛带定位的
   `ValidationError`。
4. **差分约束**：`y=x; if(x<=0){assert y-x<=0; assert y<=0}` 在真支
   推出区间单独得不到的 `y∈(-∞,0]`（假支 `y∈[1,+∞)`）；
   关系循环 `x=0;y=2; while(x<=3){assert y-x==2; x++;y++}` 在加宽/收窄
   后保住 `y-x==2`，独立具体枚举确认 body 差值恒为 2。
5. **差分无法证明**：`assume x-y<=2; assert x-y<=1` 输出 **UNKNOWN**。
6. **关系预算边界**：`relation_budget=1` 时 `relation_truncated=True`、
   差分断言全 **UNKNOWN**，区间结论仍独立给出且检查器通过。
7. 再触发一个差分语句拒绝边界：`AssumeDiff("x","x",0)` 同变量操作数被拒。

## 已知限制

- 纯区间域是非关系型的：程序不含差分语句时无法推导变量间关系，部分真
  命题只能得到 `unknown`。接入关系域后，差值表达力以**最多 4 个变量**
  为限（DBM 规模 O(n²)、闭包 O(n³)），且只能表达 `x-y<=c` 这一族
  线性约束，不能表达三元以上线性式、乘法、析取路径。
- 合并一律取凸包：`x=0` 与 `x=10` 合并为 `[0,10]`；DBM 合并取逐边最弱
  界，不含析取/路径分裂，合流点会固有地丢失路径私有精度。
- 支持六种语句与两种守卫；入口不可达块（从 entry 不可达）保持 bottom，
  不参与分析。
- 具体执行器仅适合有界小程序对照；对无界循环会在状态预算处截断并显式
  标记 `truncated=True`，无界情形的健全性由符号检查器承担。
- 加宽阈值（前两次 join）与收窄上限（8 轮）按题面固定，未做阈值自适应。
- 关系域收敛由加宽保证；`relation_budget` 是防御性显式预算，正常小
  程序远不会触及，触及即按契约降级为 unknown 而非给出不可信不变量。

## 目录

```
interval_ai/
  errors.py    错误类型与整数参数校验（NaN/Infinity/bool 拒绝）
  intervals.py 区间与逐变量抽象状态（join/widen/narrow/包含）
  cfg.py       CFG/Block/Guard/语句（含 AssumeDiff/AssertDiff）与构造期校验
  dbm.py       差界矩阵域 + 区间×差界 归约积（闭包/赋值/合流/加宽/守卫）
  transfer.py  区间局部抽象转移（语句、守卫边过滤）
  engine.py    RPO 不动点引擎：延迟加宽 + 至多 8 轮收窄；关系域路径与预算
  checker.py   独立符号包含性检查器（含独立 DBM 积参考；不采样、不依赖核心）
  concrete.py  独立确定性具体执行器（有界程序对照；支持两类差分语句）
tests/         125 个 unittest 用例（域/引擎/关系域/检查器/错误语义/具体覆盖）
demo.py        固定输入演示
```
