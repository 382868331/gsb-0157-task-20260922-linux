# 整数循环的区间抽象解释（interval abstract interpretation）

一个零依赖、可导入的 Python 库：对小型控制流图（CFG）做**区间域抽象
解释**，输出每个基本块的入/出不变量，证明 `assert x ∈ [lo, hi]` 范围
断言；证明不了时给出 `unknown`（**不**判为错误）。另含一个**独立的
局部转移包含性检查器**（符号端点证明，禁止用有限采样冒充证明）和一个
**独立具体执行参考**（仅测试中用于有界程序的覆盖性对照）。

## 运行环境

* Python **3.14.7**（用到较新的类型语法；3.10+ 亦可运行，但以 3.14.7 为准）
* Linux 原生运行；**仅标准库，无需安装任何第三方依赖**
* 完全离线：不访问网络、不需要账号/密钥/数据库/中间件/云 API/Docker

## 准确命令

```bash
# 必要测试（在仓库根目录）
python -m unittest discover -s tests -v

# 固定输入演示（约 0.1 秒，远小于 8 秒预算；真实计算，无 sleep、无预录结果）
python demo.py
```

## 输入上限（接口边界）

| 项目 | 上限 |
|---|---|
| 变量数 | 20 |
| 基本块数 | 40 |
| 单块语句数 | 100 |
| 上升迭代预算 | 默认 200 轮（可配置） |
| narrowing 轮数 | **最多 8 轮**（可配置 0–8） |

规模上限在 `Program` 构造时严格校验，超限抛 `LimitExceededError`。
演示只使用小规模固定输入，不穷举上限。

## 公开数据结构与接口

### CFG（`interval_ai.cfg`，从包根 `interval_ai` 直接导入）

* `Program(variables, blocks, entry, entry_state=None)`
  * `variables: tuple[str, ...]`：唯一、非空变量名；
  * `blocks: tuple[Block, ...]`：唯一命名块；
  * `entry: str`：入口块名；
  * `entry_state: tuple[int,...] | None`：入口具体初值（长度须等于
    变量数）；缺省所有变量初始为 `[0,0]`。
* `Block(name, statements, branch=None)`
* 语句（均为不可变 dataclass）：
  * `Assign("x", c)` —— `x := c`
  * `Copy("x", "y")` —— `x := y`
  * `AddConst("x", c)` —— `x := x + c`（`c` 可为负）
  * `AssertRange("x", lo, hi, assert_id="a")` —— 断言 `x∈[lo,hi]`，
    不改变计算状态；结果按 `assert_id` 报告。
* 出边：
  * `Jump(target)`
  * `Cond("x", "<=", c, taken, skipped)`（假边为 `x > c`）
  * `Cond("x", ">=", c, taken, skipped)`（假边为 `x < c`）
  * `None`：无后继（出口块）。真/假边目标允许相同。

### 域（`interval_ai.interval.Interval`）

`Interval(lo, hi)`，端点为任意精度 Python `int`；`None` 表示 ±∞。
方法：`Interval.of(c)`、`Interval.top()`、`hull`（凸包 join）、
`widen`、`narrow`、`meet`、`restrict_le/restrict_ge`、`add_const`、
`contains`、`subset_eq`、`to_dict`（无穷端点序列化为 `null`）。

### 分析（`interval_ai.analyze` / `Analyzer`）

```python
from interval_ai import Program, Block, Assign, AddConst, Cond, Jump, AssertRange, analyze

result = analyze(program)                 # 或 Analyzer(program).analyze()
result.all_invariants()                   # 每块 entry/exit 不变量
result.in_states[name] / .out_states[name] / .edge_states[(a,b)]
result.status_of("assert_id")             # "proved" | "unknown"
result.assertions                         # AssertResult（含 observed_interval）
result.loop_headers / result.back_edges   # DFS 识别结果
result.ascending_rounds / .narrowing_rounds / .widen_expansions
result.to_dict()                          # JSON 友好（±∞ 为 null）
```

### 独立检查器与参考

* `check_analysis(program, result) -> CheckReport`：对一份分析结果做
  独立的局部归纳证书验收（入口初值包含、每块入边凸包包含、独立重算
  的块边像包含、proved 断言的独立端点证实）。
* `check_block_transfer(program, block_name, entry_intervals, claimed_edges)`：
  单块局部转移包含性检查。
* `execute_concrete(program)`：独立具体执行参考（在 `reference.py`，
  不导入任何核心模块），枚举可达具体 `(块, 整数存储)`，供测试做有界
  程序的覆盖性对照；无界程序抛 `ConcreteBudgetExhausted`。

## 错误语义

所有错误继承 `IntervalAIError`，均带可定位的 `where` 上下文：

| 异常 | 触发 |
|---|---|
| `InvalidOperandError` | 常量/端点不是有限数学整数（拒绝 `float`，含 NaN/Infinity；**拒绝 `bool`**；拒绝非整数对象）；空区间等 |
| `ProgramStructureError` | 空变量/块列表、语句或分支形状错、算符非 `<=`/`>=` 等 |
| `DuplicateIdError` | 变量名、块名或断言 id 重复 |
| `InconsistentGraphError` | 边指向不存在的块、entry 不存在、引用未声明变量 |
| `LimitExceededError` | 超过 20 变量 / 40 块 / 单块 100 语句 |
| `AnalyzerBudgetExhausted` | 上升迭代预算耗尽仍未稳定 |

要点：

* **非法输入即抛、不静默纠正**；`Program` 校验在构造期一次性完成，
  抛错时对象不存在，不存在部分变更。
* **预算耗尽 ≠ 证不出**：预算耗尽抛 `AnalyzerBudgetExhausted`；
  正常算完但无法证明的断言给 `status="unknown"`，二者严格分开。
* 不可达块中的断言按空真（vacuously true）记为 `proved`，
  `AssertResult.reachable=False`。

## 算法与设计取舍

1. **区间格**：非空整数区间，端点 `int | None`（`None=±∞`）；不可达
   用单独的 bottom 状态表示，不引入空区间。偏序为集合包含，join 为
   最小外包（凸包）。
2. **循环识别**：从 entry 做三色 DFS，指向 GRAY 祖先的边为回边，其
   目标为循环头；迭代顺序为逆后序（RPO），entry 不可达的块追加在
   末尾且恒为 bottom。
3. **上升阶段**：
   * 循环头维护“扩张计数”。入状态每次真正变大：**第 1、2 次扩张用
     普通凸包 join；第 3 次扩张起使用标准区间 widening**（变化的端点
     立即推到 ±∞，未变化端保持）。
   * 采用**局部化 widening**：循环头只加宽“在本循环回边路径上被赋值”
     的变量（循环体由回边源反向 BFS 得到），其余变量只做凸包。这是
     Cousot 经典做法，避免嵌套循环中内层头把外层变量错误推到无穷。
4. **下降阶段**：达到后置不动点后，循环头用标准 narrowing（只把无穷
   端点替换为新一轮的有限界，有限端绝不移动，保证单调可靠），最多
   8 轮，任一轮全局无变化即停。这一步把 widening 推出的 `+∞` 收回
   为精确界（如 `i<=10` 循环出口收回为 `i==11`）。
5. **终止性**：被加宽变量的区间链有限；非加宽变量在其所在循环体内为
   恒等像，其上升由外层循环头的 widening 兜底，故整体有限步终止；
   预算耗尽作为独立的失败模式上报。
6. **可靠性（soundness）**：assert 仅当抽象区间（端点有限）包含于
   断言范围才判 proved；unknown 仅表示“本分析无法证明”，从不判错。

### 独立检查器为什么是“证明”而不是“采样”

`checker.py` 不导入 `interval/state/semantics/analyzer`，用裸
`(lo,hi)` 端点和独立的转移公式重算。本题子集（赋常量/复制/加常量 +
`x<=c`/`x>=c` 过滤）中，每个变量在块内始终是入口变量的仿射函数，
端点像由 `min/max/平移/截断` 公式**精确**给出；包含性是整数端点的
符号比较，对无穷状态成立，**不枚举任何具体取值**。检查通过意味着
声称的不变量构成局部归纳证书（入口包含 + 归纳条件 + 块条件）。
源码中有静态测试保证检查器不含 `random/sample/fuzz` 等采样设施。

## 误差口径（README 明确）

* 本库**不使用任何浮点运算**：常量与端点都是 Python 任意精度整数
  （`int`），无穷用 `null/None` 表示。因此**没有舍入误差、没有溢出、
  没有容差（tolerance）**，边界按精确整数比较。
* 唯一的“误差”是抽象解释固有的**过近似**（非关系域丢失变量间相关性，
  如 `x,y` 同步增长时无法由 `x` 的界推出 `y` 的界）。这是精度问题，
  以 `unknown` 如实呈现，不用宽限/tolerance 掩盖。
* 本实现只覆盖本题声明的语句/条件子集，**不宣称兼容任何完整行业标准
  抽象解释框架或其他数值域**（如八边形、多面体等均未实现）。

## 已知限制

1. 非关系区间域：无法表达变量间关系（相关性丢失时给 unknown）。
2. 语句子集仅含赋常量/复制/加常量与 `x<=c`、`x>=c`；没有乘法、
   别名、数组、过程调用。
3. narrowing 是每轮全局同步的最多 8 轮；个别需要更多下降轮的程序
   可能仍留 unknown（可靠但不精确）。
4. 真/假边目标相同的分支按两路过滤结果的凸包合并。
5. 从 entry 不可达的块恒为 bottom（不分析不可达代码）。

## 目录

```
interval_ai/          库
  cfg.py              公开数据结构 + 构造期严格校验
  interval.py         区间域（含 widen/narrow）
  state.py            抽象状态（变量→区间，bottom=不可达）
  semantics.py        局部抽象转移（语句/块/条件过滤）
  analyzer.py         DFS 循环识别 + 上升/下降不动点
  checker.py          独立局部转移包含性检查器（符号证明）
  reference.py        独立具体执行参考（测试对照用）
  errors.py           错误层级与语义
tests/                unittest 套件（夹具在 tests/programs.py 内确定性构造）
demo.py               固定输入演示
```
