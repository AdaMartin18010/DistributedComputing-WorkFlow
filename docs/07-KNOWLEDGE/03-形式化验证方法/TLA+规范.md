# TLA+ 规范

## 概述

**TLA+（Temporal Logic of Actions）** 是一种用于指定和验证并发和分布式系统的形式化规约语言。它由Leslie Lamport在1990年代开发，结合了时序逻辑（Temporal Logic）和动作（Actions）的概念，用于描述系统的行为。

### 核心思想

TLA+基于三个核心思想：

1. **状态和动作**：系统由状态和状态转换（动作）组成
   - **状态（State）**：系统在某个时刻的完整快照
   - **动作（Action）**：描述状态如何从一个状态转换到另一个状态
   - **行为（Behavior）**：状态的无限序列，表示系统的执行轨迹

2. **时序逻辑**：使用时序逻辑描述系统的时间相关性质
   - **不变式（Invariant）**：在所有状态下都成立的性质
   - **安全性（Safety）**：坏事永远不会发生
   - **活性（Liveness）**：好事最终会发生

3. **抽象和细化**：支持从抽象规约到具体实现的逐步细化

### 应用领域

- **并发系统**：多线程程序、分布式算法、并发数据结构
- **分布式系统**：共识算法（Paxos、Raft）、复制协议、分布式事务
- **硬件设计**：处理器设计、缓存一致性协议、总线协议
- **协议设计**：网络协议、安全协议、通信协议

---

## 形式化定义和语义

### 数学定义

#### 定义1：状态（State）

状态是系统在某个时刻的完整快照，包含所有变量的值。

$$ \text{State} = \{v_1: V_1, v_2: V_2, ..., v_n: V_n\} $$

其中 $v_i$ 是变量名，$V_i$ 是变量的值域。

#### 定义2：动作（Action）

动作是描述状态转换的公式，包含当前状态（未加prime）和下一状态（加prime）的变量。

$$ A(s, s') = \text{Precondition}(s) \land \text{Postcondition}(s, s') $$

其中 $s$ 是当前状态，$s'$ 是下一状态。

#### 定义3：TLA公式

TLA公式是时序逻辑公式，用于描述系统的行为。

$$ \phi ::= P | [A]_v | \Box \phi | \Diamond \phi | \phi \land \psi | \phi \lor \psi | \neg \phi $$

其中：

- $P$ 是状态谓词
- $[A]_v$ 是动作公式（$A$ 是动作，$v$ 是变量列表）
- $\Box \phi$ 表示"总是 $\phi$"
- $\Diamond \phi$ 表示"最终 $\phi$"

#### 定义4：系统规约

系统规约由初始状态谓词、动作公式和时序性质组成。

$$ \text{Spec} = \text{Init} \land \Box[\text{Next}]_v \land \text{Liveness} $$

其中：

- $\text{Init}$ 是初始状态谓词
- $\text{Next}$ 是下一状态动作
- $v$ 是变量列表
- $\text{Liveness}$ 是活性性质

### 语义定义

#### 语义1：状态函数语义

状态函数在状态 $s$ 下的值由状态中变量的值决定。

$$ [f]_s = f(s(v_1), s(v_2), ..., s(v_n)) $$

#### 语义2：动作语义

动作 $A$ 在状态对 $(s, t)$ 下为真，当且仅当从状态 $s$ 到状态 $t$ 的转换满足 $A$。

$$ [A]_{(s,t)} = A(s, t) $$

#### 语义3：时序公式语义

时序公式在行为 $\sigma$ 下的真值由行为的性质决定。

$$ [\Box P]_\sigma = \forall i \in \mathbb{N}: [P]_{\sigma_i} $$

$$ [\Diamond P]_\sigma = \exists i \in \mathbb{N}: [P]_{\sigma_i} $$

---

## 语法和示例

### 基本语法要素

#### 1. 模块声明

```tla
MODULE 模块名称
```

#### 2. 扩展模块

```tla
EXTENDS Naturals, Sequences, FiniteSets
```

#### 3. 变量声明

```tla
VARIABLES x, y, z
```

#### 4. 常量声明

```tla
CONSTANTS N, MaxVal
```

#### 5. 初始状态

```tla
Init == x = 0 /\ y = 0
```

#### 6. 动作定义

```tla
Increment == x' = x + 1 /\ UNCHANGED y
```

#### 7. 下一状态动作

```tla
Next == Increment \/ Decrement
```

#### 8. 系统规约

```tla
Spec == Init /\ [][Next]_<<x, y>> /\ WF_x(Increment)
```

### 时序运算符

| 运算符 | 含义 | 示例 |
|--------|------|------|
| `[]` | 总是（Globally） | `[]P` 表示 P 总是成立 |
| `<>` | 最终（Eventually） | `<>P` 表示 P 最终会成立 |
| `~>` | 导致（Leads-to） | `P ~> Q` 表示如果 P 成立，则 Q 最终会成立 |
| `[]<>` | 无限经常（Infinitely often） | `[]<>P` 表示 P 无限次成立 |

### 完整示例：简单计数器

```tla
MODULE Counter

EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES count

TypeInvariant == count \in 0..MaxValue

Init == count = 0

Increment ==
    /\ count < MaxValue
    /\ count' = count + 1
    /\ UNCHANGED <<>>

Reset ==
    /\ count = MaxValue
    /\ count' = 0
    /\ UNCHANGED <<>>

Next == Increment \/ Reset

Spec == Init /\ [][Next]_count /\ WF_count(Next)

SafetyProperty == []TypeInvariant

LivenessProperty == count = MaxValue ~> count = 0

THEOREM Spec => SafetyProperty /\ LivenessProperty
```

---

## PlusCal 算法语言

### 简介

PlusCal是一种更容易使用的算法语言，可编译为TLA+。它使用类似伪代码的语法，降低了TLA+的学习曲线。

### 基本结构

```tla
MODULE Algorithm

EXTENDS Integers, TLC

(* --algorithm AlgorithmName
variables
    x = 0,
    y = 1;

begin
    Start:
        x := x + 1;
        y := y * 2;

    Next:
        while x < 10 do
            x := x + 1;
        end while;
end algorithm *)
```

### PlusCal 示例：互斥算法

```tla
MODULE Mutex

EXTENDS Integers, TLC

CONSTANTS N

(* --algorithm Mutex
variables
    flag = [i \in 1..N |-> FALSE],
    turn = 1;

process Proc \in 1..N
variable j;
begin
    L1: flag[self] := TRUE;
    L2: while turn # self do
            if ~flag[turn] then
                turn := self;
            end if;
        end while;
    CS: (* 临界区 *)
        skip;
    L3: flag[self] := FALSE;
end process;

end algorithm *)
```

---

## 工具使用指南

### TLC 模型检验器

**TLC（TLA+ Model Checker）** 是TLA+的模型检验器，用于验证TLA+规约。

#### 安装

1. 下载 TLA+ Toolbox：<https://github.com/tlaplus/tlaplus/releases>
2. 解压并运行

#### 基本使用流程

1. **编写规约**：创建 `.tla` 文件
2. **创建模型**：在Toolbox中创建新模型
3. **配置模型**：
   - 设置常量值
   - 指定初始状态
   - 添加不变式
   - 添加活性性质
4. **运行检验**：点击 "Model Checking" 运行
5. **查看结果**：检查是否发现错误

#### 常用配置

```tla
CONSTANTS
    N = 3
    MaxValue = 10

INIT Init
NEXT Next

INVARIANTS
    TypeInvariant
    SafetyProperty

PROPERTIES
    LivenessProperty
```

### TLAPS 定理证明系统

**TLAPS（TLA+ Proof System）** 是TLA+的定理证明系统，用于形式化证明TLA+规约的性质。

#### 基本证明结构

```tla
THEOREM Spec => SafetyProperty
<1>1. Init => SafetyProperty
    BY DEF Init, SafetyProperty
<1>2. SafetyProperty /\ [Next]_vars => SafetyProperty'
    BY DEF SafetyProperty, Next, vars
<1>3. QED
    BY <1>1, <1>2, PTL DEF Spec
```

### Apalache 符号模型检验器

**Apalache** 是基于SMT求解器的TLA+模型检验器，适用于处理参数化系统。

#### 使用方法

```bash
apalache-mc check --init=Init --next=Next --inv=SafetyProperty Spec.tla
```

---

## 性质与定理

### 基本性质

#### 性质1：不变式保持性

**表述**：如果 $P$ 是初始状态，且所有动作都保持 $P$，则 $P$ 是不变式。

$$ \text{Init} \Rightarrow P \land \Box[P \Rightarrow P'] \Rightarrow \Box P $$

#### 性质2：安全性性质

**定义**：安全性性质表示"坏事永远不会发生"。

$$ \Box P $$

其中 $P$ 是状态谓词。

#### 性质3：活性性质

**定义**：活性性质表示"好事最终会发生"。

$$ \Diamond P = \exists i \in \mathbb{N}: P(s_i) $$

### 重要定理

#### 定理1：规约蕴含定理

**表述**：如果规约 $Spec_1$ 蕴含规约 $Spec_2$，则 $Spec_1$ 的所有实现都满足 $Spec_2$。

$$ Spec_1 \Rightarrow Spec_2 $$

#### 定理2：组合定理

**表述**：TLA+规约可以组合，组合后的规约仍然是有效的TLA+规约。

$$ \text{Composable}(\text{Spec}_1, \text{Spec}_2) \implies \text{Valid}(\text{Spec}_1 \land \text{Spec}_2) $$

---

## 相关文档关联

### 内部链接

| 文档 | 描述 |
|------|------|
| [时序逻辑](时序逻辑.md) | TLA+使用的时序逻辑基础（LTL、CTL） |
| [模型检验](模型检验.md) | TLC模型检验器的原理和算法 |
| [定理证明](定理证明.md) | TLAPS定理证明系统的理论基础 |
| [Petri网分析](Petri网分析.md) | 与TLA+并发的另一种建模方法 |

### 外部资源

| 资源 | 链接 |
|------|------|
| TLA+ 官网 | <https://lamport.azurewebsites.net/tla/tla.html> |
| TLA+ GitHub | <https://github.com/tlaplus/tlaplus> |
| Learn TLA+ | <https://www.learntla.com/> |
| Leslie Lamport's TLA+ Page | <https://lamport.azurewebsites.net/tla/tla.html> |

---

## 参考资源

### 经典教材

1. **Lamport, L. (2002)**. "Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers". Addison-Wesley.
   - TLA+的标准参考书

2. **Lamport, L. (1994)**. "The Temporal Logic of Actions". ACM Transactions on Programming Languages and Systems (TOPLAS).
   - TLA的理论基础论文

### 在线教程

1. **Learn TLA+** (<https://www.learntla.com/>)
   - 互动式TLA+教程

2. **TLA+ Video Course** by Leslie Lamport
   - YouTube上的TLA+视频课程

### 工业案例

1. **Amazon DynamoDB** - 使用TLA+验证分布式数据库
2. **Microsoft Azure** - 使用TLA+验证云服务
3. **Coinbase** - 使用TLA+验证支付系统
4. **MongoDB** - 使用TLA+验证复制协议

---

## 总结

TLA+是一种强大的形式化规约语言，特别适用于并发和分布式系统的验证。通过TLC模型检验器和TLAPS定理证明系统，TLA+提供了从自动验证到形式化证明的完整工具链。PlusCal算法语言进一步降低了TLA+的使用门槛，使其更易于学习和应用。

**关键优势**：

- 形式化语义，精确描述系统行为
- 强大的工具支持（TLC、TLAPS、PlusCal）
- 工业界广泛验证（Amazon、Microsoft等）
- 适合系统级规约和验证
