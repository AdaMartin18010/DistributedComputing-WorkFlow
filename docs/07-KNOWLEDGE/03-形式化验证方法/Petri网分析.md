# Petri 网分析

## 概述

**Petri网（Petri Net）** 是一种用于建模和分析并发系统的图形化数学工具。它由Carl Adam Petri在1962年提出，是并发系统理论的基础。

### 核心思想

Petri网基于三个核心思想：

1. **位置和转换**：
   - **位置（Place）**：表示资源或状态，用圆圈○表示
   - **转换（Transition）**：表示事件或动作，用矩形□表示
   - **弧（Arc）**：连接位置和转换，表示依赖关系
   - **标记（Token）**：位置中的标记，表示资源数量

2. **并发执行**：
   - 多个转换可以同时触发（如果满足条件）
   - 位置可以包含多个标记
   - 支持真正的并发执行

3. **状态转换**：
   - 转换触发时，消耗输入位置的标记
   - 产生输出位置的标记
   - 系统的状态由标记分布决定

### 应用领域

- **工作流建模**：业务流程建模、工作流验证、流程优化
- **并发系统**：并发程序建模、死锁检测、可达性分析
- **硬件设计**：电路设计、协议验证、系统建模
- **制造系统**：生产流程建模、资源调度、性能分析

---

## 形式化定义和语义

### 数学定义

#### 定义1：Petri网

Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限位置集合
- $T$ 是有限转换集合，$P \cap T = \emptyset$
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系
- $M_0: P \to \mathbb{N}$ 是初始标记

#### 定义2：标记（Marking）

标记是位置到自然数的映射，表示每个位置的标记数量。

$$ M: P \to \mathbb{N} $$

#### 定义3：转换触发（Transition Firing）

转换 $t$ 在标记 $M$ 下可触发，当且仅当所有输入位置都有足够的标记。

**触发条件**：

$$ M[t\rangle \iff \forall p \in \bullet t: M(p) \ge W(p, t) $$

其中：

- $\bullet t = \{p \in P: (p, t) \in F\}$ 是 $t$ 的输入位置集合
- $W(p, t)$ 是弧 $(p, t)$ 的权重（默认为1）

**标记变化**：

如果 $M[t\rangle M'$，则：

$$ M'(p) = M(p) - W(p, t) + W(t, p) $$

### 工作流网（Workflow Net）

工作流网是Petri网的特殊形式，用于工作流建模：

**定义**：工作流网是Petri网 $N = (P, T, F)$，满足：

1. 有一个输入位置 $i$，$\bullet i = \emptyset$
2. 有一个输出位置 $o$，$o \bullet = \emptyset$
3. 每个节点都在从 $i$ 到 $o$ 的路径上

**正确性（Soundness）**：工作流网是正确的，当且仅当：

1. **正确终止**：从初始标记，最终可以到达只包含输出位置标记的标记
2. **无死锁**：不存在死锁状态
3. **无多余标记**：正确终止时，所有位置（除输出位置）都没有标记

---

## 性质分析

### 有界性（Boundedness）

**表述**：Petri网是有界的，当且仅当所有位置的标记数量都有上界。

$$ \exists k \in \mathbb{N}: \forall M \in R(M_0), \forall p \in P: M(p) \le k $$

其中 $R(M_0)$ 是从初始标记 $M_0$ 可达的标记集合。

**1-有界性**：如果 $k = 1$，则Petri网是安全的（safe）

### 活性（Liveness）

**表述**：转换 $t$ 是活的，当且仅当从任意可达标记，都存在一条路径使得 $t$ 可以触发。

$$ \forall M \in R(M_0): \exists M' \in R(M): M'[t\rangle $$

**活性级别**：

- **L0-活性**：$t$ 可能永远不会触发
- **L1-活性**：$t$ 至少可以触发一次
- **L2-活性**：对于任意 $k$，$t$ 至少可以触发 $k$ 次
- **L3-活性**：$t$ 可以无限次触发
- **L4-活性**（活性）：从任意可达标记，都可以触发 $t$

### 可达性（Reachability）

**表述**：标记 $M$ 从 $M_0$ 可达，如果存在转换序列 $\sigma$ 使得 $M_0[\sigma\rangle M$。

**可达性问题**：对于Petri网 $N$ 和标记 $M$，可达性问题 $M_0 \to^* M$ 是可判定的。

### 死锁检测

**定理**：Petri网存在死锁，当且仅当存在一个标记，使得所有转换都不可触发。

$$ \exists M \in R(M_0): \forall t \in T: \neg M[t\rangle $$

---

## 分析方法

### 可达性分析算法

```
ReachabilityAnalysis(N, M_0):
输入：Petri网 N = (P, T, F, M_0)，初始标记 M_0
输出：可达标记集合 R(M_0)

1. R ← {M_0}
2. WorkList ← {M_0}
3. while WorkList ≠ ∅:
   a. M ← WorkList.pop()
   b. for each t ∈ T such that M[t⟩:
      M' ← fire(M, t)
      if M' ∉ R:
         R ← R ∪ {M'}
         WorkList ← WorkList ∪ {M'}
4. return R
```

**复杂度**：

- 时间复杂度：$O(|M| \times |T|)$
- 空间复杂度：$O(|M|)$
- 其中 $|M|$ 是可达标记数，$|T|$ 是转换数

### 覆盖图（Coverability Graph）

**问题**：对于无界Petri网，可达标记集合是无限的。

**解决方案**：使用覆盖图，将无限状态空间抽象为有限图。

**定义**：标记 $M_1$ 覆盖标记 $M_2$，如果：

$$ M_1 \ge M_2 \iff \forall p \in P: M_1(p) \ge M_2(p) $$

**ω符号**：表示"任意大的值"，用于表示无界增长。

### 状态空间爆炸问题

**问题**：可达标记数可能是指数级的。

$$ |M| = O(k^{|P|}) $$

其中 $k$ 是每个位置的最大标记数。

**缓解方法**：

1. **状态压缩**：使用压缩技术减少存储需求
2. **对称性约简**：利用系统对称性减少状态空间
3. **抽象**：使用抽象技术减少状态空间
4. **符号模型检验**：使用BDD等符号技术
5. **部分序约简**：利用部分序关系减少状态空间

---

## 工具使用指南

### CPN Tools

**CPN Tools** 是着色Petri网（Colored Petri Nets）的建模和验证工具。

#### 基本使用

1. **创建模型**：
   - 创建位置（Place）
   - 创建转换（Transition）
   - 创建弧（Arc）
   - 定义标记（Token）

2. **定义颜色集**：

   ```
   colset INT = int;
   colset STRING = string;
   colset PRODUCT = product INT * STRING;
   ```

3. **运行仿真**：
   - 交互式仿真
   - 自动仿真

4. **状态空间分析**：
   - 生成状态空间
   - 分析可达性
   - 验证性质

### PIPE (Platform Independent Petri Net Editor)

**PIPE** 是一个开源的Petri网编辑器，支持基本Petri网和分析功能。

#### 功能

- 创建和编辑Petri网
- 运行仿真
- 分析可达性
- 检测死锁
- 验证有界性

### Python 实现示例

```python
class PetriNet:
    def __init__(self, places, transitions, flow_relation, initial_marking):
        self.places = places
        self.transitions = transitions
        self.flow_relation = flow_relation
        self.marking = initial_marking

    def is_enabled(self, transition):
        """检查转换是否可以触发"""
        for place in self.input_places(transition):
            if self.marking[place] < self.weight(place, transition):
                return False
        return True

    def fire(self, transition):
        """触发转换，更新标记"""
        if not self.is_enabled(transition):
            return False

        # 消耗输入位置的标记
        for place in self.input_places(transition):
            self.marking[place] -= self.weight(place, transition)

        # 产生输出位置的标记
        for place in self.output_places(transition):
            self.marking[place] += self.weight(transition, place)

        return True

    def reachability_analysis(self):
        """可达性分析"""
        reachable = {self.marking.copy()}
        worklist = [self.marking.copy()]

        while worklist:
            marking = worklist.pop()
            for transition in self.transitions:
                if self.is_enabled(transition):
                    new_marking = marking.copy()
                    # 触发转换，更新new_marking
                    # ...
                    if new_marking not in reachable:
                        reachable.add(new_marking)
                        worklist.append(new_marking)

        return reachable
```

---

## 相关文档关联

### 内部链接

| 文档 | 描述 |
|------|------|
| [TLA+规范](TLA+规范.md) | 与Petri网并发的形式化建模方法 |
| [时序逻辑](时序逻辑.md) | Petri网性质表达的逻辑基础 |
| [模型检验](模型检验.md) | Petri网分析使用的验证技术 |
| [定理证明](定理证明.md) | Petri网性质的形式化证明方法 |

### 外部资源

| 资源 | 链接 |
|------|------|
| Petri Nets World | <http://www.informatik.uni-hamburg.de/TGI/PetriNets/> |
| CPN Tools | <https://cpntools.org/> |
| PIPE | <https://pipe2.sourceforge.net/> |

---

## 参考资源

### 经典教材

1. **Petri, C. A. (1962)**. "Kommunikation mit Automaten". 德国波恩大学博士论文。
   - Petri网的原始论文

2. **Reisig, W. (2013)**. "Understanding Petri Nets: Modeling Techniques, Analysis Methods, Case Studies". Springer.
   - Petri网现代教材

3. **van der Aalst, W. M. P. (1998)**. "The Application of Petri Nets to Workflow Management".
   - 工作流网的开创性论文

### 分析算法

1. **Murata, T. (1989)**. "Petri Nets: Properties, Analysis and Applications". Proceedings of the IEEE.
   - Petri网分析的综合综述

2. **Esparza, J., & Nielsen, M. (1994)**. "Decidability Issues for Petri Nets". Petri Net Newsletter.
   - Petri网可判定性问题

---

## 总结

Petri网是一种强大的并发系统建模和分析工具，具有直观的图形表示和严格的数学基础。通过可达性分析、有界性分析和活性分析，可以验证系统的各种性质。虽然状态空间爆炸是一个挑战，但通过各种优化技术，Petri网仍然是一种实用的形式化方法。

**关键优势**：

- 直观的图形化建模
- 严格的数学基础
- 丰富的分析技术
- 广泛的应用领域

**主要挑战**：

- 状态空间爆炸
- 复杂系统的可扩展性
- 实时性质的表达
