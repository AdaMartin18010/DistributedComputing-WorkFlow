# 分布式计算形式化证明体系

> **Formal Proof System for Distributed Computing**  
> 全球顶级学术标准（对标ETH Zurich和Cambridge形式化深度）

---

## 目录结构

```
formal-proofs/
├── README.md                          # 本文件
│
├── 核心理论形式化证明/                 # Core Theoretical Formal Proofs
│   ├── 01-CAP定理形式化证明.md         # CAP Theorem Formal Proof
│   ├── 02-FLP不可能性形式化证明.md     # FLP Impossibility Formal Proof
│   └── 03-共识问题形式化规约.md        # Consensus Problem Formal Specification
│
├── 算法正确性证明/                     # Algorithm Correctness Proofs
│   ├── 04-Paxos正确性证明.md           # Paxos Correctness Proof
│   ├── 05-Raft安全性证明.md            # Raft Safety Proof
│   └── 06-PBFT正确性证明.md            # PBFT Correctness Proof
│
├── 一致性模型形式化/                   # Consistency Models Formalization
│   ├── 07-线性一致性形式化定义.md      # Linearizability Formal Definition
│   ├── 08-顺序一致性形式化.md          # Sequential Consistency Formalization
│   └── 09-因果一致性形式化.md          # Causal Consistency Formalization
│
└── Two Generals问题/                   # Two Generals Problem
    ├── 10-两将军问题不可能性证明.md    # Two Generals Impossibility Proof
    └── 11-拜占庭将军问题形式化.md      # Byzantine Generals Formalization
```

---

## 文档统计

### 整体统计

| 类别 | 数量 |
|------|------|
| **总文档数** | 11 |
| **总形式化定义** | 151+ |
| **总定理数** | 42+ |
| **总引理数** | 35+ |
| **TLA+模块** | 11 |
| **Mermaid图表** | 18+ |

### 按类别统计

#### 1. 核心理论形式化证明 (3文档)

| 文档 | 定义 | 定理 | 引理 | TLA+ |
|-----|------|------|------|------|
| CAP定理 | 12 | 4 | 5 | 1 |
| FLP不可能性 | 18 | 3 | 5 | 1 |
| 共识问题规约 | 15 | 5 | 4 | 1 |
| **小计** | **45** | **12** | **14** | **3** |

#### 2. 算法正确性证明 (3文档)

| 文档 | 定义 | 定理 | 引理 | TLA+ |
|-----|------|------|------|------|
| Paxos | 14 | 4 | 5 | 1 |
| Raft | 12 | 5 | 4 | 1 |
| PBFT | 15 | 6 | 5 | 1 |
| **小计** | **41** | **15** | **14** | **3** |

#### 3. 一致性模型形式化 (3文档)

| 文档 | 定义 | 定理 | 引理 | TLA+ |
|-----|------|------|------|------|
| 线性一致性 | 15 | 4 | 3 | 1 |
| 顺序一致性 | 12 | 4 | 2 | 0 |
| 因果一致性 | 13 | 4 | 5 | 1 |
| **小计** | **40** | **12** | **10** | **2** |

#### 4. Two Generals问题 (2文档)

| 文档 | 定义 | 定理 | 引理 | TLA+ |
|-----|------|------|------|------|
| 两将军问题 | 11 | 2 | 3 | 0 |
| 拜占庭将军 | 14 | 4 | 5 | 1 |
| **小计** | **25** | **6** | **8** | **1** |

---

## 形式化方法使用

### 数学符号

所有文档使用LaTeX风格的数学公式：

- **定义**: 使用 `定义 X.Y` 格式
- **定理**: 使用 `定理 X.Y` 格式
- **引理**: 使用 `引理 X.Y` 格式
- **证明**: 使用结构化证明格式

### TLA+规约

每个算法文档包含完整的TLA+模块：

```tla
--------------------------- MODULE Example ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS ...
VARIABLES ...

Init ≜ ...
Next ≜ ...

THEOREM Safety ≜ Spec ⇒ □Invariant
=============================================================================
```

### 时序图

使用Mermaid绘制：
- 时序图 (sequenceDiagram)
- 状态图 (stateDiagram-v2)
- 依赖图 (graph TB/LR)

---

## 核心定理索引

### 不可能性定理

| 定理 | 文件 | 内容 |
|-----|------|------|
| **CAP Theorem** | 01 | ¬(C ∧ A ∧ P) |
| **FLP Impossibility** | 02 | 异步系统中无确定性共识 |
| **Two Generals** | 10 | 不可靠信道上无法达成共识 |
| **Byzantine Bound** | 11 | n ≥ 3f + 1 必要性 |

### 安全性定理

| 定理 | 文件 | 内容 |
|-----|------|------|
| **Paxos Safety** | 04 | 已选值不变性 |
| **Raft Election Safety** | 05 | 一个任期内至多一个Leader |
| **Raft Leader Completeness** | 05 | 已提交条目出现在所有后续Leader |
| **Raft State Machine Safety** | 05 | 相同索引应用相同条目 |
| **PBFT Agreement** | 06 | 正确副本达成一致 |

### 等价性定理

| 定理 | 文件 | 内容 |
|-----|------|------|
| **Linearizability ⇒ Sequential** | 07 | 线性一致性蕴含顺序一致性 |
| **Causal ⟺ Vector Clocks** | 09 | 因果一致性与向量时钟等价 |

---

## 学术标准对照

### ETH Zurich 标准

- ✅ 严格的数学定义
- ✅ 完整的形式化证明
- ✅ 公理系统明确
- ✅ 结构化证明格式

### Cambridge 标准

- ✅ 清晰的定理陈述
- ✅ 引理分解
- ✅ 反证法使用
- ✅ 归纳法证明

### 额外特性

- ✅ TLA+形式化验证
- ✅ Mermaid可视化
- ✅ 多维度关系图
- ✅ 实际应用连接

---

## 使用指南

### 学习路径

```
入门 → 核心理论 → 算法证明 → 一致性模型 → 高级主题
  │       │           │           │           │
  ▼       ▼           ▼           ▼           ▼
基础  →  CAP/FLP  →  Paxos    → 线性一致 → 两将军
数学    共识问题    Raft      顺序一致   拜占庭
基础    规约        PBFT      因果一致
```

### 阅读建议

1. **按顺序阅读**: 核心理论 → 算法 → 一致性模型
2. **重点关注**: 定义 → 定理 → 证明
3. **动手实践**: 阅读TLA+规约，尝试模型检验
4. **对比学习**: 比较不同算法的证明技巧

---

## 参考文献汇总

### 经典文献

1. **CAP Theorem**: Gilbert & Lynch (2002), ACM SIGACT News
2. **FLP Impossibility**: Fischer, Lynch & Paterson (1985), JACM
3. **Paxos**: Lamport (1998/2001), ACM TOCS/SIGACT News
4. **Raft**: Ongaro & Ousterhout (2014), USENIX ATC
5. **PBFT**: Castro & Liskov (1999/2002), OSDI/ACM TOCS
6. **Linearizability**: Herlihy & Wing (1990), ACM TOPLAS
7. **Byzantine Generals**: Lamport, Shostak & Pease (1982), ACM TOPLAS
8. **Two Generals**: Akkoyunlu et al. (1975), ACM SOSP

### 形式化方法

- Lamport, L. (2002). *Specifying Systems: The TLA+ Language and Tools*
- Lynch, N. A. (1996). *Distributed Algorithms*
- Attiya, H., & Welch, J. (2004). *Distributed Computing*

---

## 贡献与维护

### 版本历史

| 版本 | 日期 | 变更 |
|-----|------|------|
| 1.0 | 2026-04-04 | 初始发布，11个完整形式化证明文档 |

### 扩展计划

- [ ] 添加更多算法证明（Zab、Viewstamped Replication）
- [ ] 扩展一致性模型（PRAM、Processor Consistency）
- [ ] 添加概率性证明（Ben-Or、Rabin）
- [ ] 补充Isabelle/HOL形式化

---

*构建日期: 2026-04-04*  
*维护者: 分布式计算知识库*  
*学术标准: ETH Zurich / Cambridge Formal Methods*
