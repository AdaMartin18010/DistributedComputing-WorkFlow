# 分布式计算知识图谱 Schema

## 概述

本Schema定义了分布式计算知识图谱的本体（Ontology），用于描述分布式计算领域中的概念、算法、系统、论文和人物及其之间的关系。

**命名空间**: `http://distributedcomputing.org/ontology#`
**前缀**: `:`

## 类（Classes）

### 1. Concept（概念）

所有概念的基本类。

| 属性 | 类型 | 说明 |
|------|------|------|
| id | URI | 唯一标识符 |
| name | xsd:string | 中文名称 |
| nameEn | xsd:string | 英文名称 |
| definition | xsd:string | 定义描述 |
| category | :Category | 类别枚举 |
| tags | xsd:string[] | 标签列表 |
| difficulty | xsd:string | 难度级别（初级/中级/高级） |
| createdAt | xsd:dateTime | 创建时间 |
| updatedAt | xsd:dateTime | 更新时间 |

#### 类别枚举（Category）

- `Theory` - 理论基础
- `Algorithm` - 算法
- `System` - 系统
- `Pattern` - 设计模式
- `Tool` - 工具
- `Protocol` - 协议
- `Architecture` - 架构

---

### 2. Algorithm（算法）

继承自: `Concept`

| 属性 | 类型 | 说明 |
|------|------|------|
| complexity | xsd:string | 时间/空间复杂度，如 "O(n)" |
| complexityType | xsd:string | 复杂度类型：时间/空间/通信 |
| input | xsd:string | 输入描述 |
| output | xsd:string | 输出描述 |
| pseudoCode | xsd:string | 伪代码 |
| faultTolerance | xsd:string | 容错能力描述 |
| messageComplexity | xsd:string | 消息复杂度 |
| implementations | :System[] | 实现该算法的系统列表 |

---

### 3. System（系统）

继承自: `Concept`

| 属性 | 类型 | 说明 |
|------|------|------|
| systemType | :SystemType | 系统类型枚举 |
| programmingLanguage | xsd:string | 编程语言 |
| license | xsd:string | 开源协议 |
| github | xsd:anyURI | GitHub仓库地址 |
| paper | xsd:anyURI | 相关论文链接 |
| documentation | xsd:anyURI | 官方文档链接 |
| created | xsd:integer | 创建年份 |
| isActive | xsd:boolean | 是否活跃维护 |
| usedBy | :System[] | 被哪些系统使用 |

#### 系统类型枚举（SystemType）

- `Database` - 数据库
- `Framework` - 框架
- `Middleware` - 中间件
- `Platform` - 平台
- `KeyValueStore` - 键值存储
- `MessageQueue` - 消息队列
- `Cache` - 缓存系统
- `FileSystem` - 文件系统
- `Orchestrator` - 编排系统
- `ServiceMesh` - 服务网格

---

### 4. Paper（论文）

学术论文类。

| 属性 | 类型 | 说明 |
|------|------|------|
| title | xsd:string | 论文标题 |
| authors | xsd:string[] | 作者列表 |
| year | xsd:integer | 发表年份 |
| venue | xsd:string | 发表会议/期刊 |
| doi | xsd:string | DOI标识符 |
| abstract | xsd:string | 摘要 |
| citations | xsd:integer | 引用次数 |
| pdfUrl | xsd:anyURI | PDF链接 |

---

### 5. Person（人物）

研究者、工程师等人物。

| 属性 | 类型 | 说明 |
|------|------|------|
| name | xsd:string | 姓名 |
| affiliation | xsd:string | 所属机构 |
| email | xsd:string | 邮箱 |
| homepage | xsd:anyURI | 个人主页 |
| orcid | xsd:string | ORCID标识符 |

---

### 6. Theorem（定理）

理论结果。

| 属性 | 类型 | 说明 |
|------|------|------|
| statement | xsd:string | 定理陈述 |
| assumptions | xsd:string[] | 前提假设 |
| implications | xsd:string[] | 推论和影响 |

---

### 7. Protocol（协议）

通信或共识协议。

| 属性 | 类型 | 说明 |
|------|------|------|
| layer | xsd:string | 协议层次 |
| messageTypes | xsd:string[] | 消息类型 |
| safetyProperties | xsd:string[] | 安全属性 |
| livenessProperties | xsd:string[] | 活性属性 |

---

### 8. Pattern（模式）

设计模式或架构模式。

| 属性 | 类型 | 说明 |
|------|------|------|
| context | xsd:string | 适用场景 |
| problem | xsd:string | 解决的问题 |
| solution | xsd:string | 解决方案 |
| consequences | xsd:string[] | 优缺点 |

---

## 关系（Properties）

### 对象属性（Object Properties）

#### 1. isA（是一种）

- **定义域**: `:Concept`
- **值域**: `:Concept`
- **特性**: 传递性、自反性
- **逆属性**: `hasSubtype`
- **说明**: 概念之间的层次关系

**示例**: `Raft isA ConsensusAlgorithm`

---

#### 2. hasPart（包含部分）

- **定义域**: `:Concept`
- **值域**: `:Concept`
- **特性**: 传递性
- **逆属性**: `partOf`
- **说明**: 整体-部分关系

**示例**: `Raft hasPart LeaderElection`

---

#### 3. dependsOn（依赖）

- **定义域**: `:Concept | :System`
- **值域**: `:Concept | :System`
- **特性**: 传递性
- **逆属性**: `requiredBy`
- **说明**: 依赖关系

**示例**: `etcd dependsOn Raft`

---

#### 4. implements（实现）

- **定义域**: `:System`
- **值域**: `:Algorithm | :Protocol`
- **逆属性**: `implementedBy`
- **说明**: 系统实现算法或协议

**示例**: `etcd implements Raft`

---

#### 5. uses（使用）

- **定义域**: `:System | :Algorithm`
- **值域**: `:Concept | :Tool | :Protocol`
- **逆属性**: `usedBy`
- **说明**: 使用关系

**示例**: `Kafka uses ZooKeeper`

---

#### 6. proves（证明）

- **定义域**: `:Paper`
- **值域**: `:Theorem`
- **逆属性**: `provedBy`
- **说明**: 论文证明定理

**示例**: `CAPProofPaper proves CAPTheorem`

---

#### 7. proposes（提出）

- **定义域**: `:Person`
- **值域**: `:Concept | :Algorithm | :Protocol`
- **逆属性**: `proposedBy`
- **说明**: 提出概念或算法

**示例**: `LeslieLamport proposes Paxos`

---

#### 8. extends（扩展）

- **定义域**: `:Algorithm | :System`
- **值域**: `:Algorithm | :System`
- **逆属性**: `extendedBy`
- **说明**: 扩展或改进

**示例**: `MultiPaxos extends Paxos`

---

#### 9. conflictsWith（冲突）

- **定义域**: `:Concept`
- **值域**: `:Concept`
- **特性**: 对称性
- **说明**: 互斥或冲突关系

**示例**: `Consistency conflictsWith Availability (在分区时)`

---

#### 10. relatedTo（相关）

- **定义域**: `:Concept`
- **值域**: `:Concept`
- **特性**: 对称性、自反性
- **说明**: 一般相关性

**示例**: `CAPTheorem relatedTo PACELC`

---

#### 11. precedes（先于）

- **定义域**: `:Concept | :Paper`
- **值域**: `:Concept | :Paper`
- **特性**: 传递性
- **逆属性**: `succeeds`
- **说明**: 时间或逻辑上的先后

**示例**: `Paxos precedes Raft`

---

#### 12. solves（解决）

- **定义域**: `:Algorithm | :Pattern | :Protocol`
- **值域**: `:Concept`
- **逆属性**: `solvedBy`
- **说明**: 解决问题

**示例**: `Raft solves ConsensusProblem`

---

#### 13. authoredBy（作者）

- **定义域**: `:Paper`
- **值域**: `:Person`
- **逆属性**: `authorOf`
- **说明**: 论文作者

---

### 数据属性（Data Properties）

#### 1. hasComplexity（有复杂度）

- **定义域**: `:Algorithm`
- **值域**: `xsd:string`

#### 2. hasYear（有年份）

- **定义域**: `:Paper | :System | :Concept`
- **值域**: `xsd:integer`

#### 3. hasCitationCount（有引用数）

- **定义域**: `:Paper`
- **值域**: `xsd:integer`

#### 4. hasDifficulty（有难度）

- **定义域**: `:Concept`
- **值域**: `xsd:string` (初级/中级/高级)

---

## 推理规则（Inference Rules）

### 传递性推理

```
IF A isA B AND B isA C THEN A isA C
IF A hasPart B AND B hasPart C THEN A hasPart C
IF A dependsOn B AND B dependsOn C THEN A dependsOn C
```

### 对称性推理

```
IF A relatedTo B THEN B relatedTo A
IF A conflictsWith B THEN B conflictsWith A
```

### 逆属性推理

```
IF A implements B THEN B implementedBy A
IF A proposes B THEN B proposedBy A
```

---

## 类层次结构

```
Concept
├── Algorithm
│   ├── ConsensusAlgorithm
│   ├── ElectionAlgorithm
│   ├── GossipAlgorithm
│   └── SnapshotAlgorithm
├── System
│   ├── DatabaseSystem
│   │   ├── KeyValueStore
│   │   ├── DocumentStore
│   │   ├── WideColumnStore
│   │   └── GraphDatabase
│   ├── MessageQueue
│   ├── CacheSystem
│   ├── FileSystem
│   └── Orchestrator
├── Theorem
│   ├── ImpossibilityResult
│   └── PossibilityResult
├── Protocol
│   ├── ConsensusProtocol
│   ├── ReplicationProtocol
│   └── TransactionProtocol
└── Pattern
    ├── ArchitecturePattern
    └── DesignPattern
```

---

## 命名约定

### URI格式

- 概念: `http://distributedcomputing.org/ontology#ConceptName`
- 人物: `http://distributedcomputing.org/person#PersonName`
- 论文: `http://distributedcomputing.org/paper#PaperIdentifier`
- 系统: `http://distributedcomputing.org/system#SystemName`

### 命名规则

1. 使用驼峰命名法（CamelCase）
2. 缩写保持大写（如 HTTP, RPC, API）
3. 版本号使用数字后缀（如 HTTP2, RaftV3）
