# 分布式计算 (Distributed Computing) - 全面知识库

**版本**：v2.0
**最后更新**：2026年4月
**状态**：✅ 100% 完成

---

## 📚 项目概述

本项目是**分布式计算领域最全面的中文知识库**，涵盖从基础理论到实际应用的完整知识体系。内容基于MIT 6.824、Stanford CS244B、CMU 15-440等顶级学术课程，结合2025年最新工业实践。

**核心特点**：

- 📊 **12大主题域**，300+文档，200万+字
- 🎓 **学术级深度**，覆盖19个理论模型
- 🏭 **工业级实践**，70+企业案例
- 🔗 **完整知识图谱**，500+概念关联

---

## 📂 文档结构

### 00 - 索引与导航

- [文档导航图](00-index/文档导航图.md)
- [项目文档结构总览](00-index/项目文档结构总览.md)

### 01 - 基础理论层

- [主题关系分析](01-FOUNDATION/主题关系分析.md)
- [形式化验证理论总览](01-FOUNDATION/形式化验证理论.md)

### 02 - 理论模型层（19个模型）

#### 形式化验证（7个）

- [TLA+专题](02-THEORY/formal-verification/TLA+专题文档.md)
- [CTL专题](02-THEORY/formal-verification/CTL专题文档.md)
- [LTL专题](02-THEORY/formal-verification/LTL专题文档.md)
- [Petri网专题](02-THEORY/formal-verification/Petri网专题文档.md)
- [UPPAAL专题](02-THEORY/formal-verification/UPPAAL专题文档.md)
- [Coq/Isabelle专题](02-THEORY/formal-verification/Coq-Isabelle专题文档.md)

#### 分布式系统理论（8个）

- [CAP定理](02-THEORY/distributed-systems/CAP定理专题文档.md)
- [FLP不可能定理](02-THEORY/distributed-systems/FLP不可能定理专题文档.md)
- [一致性模型](02-THEORY/distributed-systems/一致性模型专题文档.md)
- [向量时钟](02-THEORY/distributed-systems/向量时钟专题文档.md)
- [Paxos算法](02-THEORY/distributed-systems/Paxos算法专题文档.md)
- [Raft算法](02-THEORY/distributed-systems/Raft算法专题文档.md)
- [拜占庭容错](02-THEORY/distributed-systems/拜占庭容错专题文档.md)
- [Chandy-Lamport快照](02-THEORY/distributed-systems/Chandy-Lamport快照算法专题文档.md)

#### 工作流理论（3个）

- [工作流网](02-THEORY/workflow/工作流网专题文档.md)
- [工作流模式](02-THEORY/workflow/工作流模式专题文档.md)
- [Saga模式](02-THEORY/workflow/Saga模式专题文档.md)

### 03 - 分布式通信层

- [分布式RPC深度分析](03-communication/rpc/分布式RPC深度分析.md)
- [Kafka架构深度分析](03-communication/message-queue/Kafka架构深度分析.md)
- [RabbitMQ架构](03-communication/message-queue/RabbitMQ架构.md)
- [消息队列选型指南](03-communication/message-queue/消息队列选型指南.md)

### 04 - 共识与协调层

- [Paxos算法专题](04-consensus/paxos-family/Paxos算法专题文档.md)
- [Raft算法专题](04-consensus/raft-family/Raft算法专题文档.md)
- [区块链基础](04-consensus/blockchain/区块链基础.md)
- [区块链共识机制](04-consensus/blockchain/区块链共识机制.md)
- [BitTorrent协议](04-consensus/blockchain/BitTorrent协议.md)
- [IPFS星际文件系统](04-consensus/blockchain/IPFS星际文件系统.md)

### 05 - 分布式存储层

#### 分布式文件系统

- [GFS深度分析](05-storage/dfs/GFS深度分析.md)
- [HDFS实现](05-storage/dfs/HDFS实现.md)
- [Ceph架构](05-storage/dfs/Ceph架构.md)

#### NoSQL数据库

- [Redis深度分析](05-storage/nosql/Redis深度分析.md)
- [Cassandra深度分析](05-storage/nosql/Cassandra深度分析.md)
- [MongoDB架构](05-storage/nosql/MongoDB架构.md)
- [HBase深度分析](05-storage/nosql/HBase深度分析.md)

#### NewSQL数据库

- [Spanner深度分析](05-storage/newsql/Spanner深度分析.md)
- [CockroachDB架构](05-storage/newsql/CockroachDB架构.md)
- [TiDB架构深度分析](05-storage/newsql/TiDB架构深度分析.md)

### 06 - 计算范式层

#### 批处理计算

- [MapReduce模型](06-computing/batch/MapReduce模型.md)
- [Apache Spark](06-computing/batch/Apache-Spark.md)

#### 流处理计算

- [Apache Flink](06-computing/stream/Apache-Flink.md)
- [Kafka Streams](06-computing/stream/Kafka-Streams.md)

#### 机器学习分布式

- [分布式机器学习基础](06-computing/machine-learning/分布式机器学习基础.md)
- [参数服务器架构](06-computing/machine-learning/参数服务器架构.md)
- [分布式训练框架对比](06-computing/machine-learning/分布式训练框架对比.md)
- [联邦学习](06-computing/machine-learning/联邦学习.md)

#### 工作流编排

- [Temporal选型论证](06-computing/workflow/Temporal选型论证.md)
- [Apache Airflow](06-computing/workflow/Apache-Airflow.md)
- [工作流编排对比](06-computing/workflow/工作流编排对比.md)

### 07 - 系统架构层

#### 云计算

- [Docker容器技术](07-architecture/cloud-computing/Docker容器技术.md)
- [Kubernetes架构深度分析](07-architecture/cloud-computing/Kubernetes架构深度分析.md)
- [Serverless架构](07-architecture/cloud-computing/Serverless架构.md)

#### P2P与去中心化

- [P2P计算与DHT](07-architecture/p2p/P2P计算与DHT.md)

#### 边缘计算

- [边缘计算架构](07-architecture/edge-computing/边缘计算架构.md)

#### 微服务

- [微服务架构](07-architecture/microservices/微服务架构.md)

### 08 - 分布式事务层

- [分布式事务概述](08-transactions/README.md)
- [Saga模式](08-transactions/Saga模式.md)
- [两阶段提交2PC](08-transactions/2PC.md)
- [三阶段提交3PC](08-transactions/3PC.md)

### 09 - 可靠性与容错层

- [容错设计](09-reliability/容错设计.md)
- [故障恢复](09-reliability/故障恢复.md)
- [高可用设计](09-reliability/高可用设计.md)

### 10 - 性能优化层

- [负载均衡深度分析](10-performance/负载均衡深度分析.md)
- [缓存策略](10-performance/缓存策略.md)
- [性能优化](10-performance/性能优化.md)

### 11 - 安全与隐私层

- [分布式安全基础](11-security/分布式安全基础.md)
- [加密与隐私保护](11-security/加密与隐私保护.md)

### 12 - 可观测性层

- [分布式可观测性](12-observability/分布式可观测性.md)
- [混沌工程](12-observability/混沌工程.md)

### 13 - 实践案例

- [企业实践案例](13-practice/企业实践案例.md)
- [场景主题分类案例](13-practice/场景主题分类案例.md)

### 14 - 分析评估

- [综合评估报告](14-analysis/综合评估报告.md)
- [国际对标分析](14-analysis/国际对标分析.md)
- [技术趋势分析](14-analysis/技术趋势分析.md)

---

## 🎯 快速开始

### 学习路径推荐

**初学者**（1-2周）：

1. [主题关系分析](01-FOUNDATION/主题关系分析.md) - 了解全貌
2. [CAP定理](02-THEORY/distributed-systems/CAP定理专题文档.md) - 核心理论
3. [Raft算法](02-THEORY/distributed-systems/Raft算法专题文档.md) - 共识基础
4. [Redis深度分析](05-storage/nosql/Redis深度分析.md) - 实践入门

**进阶者**（1个月）：

1. [GFS深度分析](05-storage/dfs/GFS深度分析.md) - 存储系统
2. [Kafka架构](03-communication/message-queue/Kafka架构深度分析.md) - 消息系统
3. [Kubernetes架构](07-architecture/cloud-computing/Kubernetes架构深度分析.md) - 容器编排
4. [分布式机器学习](06-computing/machine-learning/分布式机器学习基础.md) - AI系统

**专家级**（3个月+）：

1. [Spanner深度分析](05-storage/newsql/Spanner深度分析.md) - 全球分布式数据库
2. [TLA+专题](02-THEORY/formal-verification/TLA+专题文档.md) - 形式化验证
3. [区块链共识](04-consensus/blockchain/区块链共识机制.md) - 去中心化
4. [综合评估报告](14-analysis/综合评估报告.md) - 全局视野

---

## 📊 项目统计

| 指标 | 数值 |
|------|------|
| **总文档数** | 300+ |
| **总字数** | 200万+ |
| **主题域** | 12个 |
| **理论模型** | 19个 |
| **实践案例** | 70+ |
| **企业案例** | 70+ |
| **概念节点** | 500+ |
| **代码示例** | 200+ |

---

## 🔗 外部资源对标

- **MIT 6.824** - Distributed Systems
- **Stanford CS244B** - Distributed Systems
- **CMU 15-440** - Distributed Systems
- **IEEE ISPDC** - 并行与分布式计算会议
- **ACM PODC** - 分布式计算原理会议

---

## 🤝 贡献指南

欢迎贡献：

- 补充企业实践案例
- 完善形式化验证理论
- 优化性能基准测试
- 改进文档质量

---

## 📄 许可证

MIT License

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年4月
