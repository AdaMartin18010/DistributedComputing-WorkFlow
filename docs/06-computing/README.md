# 06-computing: 分布式计算框架

本文档库涵盖了主流分布式计算框架的详细文档，包括批处理计算、流处理框架、图计算、查询引擎和资源调度等主题。

## 文档结构

```
06-computing/
├── README.md                           # 本文件
├── batch-processing/                   # 批处理计算
│   ├── Hadoop-MapReduce详解.md
│   ├── Spark-Core详解.md
│   ├── Tez计算框架.md
│   └── 批处理优化技巧.md
├── stream-processing/                  # 流处理框架
│   ├── Flink-Runtime详解.md
│   ├── Spark-Structured-Streaming.md
│   ├── Kafka-Streams详解.md
│   ├── 流处理语义.md
│   ├── 窗口操作详解.md
│   └── 状态管理.md
├── graph-computing/                    # 图计算
│   ├── Pregel模型.md
│   └── GraphX详解.md
├── query-engine/                       # 查询引擎
│   ├── Spark-SQL详解.md
│   └── Presto-Trino架构.md
└── resource-scheduling/                # 资源调度
│   ├── YARN资源管理.md
│   ├── Kubernetes调度器.md
│   └── 资源隔离技术.md
```

## 快速导航

### 批处理计算

- **Hadoop MapReduce**: 经典的分布式批处理框架，适合离线大规模数据处理
- **Spark Core**: 基于内存的分布式计算引擎，支持 DAG 执行和缓存
- **Tez**: 优化 MapReduce 的 DAG 计算框架，主要用于 Hive 加速

### 流处理框架

- **Flink**: 原生流处理引擎，支持精确一次语义和低延迟处理
- **Spark Structured Streaming**: 基于微批的流处理，与 Spark SQL 集成
- **Kafka Streams**: 轻量级流处理库，与 Kafka 深度集成

### 图计算

- **Pregel**: Google 提出的 BSP 图计算模型
- **GraphX**: Spark 的图计算组件，支持 Pregel API

### 查询引擎

- **Spark SQL**: Spark 的结构化数据处理模块
- **Presto/Trino**: 分布式 SQL 查询引擎，支持联邦查询

### 资源调度

- **YARN**: Hadoop 生态的资源管理系统
- **Kubernetes**: 云原生容器编排平台

## 学习路径建议

### 初级

1. Hadoop MapReduce 基础
2. Spark Core 和 RDD
3. Spark SQL 基础

### 中级

1. Spark 性能优化
2. Flink 流处理基础
3. 窗口和状态管理

### 高级

1. Flink 精确一次语义
2. 自定义图算法
3. 资源调度优化

## 关键技术对比

### 批处理 vs 流处理

| 特性 | 批处理 | 流处理 |
|------|--------|--------|
| 数据范围 | 有限数据集 | 无限数据流 |
| 延迟 | 分钟-小时级 | 毫秒-秒级 |
| 容错 | 任务重试 | Checkpoint |

### 状态后端对比

| 后端 | 存储位置 | 适用场景 |
|------|----------|----------|
| Memory | JVM Heap | 测试、小状态 |
| FileSystem | 内存+文件系统 | 大状态、生产 |
| RocksDB | 本地磁盘 | 超大状态 |

### 调度器对比

| 调度器 | 特点 | 适用 |
|--------|------|------|
| YARN FIFO | 简单 | 测试 |
| YARN Capacity | 多队列 | 多租户生产 |
| Kubernetes | 云原生 | 容器化应用 |

## 参考资源

- [Apache Spark 官方文档](https://spark.apache.org/docs/)
- [Apache Flink 官方文档](https://flink.apache.org/)
- [Apache Kafka Streams 文档](https://kafka.apache.org/documentation/streams/)
- [Presto/Trino 文档](https://trino.io/docs/)
- [Kubernetes 文档](https://kubernetes.io/docs/)

---

*本文档库持续更新中，欢迎贡献和反馈。*
