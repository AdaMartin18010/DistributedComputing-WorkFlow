# Presto分布式查询专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

Presto（现Trino）是Facebook开源的分布式SQL查询引擎，专为大规模数据湖交互式分析而设计。其内存计算架构、插件化连接器和对标准SQL的完整支持，使其成为跨数据源联邦查询的首选方案。

---

## 一、核心概念

### 1.1 Presto架构

```
┌─────────────────────────────────────────────────────────────┐
│                   Presto/Trino 架构                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Client (CLI/JDBC/ODBC/Python)                             │
│       ↓                                                    │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                  Coordinator                          │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐   │ │
│  │  │ Query Parser│  │  Planner    │  │  Scheduler  │   │ │
│  │  │             │  │  (优化器)   │  │  (调度器)   │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘   │ │
│  │  ┌─────────────────────────────────────────────────┐  │ │
│  │  │  Execution Engine (Stage/Task管理)               │  │ │
│  │  └─────────────────────────────────────────────────┘  │ │
│  └───────────────────────────┬───────────────────────────┘ │
│                              │ REST API                    │
│          ┌───────────────────┼───────────────────┐         │
│          ↓                   ↓                   ↓         │
│  ┌───────────────┐   ┌───────────────┐   ┌───────────────┐│
│  │   Worker 1    │   │   Worker 2    │   │   Worker N    ││
│  │ ┌───────────┐ │   │ ┌───────────┐ │   │ ┌───────────┐ ││
│  │ │ Task 1.1  │ │   │ │ Task 2.1  │ │   │ │ Task N.1  │ ││
│  │ │ Task 1.2  │ │   │ │ Task 2.2  │ │   │ │ Task N.2  │ ││
│  │ │ ...       │ │   │ │ ...       │ │   │ │ ...       │ ││
│  │ └───────────┘ │   │ └───────────┘ │   │ └───────────┘ ││
│  │ ┌───────────┐ │   │ ┌───────────┐ │   │ ┌───────────┐ ││
│  │ │Connectors │ │   │ │Connectors │ │   │ │Connectors │ ││
│  │ │- Hive     │ │   │ │- MySQL    │ │   │ │- Kafka    │ ││
│  │ │- Iceberg  │ │   │ │- Postgres │ │   │ │- MongoDB  │ ││
│  │ │- Delta    │ │   │ │- Cassandra│ │   │ │- Redis    │ ││
│  │ └───────────┘ │   │ └───────────┘ │   │ └───────────┘ ││
│  └───────────────┘   └───────────────┘   └───────────────┘│
│                                                            │
│  核心特性：                                                  │
│  ├─ 纯内存计算，无中间结果落盘                                │ │
│  ├─ 流水线执行，数据流式处理                                  │ │
│  ├─ 基于成本的优化器（CBO）                                   │ │
│  ├─ 40+ 连接器支持多种数据源                                  │ │
│  └─ 标准SQL，兼容HiveQL                                       │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 执行模型

```
┌─────────────────────────────────────────────────────────────┐
│                  Presto 查询执行模型                         │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  SQL → Stage → Task → Driver → Operator → Split            │
│                                                            │
│  例：SELECT region, SUM(sales) FROM orders GROUP BY region  │
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Stage 0 (Root)                                       │ │
│  │  ├─ 最终聚合 + 输出结果                                │ │
│  │  └─ Exchange ← 接收Stage 1结果                         │ │
│  │                                                       │ │
│  │  Stage 1 (Partial Aggregation)                        │ │
│  │  ├─ 部分聚合 (region, sum)                             │ │
│  │  └─ Exchange ← 接收Stage 2数据                         │ │
│  │                                                       │ │
│  │  Stage 2 (Scan/Filter)                                │ │
│  │  └─ 从Connector读取orders表数据                        │ │
│  │      Filter + Project                                  │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  Task分布：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                                                       │ │
│  │  Worker 1          Worker 2          Worker 3         │ │
│  │  ┌─────────┐       ┌─────────┐       ┌─────────┐     │ │
│  │  │Task 2.1 │       │Task 2.2 │       │Task 2.3 │     │ │
│  │  │ Scan    │       │ Scan    │       │ Scan    │     │ │
│  │  │ Split 1 │       │ Split 2 │       │ Split 3 │     │ │
│  │  └────┬────┘       └────┬────┘       └────┬────┘     │ │
│  │       └─────────────────┼─────────────────┘          │ │
│  │                   Shuffle/Exchange                    │ │
│  │       ┌─────────────────┼─────────────────┐          │ │
│  │  ┌────┴────┐       ┌────┴────┐       ┌────┴────┐     │ │
│  │  │Task 1.1 │       │Task 1.2 │       │Task 1.3 │     │ │
│  │  │Partial  │       │Partial  │       │Partial  │     │ │
│  │  │Agg      │       │Agg      │       │Agg      │     │ │
│  │  └────┬────┘       └────┬────┘       └────┬────┘     │ │
│  │       └─────────────────┼─────────────────┘          │ │
│  │                   Final Aggregation                   │ │
│  │                     ┌───┴───┐                        │ │
│  │                ┌────┴────┐  │                        │ │
│  │                │Task 0.1 │  │                        │ │
│  │                │ Output  │  │                        │ │
│  │                └─────────┘  │                        │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  Split: 数据分片（如HDFS的Block）                            │ │
│  Driver: 单线程执行单元，包含Operator链                       │ │
│  Operator: 具体操作（Scan/Filter/Project/Aggregation等）      │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、技术细节

### 2.1 连接器体系

```
┌─────────────────────────────────────────────────────────────┐
│                  Presto 连接器体系                           │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  数据湖连接器：                                              │
│  ├─ Hive Connector: HDFS/S3上的Parquet/ORC/CSV              │ │
│  ├─ Iceberg Connector: 开放表格式，时间旅行                 │ │
│  ├─ Delta Lake Connector: Databricks表格式                 │ │
│  ├─ Hudi Connector: 增量数据湖                              │ │
│  └─ BigQuery Connector: Google BigQuery                    │ │
│                                                            │
│  数据库连接器：                                              │ │
│  ├─ MySQL/PostgreSQL/Oracle/SQL Server                     │ │
│  ├─ MongoDB/Cassandra/Redis                                │ │
│  └─ ClickHouse/Druid/Elasticsearch                         │ │
│                                                            │
│  消息队列连接器：                                            │ │
│  ├─ Kafka Connector: 流数据查询                             │ │
│  └─ Pulsar Connector                                        │ │
│                                                            │
│  其他连接器：                                                │ │
│  ├─ JMX Connector: 监控指标                                 │ │
│  ├─ Thrift Connector: 自定义服务                            │ │
│  └─ Accumulo/Apache Pinot                                   │ │
│                                                            │
│  Hive Connector配置示例：                                    │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  connector.name=hive-hadoop2                          │ │
│  │  hive.metastore.uri=thrift://metastore:9083           │ │
│  │  hive.s3.aws-access-key=xxx                           │ │
│  │  hive.s3.aws-secret-key=xxx                           │ │
│  │  hive.s3.endpoint=s3.amazonaws.com                    │ │
│  │  hive.storage-format=PARQUET                          │ │
│  │  hive.compression-codec=ZSTD                          │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 查询优化

```
┌─────────────────────────────────────────────────────────────┐
│                  Presto 查询优化器                           │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  优化器特性：                                                │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  基于成本的优化 (CBO)                                  │ │
│  │  ├─ 表/列统计信息收集                                  │ │
│  │  ├─ 成本模型估算                                       │ │
│  │  └─ 多阶段优化规则                                     │ │
│  │                                                       │ │
│  │  优化规则示例：                                        │ │
│  │  ├─ Predicate Pushdown: 谓词下推到数据源               │ │
│  │  ├─ Projection Pushdown: 列裁剪                       │ │
│  │  ├─ Join Reordering: 基于成本调整Join顺序              │ │
│  │  ├─ Aggregation Pushdown: 聚合下推                     │ │
│  │  └─ Dynamic Filter: 运行时过滤                         │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  性能调优参数：                                              │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  query.max-memory=50GB          # 单查询最大内存       │ │
│  │  query.max-memory-per-node=5GB  # 每节点最大内存       │ │
│  │  query.max-total-memory=100GB   # 含子查询总内存       │ │
│  │  query.max-execution-time=30m   # 最大执行时间         │ │
│  │                                                       │ │
│  │  task.writer-count=4            # 并发写文件数         │ │
│  │  task.concurrency=16            # 默认并发度           │ │
│  │  task.scale-writers.enabled=true # 自适应扩展写        │ │
│  │                                                       │ │
│  │  join-distribution-type=AUTOMATIC  # Join分布类型      │ │
│  │  optimizer.join-reordering-strategy=AUTOMATIC           │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、实践指南

### 3.1 集群部署

```yaml
# docker-compose.yml
version: '3'
services:
  coordinator:
    image: trinodb/trino:423
    ports:
      - "8080:8080"
    volumes:
      - ./etc/coordinator:/etc/trino
    command: http://localhost:8080

  worker1:
    image: trinodb/trino:423
    volumes:
      - ./etc/worker:/etc/trino
    depends_on:
      - coordinator

  worker2:
    image: trinodb/trino:423
    volumes:
      - ./etc/worker:/etc/trino
    depends_on:
      - coordinator
```

```properties
# coordinator/config.properties
coordinator=true
node-scheduler.include-coordinator=false
http-server.http.port=8080
query.max-memory=50GB
query.max-memory-per-node=5GB
discovery-server.enabled=true
discovery.uri=http://localhost:8080

# worker/config.properties
coordinator=false
http-server.http.port=8080
query.max-memory=50GB
query.max-memory-per-node=5GB
discovery.uri=http://coordinator:8080
```

### 3.2 联邦查询示例

```sql
-- 跨数据源JOIN
SELECT
    c.customer_id,
    c.customer_name,
    o.order_date,
    o.total_amount,
    p.product_name
-- MySQL中的客户表
FROM mysql.crm.customers c
-- Hive中的订单表
JOIN hive.ods.orders o ON c.customer_id = o.customer_id
-- PostgreSQL中的产品表
JOIN postgresql.inventory.products p ON o.product_id = p.product_id
WHERE o.order_date >= DATE '2024-01-01'
  AND c.region = 'APAC';

-- 查询Kafka流数据
SELECT
    _message,
    _key,
    _partition,
    _offset,
    _timestamp
FROM kafka.default.page_views
WHERE _timestamp > CURRENT_TIMESTAMP - INTERVAL '5' MINUTE;

-- 创建物化视图（使用Iceberg）
CREATE MATERIALIZED VIEW iceberg.warehouse.sales_summary
AS
SELECT
    region,
    DATE_TRUNC('month', order_date) as month,
    SUM(amount) as total_sales,
    COUNT(*) as order_count
FROM hive.ods.orders
GROUP BY 1, 2;
```

### 3.3 最佳实践

```
┌─────────────────────────────────────────────────────────────┐
│                    Presto最佳实践                            │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  1. 查询优化：                                              │ │
│  ├─ 使用列式存储（Parquet/ORC）                             │ │
│  ├─ 合理分区（按日期/地区）                                  │ │
│  ├─ 避免SELECT *，只选需要的列                              │ │
│  ├─ 大表JOIN使用Bucket优化                                   │ │
│  └─ 收集统计信息（ANALYZE）                                  │ │
│                                                            │
│  2. 内存管理：                                              │ │
│  ├─ 设置合理的内存限制                                       │ │
│  ├─ 避免大结果集（使用LIMIT）                                │ │
│  ├─ 启用溢出（spill-to-disk）                                │ │
│  └─ 监控内存使用，及时Kill异常查询                           │ │
│                                                            │
│  3. 安全配置：                                              │ │
│  ├─ 启用认证（Password/LDAP/OAuth）                          │ │
│  ├─ 配置Query ACL（访问控制）                                │ │
│  └─ 敏感数据使用Column Masking                               │ │
│                                                            │
│  4. 监控运维：                                              │ │
│  ├─ 使用JMX Exporter暴露指标                                 │ │
│  ├─ 监控查询延迟、队列深度                                   │ │
│  ├─ 监控Worker节点健康                                       │ │
│  └─ 配置Resource Groups进行资源隔离                          │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、常见问题

**Q1: Presto与Spark SQL如何选择？**
A: 交互式查询（秒级响应）选Presto；ETL批处理（分钟级）选Spark；两者可共存，Presto作为即席查询层。

**Q2: 查询内存不足怎么办？**
A: 1) 增加query.max-memory；2) 启用spill-enabled；3) 优化SQL减少内存使用；4) 增加Worker节点。

**Q3: 如何提高HDFS查询性能？**
A: 1) 使用列式存储（Parquet）；2) 数据分区；3) 压缩（ZSTD/Snappy）；4) 收集统计信息。

**Q4: Presto和Trino的关系？**
A: Trino是Presto原核心团队离开Facebook后维护的分支，功能更活跃。两者API兼容，可无缝迁移。

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
