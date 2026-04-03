# Presto/Trino 架构详解

## 1. 架构概述

Presto（现 Trino）是 Facebook 开源的分布式 SQL 查询引擎，专为交互式分析而设计。它支持跨多种数据源的联邦查询，具有低延迟、高并发的特点。

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Presto/Trino 架构                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Coordinator                                 │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │   REST API  │  │   Parser    │  │   Discovery Service │   │ │
│  │  │   (接收查询) │  │   (SQL解析)  │  │   (服务发现)        │   │ │
│  │  └──────┬──────┘  └──────┬──────┘  └─────────────────────┘   │ │
│  │         │                │                                     │ │
│  │         └────────────────┼────────────────┐                   │ │
│  │                          ▼                │                   │ │
│  │  ┌─────────────────────────────────────┐  │                   │ │
│  │  │              Planner                 │  │                   │ │
│  │  │  - Analyzer    - Optimizer          │  │                   │ │
│  │  │  - Logical Plan -> Distributed Plan │  │                   │ │
│  │  └─────────────────────────────────────┘  │                   │ │
│  │                          │                │                   │ │
│  │                          ▼                │                   │ │
│  │  ┌─────────────────────────────────────┐  │                   │ │
│  │  │            Stage Scheduler           │  │                   │ │
│  │  │  生成 Stage -> 分配 Worker          │  │                   │ │
│  │  └─────────────────────────────────────┘  │                   │ │
│  └───────────────────────────────┬───────────┴───────────────────┘ │
│                                  │                                  │
│           ┌──────────────────────┼──────────────────────┐          │
│           │                      │                      │          │
│           ▼                      ▼                      ▼          │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐│
│  │  Worker Node 1  │    │  Worker Node 2  │    │  Worker Node N  ││
│  │  ┌───────────┐  │    │  ┌───────────┐  │    │  ┌───────────┐  ││
│  │  │ Task 1    │  │    │  │ Task 3    │  │    │  │ Task 5    │  ││
│  │  │ Task 2    │  │    │  │ Task 4    │  │    │  │ Task 6    │  ││
│  │  └───────────┘  │    │  └───────────┘  │    │  └───────────┘  ││
│  │                 │    │                 │    │                 ││
│  │  - 执行 Task    │    │  - 执行 Task    │    │  - 执行 Task    ││
│  │  - 本地数据处理 │    │  - 本地数据处理 │    │  - 本地数据处理 ││
│  │  - 与其他 Worker│    │  - 与其他 Worker│    │  - 与其他 Worker││
│  │    交换数据     │    │    交换数据     │    │    交换数据     ││
│  └─────────────────┘    └─────────────────┘    └─────────────────┘│
│                                                                     │
│  Connector Layer (连接到各种数据源)                                  │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐               │
│  │  Hive    │ │  MySQL   │ │ PostgreSQL│ │  Kafka   │               │
│  │  Catalog │ │  Catalog │ │  Catalog  │ │  Catalog │               │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心组件

| 组件 | 职责 | 部署模式 |
|------|------|----------|
| **Coordinator** | 接收查询、解析 SQL、生成执行计划、调度任务 | 单节点（可 HA） |
| **Worker** | 执行 Task、处理数据、与其他 Worker 交换数据 | 多节点 |
| **Discovery Service** | 服务发现，Worker 注册和心跳 | 内嵌在 Coordinator |
| **Connector** | 连接各种数据源 | 插件化 |

## 2. 查询执行流程

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Presto 查询执行流程                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  SQL ──▶ Parse ──▶ Analyze ──▶ Plan ──▶ Optimize ──▶ Schedule ──▶ Execute│
│   │        │         │         │          │          │          │   │
│   ▼        ▼         ▼         ▼          ▼          ▼          ▼   │
│  ┌───┐  ┌─────┐   ┌─────┐  ┌─────┐    ┌─────┐    ┌─────┐   ┌────┐│
│  │SQL│  │AST  │   │Analyzed│Logical│    │Opt. │    │Frag-│   │Task││
│  │   │  │     │   │Plan   │Plan   │    │Plan │    │ments│   │Exec││
│  └───┘  └─────┘   └─────┘  └─────┘    └─────┘    └─────┘   └────┘│
│                                                                     │
│  Fragment (分布式执行单元)：                                         │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Fragment 0 (Coordinator)                                    │   │
│  │     │                                                        │   │
│  │     ▼ Exchange                                               │   │
│  │  ┌────────────────────────────────────────────────────────┐  │   │
│  │  │  Fragment 1 (Source - 多个 Worker 并行)                 │  │   │
│  │  │  ┌─────────┐  ┌─────────┐  ┌─────────┐                 │  │   │
│  │  │  │ Split 1 │  │ Split 2 │  │ Split N │  (Table Scan)   │  │   │
│  │  │  └────┬────┘  └────┬────┘  └────┬────┘                 │  │   │
│  │  │       │            │            │                      │  │   │
│  │  │       └────────────┼────────────┘                      │  │   │
│  │  │                    ▼ Partial Aggregate                 │  │   │
│  │  │       ┌────────────────────────────────────────┐      │  │   │
│  │  │       │ Fragment 2 (Aggregation - Shuffle)     │      │  │   │
│  │  │       │  ┌─────────┐  ┌─────────┐              │      │  │   │
│  │  │       │  │ Worker  │  │ Worker  │              │      │  │   │
│  │  │       │  └─────────┘  └─────────┘              │      │  │   │
│  │  │       └────────────────────────────────────────┘      │  │   │
│  │  └────────────────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. 配置示例

### 3.1 Coordinator 配置

```properties
# config.properties (Coordinator)
coordinator=true
node-scheduler.include-coordinator=false
http-server.http.port=8080
query.max-memory=50GB
query.max-memory-per-node=5GB
query.max-total-memory-per-node=10GB
discovery-server.enabled=true
discovery.uri=http://coordinator:8080

# 通信配置
exchange.http-client.max-connections=1000
exchange.http-client.max-connections-per-server=100
exchange.http-client.connect-timeout=10s

# 任务配置
task.max-worker-threads=100
task.writer-count=4

# 查询管理
query.min-expire-age=30m
query.max-history=1000
```

### 3.2 Worker 配置

```properties
# config.properties (Worker)
coordinator=false
http-server.http.port=8080
discovery.uri=http://coordinator:8080
query.max-memory-per-node=5GB
query.max-total-memory-per-node=10GB

# 资源配置
task.max-worker-threads=100
task.concurrency=16
node-scheduler.max-splits-per-node=100
node-scheduler.max-pending-splits-per-task=10
```

### 3.3 Hive Connector 配置

```properties
# catalog/hive.properties
connector.name=hive
hive.metastore.uri=thrift://metastore:9083
hive.config.resources=/etc/hadoop/conf/core-site.xml,/etc/hadoop/conf/hdfs-site.xml

# 数据格式
hive.parquet.use-column-names=true
hive.orc.use-column-names=true

# 分区和桶
hive.max-partitions-per-writers=100
hive.max-partitions-per-scan=1000

# 安全配置
hive.hdfs.authentication.type=KERBEROS
hive.hdfs.impersonation.enabled=true
```

## 4. SQL 示例

```sql
-- 基本查询
SELECT
    region,
    COUNT(*) as order_count,
    SUM(amount) as total_amount,
    AVG(amount) as avg_amount
FROM hive.sales.orders
WHERE order_date >= DATE '2024-01-01'
GROUP BY region
ORDER BY total_amount DESC
LIMIT 100;

-- 联邦查询（跨数据源 JOIN）
SELECT
    c.customer_name,
    o.order_id,
    p.product_name
FROM mysql.crm.customers c
JOIN hive.sales.orders o ON c.customer_id = o.customer_id
JOIN postgresql.catalog.products p ON o.product_id = p.product_id
WHERE o.order_date >= CURRENT_DATE - INTERVAL '7' DAY;

-- 窗口函数
SELECT
    user_id,
    event_time,
    event_type,
    ROW_NUMBER() OVER (PARTITION BY user_id ORDER BY event_time) as seq,
    LAG(event_type) OVER (PARTITION BY user_id ORDER BY event_time) as prev_event
FROM kafka.events.user_activity;

-- 复杂分析
WITH daily_stats AS (
    SELECT
        DATE(order_time) as order_date,
        region,
        COUNT(*) as orders,
        SUM(amount) as revenue
    FROM hive.sales.orders
    WHERE order_time >= CURRENT_DATE - INTERVAL '30' DAY
    GROUP BY 1, 2
)
SELECT
    order_date,
    region,
    orders,
    revenue,
    LAG(revenue) OVER (PARTITION BY region ORDER BY order_date) as prev_revenue,
    (revenue - LAG(revenue) OVER (PARTITION BY region ORDER BY order_date))
        / LAG(revenue) OVER (PARTITION BY region ORDER BY order_date) * 100
        as growth_pct
FROM daily_stats
ORDER BY order_date DESC, region;
```

## 5. 性能优化

### 5.1 内存配置

```properties
# 查询内存限制
query.max-memory=100GB
query.max-memory-per-node=10GB
query.max-total-memory-per-node=20GB

# 内存管理策略
memory.heap-headroom-per-node=2GB
query.low-memory-killer.policy=total-reservation
```

### 5.2 并发控制

```properties
# 查询并发
query.max-concurrent-queries=100
query.max-queued-queries=500
query.queue-config-file=/etc/trino/queues.json
```

### 5.3 查询优化

```sql
-- 1. 使用分区裁剪
SELECT * FROM hive.sales.orders
WHERE order_date BETWEEN DATE '2024-01-01' AND DATE '2024-01-31'
  AND region = 'North America';

-- 2. 使用桶优化 JOIN
SELECT /*+ BROADCAST(small_table) */ *
FROM large_table l
JOIN small_table s ON l.key = s.key;

-- 3. 限制数据量
SELECT * FROM huge_table
WHERE event_time > CURRENT_TIMESTAMP - INTERVAL '1' HOUR
LIMIT 1000;
```

## 6. 资源组配置

```json
// etc/resource-groups.json
{
  "rootGroups": [
    {
      "name": "global",
      "softMemoryLimit": "80%",
      "hardConcurrencyLimit": 100,
      "maxQueued": 1000,
      "schedulingPolicy": "weighted",
      "jmxExport": true,
      "subGroups": [
        {
          "name": "data-science",
          "softMemoryLimit": "40%",
          "hardConcurrencyLimit": 40,
          "maxQueued": 400,
          "schedulingWeight": 40
        },
        {
          "name": "bi-tools",
          "softMemoryLimit": "30%",
          "hardConcurrencyLimit": 30,
          "maxQueued": 300,
          "schedulingWeight": 30
        },
        {
          "name": "adhoc",
          "softMemoryLimit": "10%",
          "hardConcurrencyLimit": 10,
          "maxQueued": 100,
          "schedulingWeight": 10
        }
      ]
    }
  ],
  "selectors": [
    {
      "user": "data_scientist.*",
      "group": "global.data-science"
    },
    {
      "source": "tableau",
      "group": "global.bi-tools"
    },
    {
      "group": "global.adhoc"
    }
  ]
}
```

## 7. 与 Hive 对比

| 特性 | Presto/Trino | Hive |
|------|--------------|------|
| **执行引擎** | 基于内存的 MPP | MapReduce/Tez/Spark |
| **延迟** | 毫秒-秒级 | 分钟级 |
| **适用场景** | 交互式查询 | 批处理 ETL |
| **数据源** | 联邦查询 | 主要是 HDFS |
| **SQL 支持** | ANSI SQL 兼容 | HiveQL |
| **扩展性** | 插件化 Connector | UDF/UDAF |

## 8. 总结

Presto/Trino 的优势：

- **低延迟**：内存计算，毫秒-秒级响应
- **联邦查询**：跨多种数据源统一查询
- **高并发**：支持数百并发查询
- **标准 SQL**：ANSI SQL 兼容

适用场景：

- 交互式数据分析
- 数据湖查询
- 联邦查询（跨数据源 JOIN）
- 实时仪表盘

最佳实践：

1. 合理配置内存限制
2. 使用分区裁剪减少数据扫描
3. 对常用数据使用缓存
4. 监控查询性能，优化慢查询
