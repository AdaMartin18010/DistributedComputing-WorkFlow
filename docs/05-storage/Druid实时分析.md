# Druid实时分析专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

Apache Druid是面向实时分析场景的开源OLAP数据库，专为高吞吐事件流和快速交互式查询而设计。其独特的Lambda架构、列式存储、倒排索引和预聚合能力，使其成为实时大盘、监控告警和事件分析的理想选择。

---

## 一、核心概念

### 1.1 Druid架构

```
┌─────────────────────────────────────────────────────────────┐
│                  Apache Druid 架构                           │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  数据源（Kafka/Kinesis/Files）                               │
│       ↓                                                    │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                  Ingestion Layer                       │ │
│  │  ┌─────────────┐    ┌─────────────┐    ┌────────────┐ │ │
│  │  │ Real-time   │    │  Batch      │    │  Indexing  │ │ │
│  │  │ Ingestion   │    │  Ingestion  │    │  Service   │ │ │
│  │  │ (Kafka索引) │    │ (Hadoop/本地)│    │ (任务调度) │ │ │
│  │  └──────┬──────┘    └──────┬──────┘    └──────┬─────┘ │ │
│  │         └──────────────────┴──────────────────┘       │ │
│  └───────────────────────────┬───────────────────────────┘ │
│                              ↓                             │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                  Storage Layer                         │ │
│  │  ┌─────────────────────────────────────────────────┐  │ │
│  │  │  Segments (不可变列式存储)                        │  │ │
│  │  │  ├─ 时间分片 (每小时/每天)                        │  │ │
│  │  │  ├─ 列式压缩 (LZ4/AF4)                           │  │ │
│  │  │  ├─ 倒排索引 (String列)                          │  │ │
│  │  │  └─ Bitmap索引 (Roaring/Concise)               │  │ │
│  │  └─────────────────────────────────────────────────┘  │ │
│  │  ┌─────────────┐    ┌─────────────┐    ┌────────────┐ │ │
│  │  │ Historical  │    │  Middle     │    │  Deep      │ │ │
│  │  │ Nodes       │    │  Manager    │    │  Storage   │ │ │
│  │  │ (查询数据)   │    │ (热缓存)    │    │ (S3/HDFS) │ │ │
│  │  └─────────────┘    └─────────────┘    └────────────┘ │ │
│  └───────────────────────────────────────────────────────┘ │
│                              ↑                             │
│  ┌───────────────────────────┴───────────────────────────┐ │
│  │                  Query Layer                           │ │
│  │  ┌─────────────┐    ┌─────────────┐    ┌────────────┐ │ │
│  │  │ Broker      │    │  Router     │    │  Coordinator│ │ │
│  │  │ Nodes       │    │  (可选)      │    │  (元数据)  │ │ │
│  │  │ (查询路由)   │    │  (负载均衡)  │    │  (Segment管理)│ │ │
│  │  └─────────────┘    └─────────────┘    └────────────┘ │ │
│  └───────────────────────────────────────────────────────┘ │
│                              ↑                             │
│                         Client Query                       │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 核心组件

| 组件 | 职责 | 高可用 |
|------|------|--------|
| **Coordinator** | Segment管理和负载均衡 | 多实例+ZooKeeper |
| **Overlord** | 索引任务调度 | 多实例 |
| **Broker** | 查询路由和结果合并 | 多实例+负载均衡 |
| **Historical** | 历史数据存储和查询 | 多实例+副本 |
| **MiddleManager** | 实时索引任务执行 | 多实例 |
| **Router** | API网关（可选） | 多实例 |

---

## 二、技术细节

### 2.1 数据摄取

```
┌─────────────────────────────────────────────────────────────┐
│                  Druid 数据摄取流程                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Lambda架构：                                               │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                                                       │ │
│  │  Real-time Path (低延迟，最终一致)                     │ │
│  │  ┌─────────┐    ┌─────────┐    ┌─────────┐           │ │
│  │  │ Kafka   │───→│ Peon    │───→│ Real-time│           │ │
│  │  │ Stream  │    │ Tasks   │    │ Segments │           │ │
│  │  └─────────┘    └─────────┘    └────┬────┘           │ │
│  │                                     │ (handoff)       │ │
│  │                                     ↓                 │ │
│  │  Batch Path (高吞吐，精确一次)      ┌─────────┐      │ │
│  │  ┌─────────┐    ┌─────────┐    ┌──→│Historical│      │ │
│  │  │ HDFS/   │───→│ Indexer │───→│   └─────────┘      │ │
│  │  │ S3      │    │ Job     │    │                   │ │
│  │  └─────────┘    └─────────┘    └──→───────────────   │ │
│  │                                     (publish)        │ │
│  │                                                       │ │
│  │  查询时合并：                                          │ │
│  │  ├─ 实时Segment（可变更）                              │ │
│  │  └─ 历史Segment（不可变）                              │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  数据模型：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Timestamp: 主时间戳（必须，用于分区）                   │ │
│  │  Dimensions: 维度列（String类型，用于过滤/分组）         │ │
│  │  Metrics: 指标列（数值类型，用于聚合）                   │ │
│  │                                                       │ │
│  │  例：                                                  │ │
│  │  {                                                    │ │
│  │    "timestamp": "2024-01-01T00:00:00Z",               │ │
│  │    "dimensions": {                                    │ │
│  │      "country": "CN",                                 │ │
│  │      "city": "Beijing",                               │ │
│  │      "device": "mobile"                               │ │
│  │    },                                                 │ │
│  │    "metrics": {                                       │ │
│  │      "click": 1,                                      │ │
│  │      "revenue": 10.5                                  │ │
│  │    }                                                  │ │
│  │  }                                                    │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  摄取规格（Ingestion Spec）：                                │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  {                                                    │ │
│  │    "type": "kafka",                                   │ │
│  │    "dataSchema": {                                    │ │
│  │      "dataSource": "events",                          │ │
│  │      "timestampSpec": {                               │ │
│  │        "column": "timestamp",                         │ │
│  │        "format": "iso"                                │ │
│  │      },                                               │ │
│  │      "dimensionsSpec": {                              │ │
│  │        "dimensions": ["country", "city", "device"]    │ │
│  │      },                                               │ │
│  │      "metricsSpec": [                                 │ │
│  │        {"type": "count", "name": "count"},            │ │
│  │        {"type": "longSum", "name": "click", ...},     │ │
│  │        {"type": "doubleSum", "name": "revenue", ...}  │ │
│  │      ],                                               │ │
│  │      "granularitySpec": {                             │ │
│  │        "type": "uniform",                             │ │
│  │        "segmentGranularity": "DAY",                   │ │
│  │        "queryGranularity": "HOUR"                     │ │
│  │      }                                                │ │
│  │    },                                                 │ │
│  │    "tuningConfig": {...},                             │ │
│  │    "ioConfig": {...}                                  │ │
│  │  }                                                    │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Segment存储结构

```
┌─────────────────────────────────────────────────────────────┐
│                  Druid Segment 结构                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Segment: datasource_interval_version_partition              │
│  例: events_2024-01-01T00:00:00.000Z_2024-01-02T00:00:00.000Z_2024-01-01T00:05:00.000Z_1 │
│                                                            │
│  文件结构：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  segment/                                             │ │
│  │  ├── factory.json            # 元数据                 │ │
│  │  ├── 00000.smoosh            # 列数据文件             │ │
│  │  ├── 00000.smoosh_files      # 文件列表               │ │
│  │  └── version.bin             # 版本信息               │ │
│  │                                                       │ │
│  │  smoosh文件内容：                                      │ │
│  │  ├─ __time (时间戳列)                                  │ │
│  │  ├─ 维度列 (字典编码 + 位图索引)                        │ │
│  │  │   ├─ country (CN, US, JP...)                       │ │
│  │  │   │   ├─ 字典: [CN, US, JP]                        │ │
│  │  │   │   └─ 位图: CN→[0,1,0,1], US→[1,0,1,0]        │ │
│  │  │   └─ city (Beijing, New York...)                   │ │
│  │  └─ 指标列 (压缩存储)                                  │ │
│  │      ├─ click (longSum)                               │ │
│  │      └─ revenue (doubleSum)                           │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  位图索引查询：                                              │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  查询: country='CN' AND city='Beijing'                │ │
│  │                                                       │ │
│  │  计算:                                                │ │
│  │  ├─ country_CN_bitmap = [0,1,0,1,0,1,1,0]            │ │
│  │  ├─ city_Beijing_bitmap = [0,1,0,0,0,1,0,0]          │ │
│  │  ├─ result = AND(country_CN, city_Beijing)           │ │
│  │  └─        = [0,1,0,0,0,1,0,0] → 匹配row 1,5         │ │
│  │                                                       │ │
│  │  优势：O(1)复杂度，极速过滤                             │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、实践指南

### 3.1 集群部署

```yaml
# docker-compose.yml 示例
druid_services:
  # ZooKeeper
  zookeeper:
    image: zookeeper:3.8
    ports:
      - "2181:2181"
  
  # Coordinator
  coordinator:
    image: apache/druid:28.0.0
    command: coordinator
    environment:
      - DRUID_COORDINATOR_STARTUP_RETRY_DELAY=10
      - druid_coordinator_period=PT30S
  
  # Overlord
  overlord:
    image: apache/druid:28.0.0
    command: overlord
  
  # Broker
  broker:
    image: apache/druid:28.0.0
    command: broker
    ports:
      - "8082:8082"
  
  # Historical
  historical:
    image: apache/druid:28.0.0
    command: historical
    volumes:
      - druid_data:/var/druid
  
  # MiddleManager
  middlemanager:
    image: apache/druid:28.0.0
    command: middleManager
```

### 3.2 查询DSL

```json
// Native查询示例
{
  "queryType": "timeseries",
  "dataSource": "events",
  "granularity": "hour",
  "aggregations": [
    {"type": "longSum", "name": "total_clicks", "fieldName": "click"},
    {"type": "doubleSum", "name": "total_revenue", "fieldName": "revenue"}
  ],
  "filter": {
    "type": "and",
    "fields": [
      {"type": "selector", "dimension": "country", "value": "CN"},
      {"type": "interval", "dimension": "__time", 
       "intervals": ["2024-01-01/2024-01-02"]}
    ]
  },
  "intervals": ["2024-01-01/2024-01-07"]
}

// SQL查询（推荐）
SELECT 
  FLOOR(__time TO HOUR) as hour,
  country,
  SUM(click) as total_clicks,
  SUM(revenue) as total_revenue
FROM events
WHERE country = 'CN'
  AND __time BETWEEN '2024-01-01' AND '2024-01-02'
GROUP BY 1, 2
ORDER BY hour
```

### 3.3 最佳实践

```
┌─────────────────────────────────────────────────────────────┐
│                    Druid最佳实践                             │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  1. 数据建模：                                              │ │
│  ├─ 合理选择时间粒度（避免过细）                            │ │
│  ├─ 维度列控制在合理范围（<1000基数）                        │ │
│  └─ 预聚合减少存储（高基数维度需谨慎）                       │ │
│                                                            │
│  2. 摄取优化：                                              │ │
│  ├─ Kafka分区数 ≥ Peon任务数                                │ │
│  ├─ taskDuration不宜过长（1-2小时）                         │ │
│  └─ 监控handoff延迟                                         │ │
│                                                            │
│  3. 查询优化：                                              │ │
│  ├─ 使用近似算法（HyperUnique、ThetaSketch）                │ │
│  ├─ TopN替代GroupBy（性能更好）                             │ │
│  └─ 合理使用缓存（Historical/Broker）                       │ │
│                                                            │
│  4. 运维监控：                                              │ │
│  ├─ 监控Segment大小（建议300MB-700MB）                      │ │
│  ├─ 监控Compaction任务                                      │ │
│  └─ 定期清理未使用数据源                                    │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、常见问题

**Q1: Druid与ClickHouse如何选择？**
A: 实时摄取优先选Druid（Lambda架构成熟）；复杂SQL分析选ClickHouse；已有Kafka生态选Druid更自然。

**Q2: 如何处理数据延迟到达？**
A: 使用Late Message Rejection或配置lateMessageRejectionPeriod，超过窗口的数据进入特殊处理流程。

**Q3: 为什么查询结果为近似值？**
A: 使用了近似聚合算法（如HyperLogLog），牺牲精度换取性能。需要精确值时使用groupBy+exact聚合。

**Q4: 如何实现数据更新？**
A: Druid不支持单条更新，通过重新摄取覆盖（reindex）或使用Lookup功能映射维度值。

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
