# ClickHouse列式存储专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

ClickHouse是俄罗斯Yandex开源的高性能列式OLAP数据库，采用向量化执行引擎和MPP架构，在单表亿级数据分析场景下性能卓越。其独特的MergeTree存储引擎、数据压缩和向量化计算使其成为实时分析领域的首选方案。

---

## 一、核心概念

### 1.1 列式存储 vs 行式存储

```
┌─────────────────────────────────────────────────────────────┐
│              列式存储 vs 行式存储对比                        │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  行式存储 (Row-Oriented)：                                   │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  id │ name  │ age │ city    │ amount │                │ │
│  ├─────┼───────┼─────┼─────────┼────────┤                │ │
│  │  1  │ Alice │ 25  │ Beijing │  100   │ ← 一行数据连续存储│ │
│  │  2  │ Bob   │ 30  │ Shanghai│  200   │                │ │
│  │  3  │ Carol │ 28  │ Beijing │  150   │                │ │
│  │  4  │ David │ 35  │ Guangzhou│ 300   │                │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  物理存储：[1,Alice,25,Beijing,100][2,Bob,30,Shanghai,200]...│
│                                                            │
│  特点：                                                     │
│  ├─ 适合事务处理（需要整行）                                 │
│  ├─ 适合点查（根据主键快速定位）                             │ │
│  └─ 分析查询需读取所有列（即使只需几列）                      │ │
│                                                            │
│  ────────────────────────────────────────────────────────  │
│                                                            │
│  列式存储 (Column-Oriented)：                                │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  id: [1, 2, 3, 4]                                     │ │
│  │  name: [Alice, Bob, Carol, David]                     │ │
│  │  age: [25, 30, 28, 35]                                │ │
│  │  city: [Beijing, Shanghai, Beijing, Guangzhou]        │ │
│  │  amount: [100, 200, 150, 300]                         │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  物理存储：                                                  │
│  ├─ id.bin: 1,2,3,4                                       │ │
│  ├─ name.bin: Alice,Bob,Carol,David                       │ │
│  ├─ age.bin: 25,30,28,35                                  │ │
│  ├─ city.bin: Beijing,Shanghai,Beijing,Guangzhou          │ │
│  └─ amount.bin: 100,200,150,300                           │ │
│                                                            │
│  特点：                                                     │
│  ├─ 分析查询只需读取所需列                                   │ │
│  ├─ 同类型数据连续存储，压缩率高                              │ │
│  ├─ 向量化执行（SIMD优化）                                   │ │
│  └─ 适合聚合计算（SUM/AVG等）                                │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 ClickHouse架构

```
┌─────────────────────────────────────────────────────────────┐
│                  ClickHouse 架构                             │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                  Client (HTTP/TCP/CLI)                 │ │
│  └───────────────────────────┬───────────────────────────┘ │
│                              │                             │
│  ┌───────────────────────────▼───────────────────────────┐ │
│  │                  Parser & Analyzer                     │ │
│  │  - SQL解析                                             │ │
│  │  - 语法分析                                             │ │
│  │  - 查询优化                                             │ │
│  └───────────────────────────┬───────────────────────────┘ │
│                              │                             │
│  ┌───────────────────────────▼───────────────────────────┐ │
│  │                  Query Executor                        │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌─────────────┐ │ │
│  │  │  Interpreter │  │   Aggregator │  │   Merger    │ │ │
│  │  └──────────────┘  └──────────────┘  └─────────────┘ │ │
│  └───────────────────────────┬───────────────────────────┘ │
│                              │                             │
│  ┌───────────────────────────▼───────────────────────────┐ │
│  │                  Storage Layer                         │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐   │ │
│  │  │ MergeTree   │  │  Log        │  │  Special    │   │ │
│  │  │ ├─ Replacing│  │ ├─ TinyLog  │  │ ├─ Memory   │   │ │
│  │  │ ├─ Summing  │  │ ├─ StripeLog│  │ ├─ File     │   │ │
│  │  │ ├─ Aggregating│ └─────────────┘  │ └─────────────┘   │ │
│  │  │ └─ ...      │                  │                     │ │
│  │  └─────────────┘                  │                     │ │
│  └───────────────────────────────────┼─────────────────────┘ │
│                                      │                       │
│  ┌───────────────────────────────────▼─────────────────────┐ │
│  │                  Distributed (可选)                      │ │
│  │  ┌─────────┐    ┌─────────┐    ┌─────────┐             │ │
│  │  │ Shard 1 │    │ Shard 2 │    │ Shard 3 │             │ │
│  │  │ ├─ Rep  │    │ ├─ Rep  │    │ ├─ Rep  │             │ │
│  │  └─────────┘    └─────────┘    └─────────┘             │ │
│  └─────────────────────────────────────────────────────────┘ │
│                                                            │
│  核心特性：                                                  │
│  ├─ 向量化执行：批量处理数据（每次处理上千行）                │ │
│  ├─ SIMD优化：利用CPU SSE4.2/AVX指令集                      │ │
│  ├─ 数据压缩：LZ4/ZSTD，压缩比可达10:1                      │ │
│  └─ MPP架构：大规模并行处理                                  │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、技术细节

### 2.1 MergeTree存储引擎

```
┌─────────────────────────────────────────────────────────────┐
│                  MergeTree 存储结构                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  数据组织：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  数据库 → 表 → 分区 → 分片 → 粒度 → 列文件              │ │
│  │                                                       │ │
│  │  db.table/                                            │ │
│  │  ├── 202401_1_3_1/      # 分区目录 (partition)         │ │
│  │  │   ├── part_1.bin      # 列数据文件                  │ │
│  │  │   ├── part_2.bin                                │ │
│  │  │   ├── minmax_part.idx # 分区索引                   │ │
│  │  │   └── checksums.txt   # 校验和                     │ │
│  │  ├── 202401_4_6_2/                                  │ │
│  │  └── detached/            # 分离的part                │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  分区目录命名：min_block_max_block_level                     │
│  ├─ min_block: 最小数据块号                                 │
│  ├─ max_block: 最大数据块号                                 │
│  └─ level: 合并次数（0表示新插入）                           │ │
│                                                            │
│  数据写入：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Insert → 内存缓冲区 (max_insert_block_size)          │ │
│  │       ↓                                               │ │
│  │  按分区键排序 → 写入临时part                            │ │
│  │       ↓                                               │ │
│  │  后台Merge → 合并小part为大part                        │ │
│  │       ↓                                               │ │
│  │  旧part标记为inactive，定期清理                         │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  MergeTree变体：                                             │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ ReplacingMergeTree                                    │ │
│  │ ├─ 按排序键去重，保留最新版本                           │ │
│  │ ├─ 去重在Merge时进行，非实时                           │ │
│  │ └─ 需使用FINAL或argMax查询最新                          │ │
│  │                                                       │ │
│  │ SummingMergeTree                                      │ │
│  │ ├─ 合并时数值列自动求和                                 │ │
│  │ └─ 适用于预聚合场景                                     │ │
│  │                                                       │ │
│  │ AggregatingMergeTree                                  │ │
│  │ ├─ 支持更复杂的聚合函数状态                             │ │
│  │ └─ 配合物化视图使用                                     │ │
│  │                                                       │ │
│  │ CollapsingMergeTree / VersionedCollapsingMergeTree   │ │
│  │ └─ 支持数据行折叠（删除/更新语义）                      │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 索引与查询优化

```
┌─────────────────────────────────────────────────────────────┐
│                  ClickHouse 索引机制                         │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  主键/排序键：                                               │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  建表时指定ORDER BY (col1, col2, col3)                 │ │
│  │                                                       │ │
│  │  数据按排序键有序存储：                                 │ │
│  │  ┌──────┬──────┬──────┐                              │ │
│  │  │  A   │  1   │  x   │                              │ │
│  │  │  A   │  2   │  y   │                              │ │
│  │  │  B   │  1   │  z   │                              │ │
│  │  │  B   │  3   │  w   │                              │ │
│  │  │  C   │  2   │  v   │                              │ │
│  │  └──────┴──────┴──────┘                              │ │
│  │                                                       │ │
│  │  稀疏索引（默认8192行一个mark）：                        │ │
│  │  ├─ mark 0: offset 0, 值 (A, 1, x)                    │ │
│  │  ├─ mark 1: offset 8192, 值 (B, 1, z)                 │ │
│  │  └─ mark 2: offset 16384, 值 (C, 2, v)                │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  跳数索引 (Data Skipping Indexes)：                          │ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  CREATE TABLE ...                                     │ │
│  │  ORDER BY (user_id, event_time)                       │ │
│  │  INDEX idx_amount minmax(amount) TYPE minmax GRANULARITY 4 │ │
│  │  INDEX idx_city bloom_filter(city) TYPE bloom_filter GRANULARITY 4 │ │
│  │                                                       │ │
│  │  类型：                                                │ │
│  │  ├─ minmax: 存储每granularity块的最小/最大值          │ │
│  │  ├─ set: 存储唯一值集合（最多限制）                    │ │
│  │  ├─ bloom_filter: 布隆过滤器                          │ │
│  │  └─ tokenbf_v1/ngrambf_v1: 全文搜索索引               │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、实践指南

### 3.1 建表示例

```sql
-- 基础MergeTree表
CREATE TABLE events (
    event_id UInt64,
    user_id UInt64,
    event_type LowCardinality(String),
    event_time DateTime,
    amount Decimal(16, 2),
    properties String CODEC(ZSTD(1))
) ENGINE = MergeTree()
PARTITION BY toYYYYMM(event_time)
ORDER BY (user_id, event_time)
SETTINGS index_granularity = 8192;

-- ReplacingMergeTree（去重）
CREATE TABLE user_states (
    user_id UInt64,
    state String,
    updated_at DateTime,
    version UInt64
) ENGINE = ReplacingMergeTree(version)
PARTITION BY toYYYYMM(updated_at)
ORDER BY user_id;

-- SummingMergeTree（预聚合）
CREATE TABLE daily_stats (
    date Date,
    user_id UInt64,
    impressions UInt64,
    clicks UInt64,
    revenue Decimal(16, 4)
) ENGINE = SummingMergeTree()
PARTITION BY toYYYYMM(date)
ORDER BY (date, user_id);

-- 分布式表
CREATE TABLE events_local ON CLUSTER 'cluster_1' (
    -- 本地表结构
) ENGINE = MergeTree() ...

CREATE TABLE events_distributed ON CLUSTER 'cluster_1' AS events_local
ENGINE = Distributed('cluster_1', 'default', 'events_local', rand());
```

### 3.2 性能优化

```sql
-- 查询优化技巧

-- 1. 使用PREWHERE过滤（先过滤再读取列）
SELECT * FROM events
PREWHERE event_time > '2024-01-01'
WHERE user_id = 123;

-- 2. 采样查询（大数据集快速估算）
SELECT avg(amount) FROM events SAMPLE 0.1;  -- 10%采样

-- 3. 物化视图（预聚合）
CREATE MATERIALIZED VIEW events_agg
ENGINE = SummingMergeTree()
PARTITION BY toYYYYMM(hour)
ORDER BY (hour, event_type)
AS SELECT
    toStartOfHour(event_time) as hour,
    event_type,
    count() as cnt,
    sum(amount) as total_amount
FROM events
GROUP BY hour, event_type;

-- 4. 投影（Projections）
ALTER TABLE events
ADD PROJECTION event_type_stats
(
    SELECT event_type, count(), sum(amount)
    GROUP BY event_type
);
```

### 3.3 最佳实践

```
┌─────────────────────────────────────────────────────────────┐
│                    ClickHouse最佳实践                        │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  1. 表设计：                                                │ │
│  ├─ 选择合适的数据类型（UInt64 vs UInt32）                  │ │
│  ├─ 使用LowCardinality优化枚举列                            │ │
│  ├─ 字符串考虑使用CODEC(ZSTD)压缩                           │ │
│  └─ 大字段（text/blob）谨慎使用                             │ │
│                                                            │
│  2. 分区策略：                                              │ │
│  ├─ 分区数不宜过多（<1000）                                 │ │
│  ├─ 时间序列数据按toYYYYMMDD或toYYYYMM                     │ │
│  └─ 定期删除旧分区（比DELETE快得多）                        │ │
│                                                            │
│  3. 写入优化：                                              │ │
│  ├─ 批量写入（每次>10000行）                                │ │
│  ├─ 避免小文件（Too many parts错误）                        │ │
│  └─ 使用异步插入（async_insert）                            │ │
│                                                            │
│  4. 查询优化：                                              │ │
│  ├─ 避免SELECT *，只取需要的列                              │ │
│  ├─ WHERE条件尽量包含分区键和排序键前缀                     │ │
│  ├─ 大结果集使用LIMIT限制                                   │ │
│  └─ 使用FINAL谨慎（性能开销大）                             │ │
│                                                            │
│  5. 分布式注意事项：                                        │ │
│  ├─ 分布式表只负责路由，本地表存储数据                      │ │
│  ├─ 多副本使用ReplicatedMergeTree                           │ │
│  └─ 跨分片查询避免高开销操作（如GLOBAL JOIN）               │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、常见问题

**Q1: ClickHouse为什么不支持事务？**
A: 设计目标为分析型数据库，追求极致查询性能而非事务能力。使用MergeTree的合并机制保证最终一致性。

**Q2: 如何模拟UPDATE/DELETE？**
A: 使用ALTER TABLE ... UPDATE（异步重写作业）或CollapsingMergeTree进行标记删除。

**Q3: 单节点性能瓶颈如何处理？**
A: 1) 优化查询；2) 增加内存；3) 使用物化视图；4) 分布式集群扩展。

**Q4: 如何导入大批量历史数据？**
A: 使用clickhouse-client --query="INSERT INTO ... FORMAT CSV" < data.csv，或利用s3表函数直接读取对象存储。

---

## 五、与其他主题的关联

### 5.1 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| Presto | 对比 | 联邦查询 vs 专用OLAP |
| Druid | 对比 | 实时摄取能力对比 |
| 列式存储 | 基础 | OLAP核心特性 |

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
