# Apache Iceberg 数据湖表格式深度解析

**文档版本**：v1.0
**创建时间**：2026年4月
**最后更新**：2026年4月
**状态**：✅ 已完成

---

## 📋 执行摘要

Apache Iceberg是一种开源的表格式标准，专为大规模分析数据集设计。它在Parquet、ORC等数据格式之上提供了一种表抽象，支持模式演化、时间旅行查询和分区演进等高级功能。Iceberg由Netflix开源，现已成为数据湖架构的事实标准之一，被Apache Spark、Flink、Trino等主流计算引擎广泛支持。

---

## 一、核心架构设计

### 1.1 表格式分层模型

Iceberg通过元数据层将表抽象与底层存储分离，实现了数据与元数据的分离管理。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg 表格式分层架构                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Layer 3: 查询层 (计算引擎)                                                   │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐       │
│  │   Apache    │  │   Apache    │  │    Trino    │  │   Dremio    │       │
│  │   Spark     │  │   Flink     │  │   (Presto)  │  │             │       │
│  │             │  │             │  │             │  │             │       │
│  │ Spark SQL   │  │ SQL/DataStream│  │ ANSI SQL  │  │ SQL+REST    │       │
│  │ DataFrame   │  │ Table API   │  │             │  │             │       │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘       │
│         │                │                │                │              │
│         └────────────────┴────────────────┴────────────────┘              │
│                              ↓                                            │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │  Layer 2: Iceberg Catalog (表元数据管理)                               │ │
│  │                                                                       │ │
│  │  ┌───────────────────────────────────────────────────────────────┐   │ │
│  │  │                    Iceberg Catalog API                        │   │ │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │   │ │
│  │  │  │  Hive Meta  │  │  AWS Glue   │  │  JDBC/RDBMS Catalog │   │   │ │
│  │  │  │    store    │  │   Catalog   │  │                     │   │   │ │
│  │  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │   │ │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │   │ │
│  │  │  │  Hadoop     │  │  REST       │  │  Nessie (Git-like)  │   │   │ │
│  │  │  │  Catalog    │  │  Catalog    │  │                     │   │   │ │
│  │  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │   │ │
│  │  └───────────────────────────────────────────────────────────────┘   │ │
│  │                                                                       │ │
│  │  职责: 表发现、Schema管理、快照管理、锁管理                               │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                              ↓                                            │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │  Layer 1: Iceberg Metadata (元数据层)                                  │ │
│  │                                                                       │ │
│  │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐               │ │
│  │  │  Metadata   │    │  Metadata   │    │  Metadata   │               │ │
│  │  │  File (v1)  │───►│  File (v2)  │───►│  File (vN)  │               │ │
│  │  │             │    │             │    │             │               │ │
│  │  │ • Schema    │    │ • Schema    │    │ • Schema    │               │ │
│  │  │ • Partition │    │ • Partition │    │ • Partition │               │ │
│  │  │ • Snapshots │    │ • Snapshots │    │ • Snapshots │               │ │
│  │  │ • Properties│    │ • Properties│    │ • Properties│               │ │
│  │  └─────────────┘    └─────────────┘    └─────────────┘               │ │
│  │       │                  │                  │                         │ │
│  │       └──► Manifest List ◄─────────────────┘                         │ │
│  │               │                                                       │ │
│  │               └──► Manifest File                                      │ │
│  │                      │                                                │ │
│  │                      └──► Data Files                                  │ │
│  │                                                                       │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                              ↓                                            │
│  ┌───────────────────────────────────────────────────────────────────────┐ │
│  │  Layer 0: Data Layer (数据层)                                          │ │
│  │                                                                       │ │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐       │ │
│  │  │  Data File 1    │  │  Data File 2    │  │  Data File N    │       │ │
│  │  │  (Parquet)      │  │  (Parquet)      │  │  (Parquet)      │       │ │
│  │  │                 │  │                 │  │                 │       │ │
│  │  │ • Column stats  │  │ • Column stats  │  │ • Column stats  │       │ │
│  │  │ • Row groups    │  │ • Row groups    │  │ • Row groups    │       │ │
│  │  │ • Dictionary    │  │ • Dictionary    │  │ • Dictionary    │       │ │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘       │ │
│  │                                                                       │ │
│  │  底层存储: S3 / HDFS / GCS / Azure Blob / 本地文件系统                    │ │
│  │                                                                       │ │
│  └───────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.2 元数据文件组织结构

Iceberg的元数据文件采用层次化组织，支持高效的元数据操作。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg 元数据文件层次结构                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   表目录结构 (以Hive Catalog为例):                                           │
│                                                                             │
│   warehouse/                                                                 │
│   └── database.db/                                                           │
│       └── table/                                                             │
│           ├── metadata/                      ← 元数据目录                    │
│           │   ├── 00001-aaa.metadata.json   ← 元数据文件 v1                  │
│           │   ├── 00002-bbb.metadata.json   ← 元数据文件 v2                  │
│           │   ├── 00003-ccc.metadata.json   ← 元数据文件 v3 (当前)           │
│           │   ├── snap-aaa.avro             ← Manifest List                  │
│           │   ├── snap-bbb.avro             ← Manifest List                  │
│           │   ├── snap-ccc.avro             ← Manifest List (当前)           │
│           │   ├── d8f9-abc.avro             ← Manifest File                  │
│           │   ├── e0a1-def.avro             ← Manifest File                  │
│           │   └── ...                                                          │
│           └── data/                          ← 数据目录                      │
│               ├── 00000-1-abc.parquet       ← 数据文件                       │
│               ├── 00001-2-def.parquet       ← 数据文件                       │
│               └── ...                                                          │
│                                                                             │
│   元数据文件内容详解:                                                         │
│                                                                             │
│   1. Metadata JSON (表的总体信息)                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ {                                                                    │   │
│   │   "format-version": 2,                                               │   │
│   │   "table-uuid": "fb072c92-a02b-11e9-ae9c-...",                       │   │
│   │   "location": "s3://bucket/db/table",                               │   │
│   │   "last-updated-ms": 1515100955770,                                 │   │
│   │   "last-column-id": 3,                                              │   │
│   │   "schema": {                                                        │   │
│   │     "type": "struct",                                                │   │
│   │     "fields": [                                                      │   │
│   │       {"id": 1, "name": "id", "type": "long"},                      │   │
│   │       {"id": 2, "name": "data", "type": "string"},                  │   │
│   │       {"id": 3, "name": "category", "type": "string"}               │   │
│   │     ]                                                                │   │
│   │   },                                                                 │   │
│   │   "partition-spec": [...],                                           │   │
│   │   "snapshots": [                                                     │   │
│   │     {                                                                │   │
│   │       "snapshot-id": 3055729675574597004,                            │   │
│   │       "timestamp-ms": 1515100955770,                                 │   │
│   │       "manifest-list": "s3://bucket/db/table/metadata/snap-ccc.avro" │   │
│   │     }                                                                │   │
│   │   ],                                                                 │   │
│   │   "current-snapshot-id": 3055729675574597004                         │   │
│   │ }                                                                    │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. Manifest List (快照级别的清单列表)                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ Avro格式, 包含该快照下的所有Manifest文件信息                          │   │
│   │                                                                     │   │
│   │ 字段:                                                               │   │
│   │ - manifest_path: Manifest文件路径                                   │   │
│   │ - manifest_length: 文件大小                                         │   │
│   │ - partition_spec_id: 分区规范ID                                     │   │
│   │ - added_snapshot_id: 添加快照ID                                     │   │
│   │ - added_data_files_count: 新增文件数                                │   │
│   │ - existing_data_files_count: 现有文件数                             │   │
│   │ - deleted_data_files_count: 删除文件数                              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. Manifest File (数据文件清单)                                           │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │ Avro格式, 包含实际数据文件的详细信息                                  │   │
│   │                                                                     │   │
│   │ 每个数据文件记录:                                                    │   │
│   │ - status: ADDED(1) / EXISTING(0) / DELETED(2)                       │   │
│   │ - data_file:                                                        │   │
│   │   - file_path: 数据文件路径                                         │   │
│   │   - file_format: PARQUET / ORC / AVRO                               │   │
│   │   - partition: 分区值                                               │   │
│   │   - record_count: 记录数                                            │   │
│   │   - file_size_in_bytes: 文件大小                                    │   │
│   │   - column_sizes: 每列大小统计                                      │   │
│   │   - value_counts: 每列值数量                                        │   │
│   │   - null_value_counts: 每列null数量                                 │   │
│   │   - lower_bounds: 每列最小值                                        │   │
│   │   - upper_bounds: 每列最大值                                        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 二、模式演化 (Schema Evolution)

### 2.1 支持的Schema变更

Iceberg通过列ID而非列名来追踪Schema变化，支持安全的模式演化。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg 模式演化机制                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Schema v1 (初始):                                                          │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  Column ID    │  Column Name  │  Data Type  │  Transform            │   │
│   ├───────────────┼───────────────┼─────────────┼───────────────────────┤   │
│   │      1        │      id       │    long     │                       │   │
│   │      2        │     data      │   string    │                       │   │
│   │      3        │    category   │   string    │                       │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Schema v2 (添加列 + 重命名):                                                │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │      1        │      id       │    long     │                       │   │
│   │      2        │     info      │   string    │  ← 重命名 (data→info)  │   │
│   │      3        │    category   │   string    │                       │   │
│   │      4        │  created_at   │  timestamp  │  ← 新增列              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Schema v3 (修改类型):                                                       │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │      1        │      id       │    long     │                       │   │
│   │      2        │     info      │   string    │                       │   │
│   │      3        │    category   │   string    │                       │   │
│   │      4        │  created_at   │  timestamp  │                       │   │
│   │      5        │    amount     │  decimal(10,2)│ ← 新增, 支持精度调整 │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   支持的Schema变更类型:                                                        │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  操作类型          │  是否支持  │  说明                              │   │
│   ├────────────────────┼────────────┼────────────────────────────────────┤   │
│   │  添加列            │     ✅     │  新列默认值为null                   │   │
│   │  删除列            │     ✅     │  列ID被标记为已删除, 但数据保留      │   │
│   │  重命名列          │     ✅     │  仅名称变化, 列ID不变               │   │
│   │  修改列顺序        │     ✅     │  不影响存储                         │   │
│   │  扩大类型(如int→long)│   ✅     │  安全类型提升                       │   │
│   │  缩小类型          │     ❌     │  可能导致数据丢失                    │   │
│   │  修改列nullability │   ⚠️      │  需谨慎处理null值                   │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   与Hive/Parquet对比:                                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  场景              │ Hive表格式      │ Iceberg                       │   │
│   ├────────────────────┼─────────────────┼───────────────────────────────┤   │
│   │  添加列后旧数据读取 │ 可能失败/错位   │ 自动填充null, 按列ID读取       │   │
│   │  删除列后读取       │ 失败            │ 正常工作, 被删列不可见         │   │
│   │  重命名列           │ 视为新列        │ 正常工作, 历史数据可读         │   │
│   │  修改类型           │ 失败            │ 安全类型提升支持               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 分区演进 (Partition Evolution)

Iceberg支持分区方案的演进，无需重写历史数据。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg 分区演进机制                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   分区演进示例:                                                              │
│                                                                             │
│   Snapshot 1 (按天分区):                                                     │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  分区规范 ID: 0                                                     │   │
│   │  分区列: day(event_time)                                            │   │
│   │                                                                     │   │
│   │  数据布局:                                                           │   │
│   │  data/event_time_day=2023-01-01/*.parquet                           │   │
│   │  data/event_time_day=2023-01-02/*.parquet                           │   │
│   │  data/event_time_day=2023-01-03/*.parquet                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Snapshot 2 (改为按小时分区 - 分区演进):                                     │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  分区规范 ID: 1 (新规范)                                             │   │
│   │  分区列: hour(event_time), category                                  │   │
│   │                                                                     │   │
│   │  数据布局 (新写入的数据):                                             │   │
│   │  data/event_time_hour=2023-01-04-00/category=A/*.parquet            │   │
│   │  data/event_time_hour=2023-01-04-00/category=B/*.parquet            │   │
│   │  data/event_time_hour=2023-01-04-01/category=A/*.parquet            │   │
│   │                                                                     │   │
│   │  历史数据保持原分区布局 (无需重写)                                     │   │
│   │  data/event_time_day=2023-01-01/*.parquet                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   查询时的分区剪枝:                                                           │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                                                                     │   │
│   │  SELECT * FROM events                                               │   │
│   │  WHERE event_time >= '2023-01-01'                                   │   │
│   │    AND event_time < '2023-01-05'                                    │   │
│   │                                                                     │   │
│   │  Iceberg自动识别:                                                    │   │
│   │  • 2023-01-01 ~ 2023-01-03: 使用分区规范0, 按天扫描                   │   │
│   │  • 2023-01-04: 使用分区规范1, 按小时扫描                              │   │
│   │                                                                     │   │
│   │  无需用户关心分区方案变化!                                             │   │
│   │                                                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   隐藏分区 (Hidden Partitioning):                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                                                                     │   │
│   │  传统分区 (Hive):                                                    │   │
│   │  SELECT * FROM events                                               │   │
│   │  WHERE event_time_day = '2023-01-01'  ← 用户必须知道分区列名         │   │
│   │                                                                     │   │
│   │  Iceberg隐藏分区:                                                    │   │
│   │  SELECT * FROM events                                               │   │
│   │  WHERE event_time >= '2023-01-01'     ← 使用原始列, 自动分区剪枝     │   │
│   │    AND event_time < '2023-01-02'                                    │   │
│   │                                                                     │   │
│   │  Iceberg自动将过滤器转换为分区规范对应的值:                             │   │
│   │  - bucket(16, user_id) → user_id % 16                              │   │
│   │  - days(event_time) → days since epoch                             │   │
│   │  - truncate(10, category) → 前缀截取                                │   │
│   │                                                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 三、时间旅行查询

### 3.1 快照隔离与版本控制

Iceberg的快照机制提供了强大的时间旅行能力。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg 时间旅行机制                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   快照时间线:                                                                │
│                                                                             │
│   时间 →                                                                    │
│                                                                             │
│   T0          T1          T2          T3          T4          T5            │
│   │           │           │           │           │           │            │
│   ▼           ▼           ▼           ▼           ▼           ▼            │
│ ┌───┐       ┌───┐       ┌───┐       ┌───┐       ┌───┐       ┌───┐        │
│ │S0 │──────►│S1 │──────►│S2 │──────►│S3 │──────►│S4 │──────►│S5 │        │
│ └───┘       └───┘       └───┘       └───┘       └───┘       └───┘        │
│              │                       │                       │            │
│           插入1K                    删除500                  更新200       │
│           记录                      记录                     记录          │
│                                                                             │
│   时间旅行查询示例:                                                           │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  -- 查询最新数据 (默认)                                              │   │
│   │  SELECT * FROM events;                                              │   │
│   │                                                                     │   │
│   │  -- 查询特定时间点的数据                                             │   │
│   │  SELECT * FROM events                                               │   │
│   │  FOR SYSTEM_TIME AS OF TIMESTAMP '2023-01-15 10:00:00';             │   │
│   │                                                                     │   │
│   │  -- 查询特定快照ID                                                   │   │
│   │  SELECT * FROM events                                               │   │
│   │  FOR SYSTEM_VERSION AS OF 3055729675574597004;                      │   │
│   │                                                                     │   │
│   │  -- Spark SQL语法                                                    │   │
│   │  spark.read                                                      │   │
│   │    .option("snapshot-id", 3055729675574597004)                      │   │
│   │    .table("events")                                                 │   │
│   │                                                                     │   │
│   │  -- 查询10分钟前的数据                                               │   │
│   │  SELECT * FROM events                                               │   │
│   │  FOR SYSTEM_TIME AS OF NOW() - INTERVAL '10' MINUTE;                │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   快照管理操作:                                                               │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │  -- 查看表历史                                                        │   │
│   │  SELECT * FROM db.table.history;                                    │   │
│   │                                                                     │   │
│   │  -- 查看快照详情                                                      │   │
│   │  SELECT * FROM db.table.snapshots;                                  │   │
│   │                                                                     │   │
│   │  -- 回滚到特定快照 (撤销更改)                                          │   │
│   │  CALL system.rollback_to_snapshot('db.table', 3055729675574597004); │   │
│   │                                                                     │   │
│   │  -- 创建分支 (实验性功能)                                              │   │
│   │  ALTER TABLE db.table CREATE BRANCH testing                         │   │
│   │    AS OF VERSION 3055729675574597004;                               │   │
│   │                                                                     │   │
│   │  -- 清理过期快照 (维护操作)                                            │   │
│   │  CALL system.expire_snapshots('db.table',                           │   │
│   │    TIMESTAMP '2023-01-01 00:00:00.000');                            │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 四、Iceberg vs Delta Lake 对比

### 4.1 功能特性对比

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Iceberg vs Delta Lake 对比                               │
├─────────────────────────────────────────────────────────────────────────────┤
│  特性                  │ Apache Iceberg          │ Delta Lake              │
├─────────────────────────────────────────────────────────────────────────────┤
│  开源协议              │ Apache 2.0              │ Apache 2.0              │
│  发源地                │ Netflix                 │ Databricks              │
│  首发布                │ 2018                    │ 2019                    │
├─────────────────────────────────────────────────────────────────────────────┤
│  存储格式              │ Parquet/ORC/Avro        │ Parquet                 │
│  元数据格式            │ JSON + Avro             │ JSON                    │
│  表格式规范            │ 开放规范, 多实现         │ 单一实现                │
├─────────────────────────────────────────────────────────────────────────────┤
│  Schema演进            │ ✅ 完整支持              │ ✅ 支持                 │
│  分区演进              │ ✅ 支持                  │ ⚠️ 有限支持             │
│  隐藏分区              │ ✅ 支持                  │ ❌ 不支持               │
│  时间旅行              │ ✅ 完整支持              │ ✅ 支持                 │
│  增量读取              │ ✅ 支持                  │ ✅ 支持                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  Spark支持             │ ✅ 原生支持              │ ✅ 原生支持             │
│  Flink支持             │ ✅ 原生支持              │ ⚠️ 社区支持             │
│  Trino/Presto支持      │ ✅ 原生支持              │ ⚠️ 社区支持             │
│  Hive支持              │ ✅ 原生支持              │ ❌ 不支持               │
│  Flink CDC             │ ✅ 支持                  │ ⚠️ 有限                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  视图支持              │ ✅ 支持                  │ ❌ 不支持               │
│  分支/标签             │ ✅ 支持 (v2)             │ ❌ 不支持               │
│  统计信息              │ ✅ 详细列级统计          │ ✅ 文件级统计           │
│  行级更新              │ ✅ MERGE INTO           │ ✅ MERGE INTO           │
│  删除向量              │ ⚠️ 有限                  │ ✅ 支持                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  云端服务              │                                                         │
│  - AWS                │ EMR, Athena, Glue       │ Databricks, Glue        │
│  - GCP                │ BigLake                 │ BigQuery                │
│  - Azure              │ Synapse                 │ Databricks, Fabric      │
│  - Snowflake          ✅ 原生支持              │ ❌ 不支持               │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 4.2 性能对比

| 场景 | Iceberg | Delta Lake | 说明 |
|------|---------|-----------|------|
| 小文件查询 | 更快 | 较慢 | Iceberg的元数据设计更高效 |
| 模式演进查询 | 更快 | 相当 | Iceberg的列ID追踪更优 |
| 分区剪枝 | 更灵活 | 基础 | Iceberg支持分区演进 |
| 并发写入 | 更好 | 良好 | Iceberg的乐观并发控制 |
| 元数据操作 | 更快 | 较慢 | Iceberg的清单分层设计 |

---

## 五、配置与使用

### 5.1 Spark集成配置

```python
# spark-iceberg-config.py
from pyspark.sql import SparkSession

spark = SparkSession.builder \
    .appName("IcebergDemo") \
    .config("spark.sql.extensions", "org.apache.iceberg.spark.extensions.IcebergSparkSessionExtensions") \
    .config("spark.sql.catalog.spark_catalog", "org.apache.iceberg.spark.SparkSessionCatalog") \
    .config("spark.sql.catalog.spark_catalog.type", "hive") \
    .config("spark.sql.catalog.local", "org.apache.iceberg.spark.SparkCatalog") \
    .config("spark.sql.catalog.local.type", "hadoop") \
    .config("spark.sql.catalog.local.warehouse", "warehouse") \
    .config("spark.sql.defaultCatalog", "local") \
    .getOrCreate()

# 创建Iceberg表
spark.sql("""
CREATE TABLE IF NOT EXISTS local.db.events (
    id BIGINT,
    event_time TIMESTAMP,
    user_id STRING,
    category STRING,
    amount DECIMAL(10,2)
)
USING iceberg
PARTITIONED BY (days(event_time), bucket(16, user_id))
TBLPROPERTIES (
    'write_compression' = 'zstd',
    'commit.manifest.min-count-to-merge' = '5'
)
""")

# 写入数据
spark.sql("""
INSERT INTO local.db.events
VALUES
    (1, TIMESTAMP '2024-01-15 10:00:00', 'user1', 'A', 100.50),
    (2, TIMESTAMP '2024-01-15 11:00:00', 'user2', 'B', 200.00)
""")

# 时间旅行查询
spark.sql("""
SELECT * FROM local.db.events TIMESTAMP AS OF '2024-01-15 10:00:00'
""").show()

# 查看表历史
spark.sql("SELECT * FROM local.db.events.history").show()

# 查看快照
spark.sql("SELECT * FROM local.db.events.snapshots").show()

# 数据优化 (合并小文件)
spark.sql("CALL local.system.rewrite_data_files('db.events')")
```

### 5.2 Flink集成配置

```java
// Flink Iceberg Sink配置
StreamExecutionEnvironment env = StreamExecutionEnvironment.getExecutionEnvironment();
env.enableCheckpointing(60000);

// Iceberg Catalog配置
Map<String, String> properties = new HashMap<>();
properties.put("type", "iceberg");
properties.put("catalog-type", "hadoop");
properties.put("warehouse", "s3://bucket/warehouse");

CatalogLoader catalogLoader = CatalogLoader.load("iceberg_catalog", new Configuration(), properties);

// 创建Flink Table
TableLoader tableLoader = TableLoader.fromHadoopTable("s3://bucket/warehouse/db/table", new Configuration());

// Flink DataStream写入Iceberg
DataStream<Row> stream = env.addSource(new KafkaSource<>());

FlinkSink.forRowData(stream)
    .tableLoader(tableLoader)
    .equalityFieldColumns(Arrays.asList("id"))
    .upsert(true)
    .build();
```

### 5.3 维护操作

```sql
-- 1. 小文件合并
CALL local.system.rewrite_data_files(
    table => 'db.table',
    options => map('min-input-files', '5', 'target-file-size-bytes', '536870912')
);

-- 2. 过期快照清理
CALL local.system.expire_snapshots(
    table => 'db.table',
    older_than => TIMESTAMP '2024-01-01 00:00:00.000',
    retain_last => 5
);

-- 3. 删除孤立文件
CALL local.system.remove_orphan_files(
    table => 'db.table',
    older_than => TIMESTAMP '2024-01-01 00:00:00.000'
);

-- 4. 重写Manifest
CALL local.system.rewrite_manifests('db.table');
```

---

## 六、总结

Apache Iceberg通过创新的表格式设计，解决了传统数据湖的多个痛点：

1. **模式演化**：安全的Schema变更，历史数据兼容
2. **分区演进**：灵活的分区策略变更，无需重写数据
3. **时间旅行**：完整的快照历史和回滚能力
4. **计算引擎无关**：Spark、Flink、Trino等统一支持

Iceberg是构建现代数据湖架构的首选表格式之一。

---

**参考资源**：

- [Apache Iceberg官方文档](https://iceberg.apache.org/)
- [Iceberg GitHub](https://github.com/apache/iceberg)
- [Iceberg Table Spec](https://iceberg.apache.org/spec/)
