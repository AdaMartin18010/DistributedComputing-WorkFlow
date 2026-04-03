# Spark Structured Streaming 详解

## 1. 架构概述

Spark Structured Streaming 是基于 Spark SQL 引擎构建的可扩展、容错的流处理引擎。它将流计算抽象为对无限输入表的增量查询，简化了流处理编程模型。

```
┌─────────────────────────────────────────────────────────────────────┐
│           Spark Structured Streaming 架构                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    编程模型：无限表抽象                          │ │
│  │                                                               │ │
│  │    输入流          查询          结果                          │ │
│  │   ┌────┐      ┌─────────┐    ┌────────┐                      │ │
│  │   │ ▲  │      │ SELECT  │    │  ▲     │                      │ │
│  │   │ │  │  ──▶ │  WHERE  │──▶ │  │     │                      │ │
│  │   │ │  │      │ GROUP BY│    │  │     │                      │ │
│  │   └──┼─┘      └─────────┘    └──┼─────┘                      │ │
│  │      │                          │                            │ │
│  │      └──────────────────────────┘                            │ │
│  │              新数据触发增量计算                                │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    执行引擎：微批模式 / 连续处理                 │ │
│  │                                                               │ │
│  │   微批模式 (Micro-batch)         连续处理 (Continuous)        │ │
│  │   ┌─────────────────────┐       ┌─────────────────────┐      │ │
│  │   │ Trigger: 1 second   │       │ Trigger: Continuous │      │ │
│  │   │ ┌───┐ ┌───┐ ┌───┐  │       │  ─────────────────▶  │      │ │
│  │   │ │Batch│Batch│Batch│ │       │  毫秒级延迟          │      │ │
│  │   │ │ 1  │  2  │  3  │ │       │                     │      │ │
│  │   │ └───┘ └───┘ └───┘  │       │  实验性功能          │      │ │
│  │   └─────────────────────┘       └─────────────────────┘      │ │
│  │                                                               │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心组件

| 组件 | 职责 |
|------|------|
| **Source** | 数据输入（Kafka、文件、Socket 等） |
| **Transformation** | 数据处理（Spark SQL / DataFrame API） |
| **Sink** | 数据输出（Kafka、文件、Console 等） |
| **Checkpoint** | 容错和状态恢复 |
| **Watermark** | 处理乱序数据和迟到数据 |

## 2. 快速开始

### 2.1 Python API

```python
from pyspark.sql import SparkSession
from pyspark.sql.functions import explode, split, window, col

# 创建 SparkSession
spark = SparkSession.builder \
    .appName("StructuredStreaming") \
    .getOrCreate()

# 读取流数据
lines = spark.readStream \
    .format("socket") \
    .option("host", "localhost") \
    .option("port", 9999) \
    .load()

# 处理数据
words = lines.select(
    explode(split(lines.value, " ")).alias("word")
)
wordCounts = words.groupBy("word").count()

# 输出结果
query = wordCounts.writeStream \
    .outputMode("complete") \
    .format("console") \
    .start()

query.awaitTermination()
```

### 2.2 Scala API

```scala
import org.apache.spark.sql.SparkSession
import org.apache.spark.sql.functions._

val spark = SparkSession.builder
    .appName("StructuredStreaming")
    .getOrCreate()

import spark.implicits._

// 读取 Kafka 流
val df = spark.readStream
    .format("kafka")
    .option("kafka.bootstrap.servers", "localhost:9092")
    .option("subscribe", "topic1")
    .option("startingOffsets", "latest")
    .load()

// 解析 JSON
val parsed = df.selectExpr("CAST(value AS STRING)")
    .select(from_json($"value", schema).as("data"))
    .select("data.*")

// 窗口聚合
val windowedCounts = parsed
    .withWatermark("timestamp", "10 minutes")
    .groupBy(
        window($"timestamp", "5 minutes", "1 minute"),
        $"action"
    )
    .count()

// 输出到 Kafka
val query = windowedCounts.writeStream
    .format("kafka")
    .option("kafka.bootstrap.servers", "localhost:9092")
    .option("topic", "output-topic")
    .option("checkpointLocation", "/path/to/checkpoint")
    .outputMode("update")
    .start()

query.awaitTermination()
```

## 3. 输入源（Sources）

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Structured Streaming Sources                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────┐ │
│  │   Kafka     │  │   Files     │  │   Socket    │  │   Rate     │ │
│  │             │  │             │  │             │  │            │ │
│  │  - 高吞吐   │  │  - CSV/JSON │  │  - 测试用   │  │ - 测试用   │ │
│  │  - 容错性   │  │  - Parquet  │  │  - 无容错   │  │ - 自动生成 │ │ │
│  │  -  exactly-│  │  - ORC      │  │             │  │            │ │
│  │    once    │  │  - 自动发现 │  │             │  │            │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.1 Kafka Source 详解

```python
# Kafka Source 配置
df = spark.readStream \
    .format("kafka") \
    .option("kafka.bootstrap.servers", "host1:9092,host2:9092") \
    .option("subscribe", "topic1,topic2") \
    .option("startingOffsets", "latest") \
    .option("minPartitions", "10") \
    .option("maxOffsetsPerTrigger", "10000") \
    .option("kafka.security.protocol", "SASL_SSL") \
    .option("kafka.sasl.mechanism", "PLAIN") \
    .load()

# 解析消息结构
from pyspark.sql.types import StructType, StringType, TimestampType

schema = StructType() \
    .add("user_id", StringType()) \
    .add("event_type", StringType()) \
    .add("timestamp", TimestampType()) \
    .add("properties", StringType())

parsed_df = df.selectExpr("CAST(key AS STRING)", "CAST(value AS STRING)") \
    .select(from_json(col("value"), schema).alias("data")) \
    .select("data.*")
```

### 3.2 File Source

```python
# 文件流处理
schema = "name STRING, age INT, city STRING"

df = spark.readStream \
    .schema(schema) \
    .option("maxFilesPerTrigger", 1) \
    .json("/path/to/input/")

# 支持格式：json, csv, parquet, orc, text
```

## 4. 输出模式（Output Modes）

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Output Modes 对比                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Append Mode                    Complete Mode                      │
│  (仅输出新增行)                  (输出完整结果表)                     │
│                                                                     │
│  ┌───────┐  ┌───────┐          ┌─────────────┐  ┌─────────────┐   │
│  │Batch 1│  │Batch 2│          │  Result 1   │  │  Result 2   │   │
│  │ a:1   │  │ a:1   │          │  a:1, b:2   │  │  a:2, b:2   │   │
│  │ b:2   │  │       │          │             │  │  c:3        │   │
│  └───────┘  │ a:1   │          └─────────────┘  └─────────────┘   │
│             │ c:3   │                                               │
│             └───────┘                                               │
│                                                                     │
│  Update Mode                                                        │
│  (仅输出更新的行)                                                    │
│                                                                     │
│  ┌───────┐  ┌───────┐                                              │
│  │Batch 1│  │Batch 2│                                              │
│  │ a:1   │  │ a:2   │  ← 仅输出 a:2 (变更的行)                      │
│  │ b:2   │  │       │                                              │
│  └───────┘  │ c:3   │  ← 仅输出 c:3 (新增的行)                      │
│             └───────┘                                              │
│                                                                     │
│  支持情况：                                                         │
│  - Append: 无聚合查询 (select, filter, map)                         │
│  - Complete: 有聚合查询 (groupBy, agg)                              │
│  - Update: 有聚合查询，Sink 支持更新                                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```python
# Append Mode - 仅输出新行
query = df.writeStream \
    .outputMode("append") \
    .format("parquet") \
    .start()

# Complete Mode - 输出完整结果
query = aggregated_df.writeStream \
    .outputMode("complete") \
    .format("console") \
    .start()

# Update Mode - 仅输出变更
query = aggregated_df.writeStream \
    .outputMode("update") \
    .format("kafka") \
    .start()
```

## 5. 窗口操作

```
┌─────────────────────────────────────────────────────────────────────┐
│                   窗口类型对比                                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Tumbling Window (滚动窗口)     Sliding Window (滑动窗口)          │
│                                                                     │
│  ┌───┐ ┌───┐ ┌───┐ ┌───┐       ┌───────┐ ┌───────┐ ┌───────┐      │
│  │W1 │ │W2 │ │W3 │ │W4 │       │ W1    │ │ W2    │ │ W3    │      │
│  │0-5│ │5-10││10-│ │15-│       │ 0-10  │ │ 5-15  │ │ 10-20 │      │
│  │   │ │   │ │ 15│ │ 20│       └───────┘ └───────┘ └───────┘      │
│  └───┘ └───┘ └───┘ └───┘          窗口大小 10s, 滑动间隔 5s         │
│   窗口大小 5s, 无重叠                                               │
│                                                                     │
│  Session Window (会话窗口)                                         │
│                                                                     │
│  ┌─────────┐     ┌─────────────────┐                               │
│  │Session 1│     │    Session 2    │                               │
│  │ 0-5s    │gap  │     15-25s      │                               │
│  └─────────┘ 10s └─────────────────┘                               │
│           数据间隔超过 10s 触发新窗口                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 5.1 窗口聚合示例

```python
from pyspark.sql.functions import window, count, sum

# 滚动窗口
windowedCounts = events \
    .withWatermark("timestamp", "10 minutes") \
    .groupBy(
        window(events.timestamp, "10 minutes", "5 minutes"),
        events.action
    ) \
    .count()

# 会话窗口
sessionCounts = events \
    .withWatermark("timestamp", "10 minutes") \
    .groupBy(
        session_window(events.timestamp, "5 minutes"),
        events.user_id
    ) \
    .agg(count("*").alias("event_count"))
```

## 6. Watermark 与迟到数据处理

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Watermark 机制                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Time ──────────────────────────────────────────────────▶           │
│                                                                     │
│  Max Event Time: 12:00:00                                           │
│  Watermark:      11:55:00  (Max Event Time - 5 min delay)          │
│                                                                     │
│  事件时间轴：                                                        │
│  ──────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬─────┬──────     │
│       11:50 11:52 11:54 11:56 11:58 12:00 12:02 12:04 12:06        │
│        │     │     │     │     │     │     │     │     │          │
│  数据   ■     ■     ■     ■     ■     ■     □     □     □          │
│        │     │     │     │     │     │     │     │     │          │
│  Watermark ─────────────────────────▶                               │
│        │           │           │     │     │                       │
│        ▼           ▼           ▼     ▼     ▼                       │
│      11:45       11:50       11:55 12:00  关闭11:55前的窗口         │
│                                                                     │
│  ■ = 正常处理    □ = 可能丢弃 (取决于 watermark 策略)                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```python
# Watermark 配置
watermarked_df = events \
    .withWatermark("timestamp", "10 minutes") \
    .groupBy(
        window("timestamp", "5 minutes"),
        "user_id"
    ) \
    .count()

# 多种 Watermark 策略
from pyspark.sql.functions import current_timestamp

# 固定延迟
.withWatermark("timestamp", "10 minutes")

# 根据数据动态调整 (需要自定义 UDF)
.withWatermark("timestamp", "10 minutes") \
    .dropDuplicates("event_id", "timestamp")  # 去重
```

## 7. 容错与 Checkpoint

```python
# Checkpoint 配置
spark.conf.set("spark.sql.streaming.checkpointLocation", "/path/to/checkpoint")

# 或使用选项设置
query = df.writeStream \
    .option("checkpointLocation", "/path/to/checkpoint") \
    .format("parquet") \
    .start("/path/to/output")

# 精确一次语义配置
query = df.writeStream \
    .format("kafka") \
    .option("kafka.bootstrap.servers", "localhost:9092") \
    .option("topic", "output") \
    .option("checkpointLocation", "/path/to/checkpoint") \
    .start()
```

## 8. Sink 输出

```python
# File Sink
query = df.writeStream \
    .format("parquet") \
    .option("path", "/path/to/output") \
    .option("checkpointLocation", "/path/to/checkpoint") \
    .partitionBy("date", "hour") \
    .trigger(processingTime="10 seconds") \
    .start()

# Kafka Sink
query = df.selectExpr("CAST(key AS STRING)", "CAST(value AS STRING)") \
    .writeStream \
    .format("kafka") \
    .option("kafka.bootstrap.servers", "localhost:9092") \
    .option("topic", "output-topic") \
    .option("checkpointLocation", "/path/to/checkpoint") \
    .start()

# Foreach Sink (自定义处理)
def process_row(row):
    # 自定义处理逻辑
    print(f"Processing: {row}")

query = df.writeStream \
    .foreach(process_row) \
    .start()

# Console Sink (调试用)
query = df.writeStream \
    .outputMode("complete") \
    .format("console") \
    .option("truncate", "false") \
    .start()
```

## 9. 性能调优

```python
# 1. 控制触发间隔
query = df.writeStream \
    .trigger(processingTime="10 seconds") \
    .start()

# 2. 限制每个触发器的数据量
spark.readStream \
    .format("kafka") \
    .option("maxOffsetsPerTrigger", "10000") \
    .load()

# 3. 使用缓存
spark.conf.set("spark.sql.streaming.stateStore.providerClass",
               "org.apache.spark.sql.execution.streaming.state.HDFSBackedStateStoreProvider")

# 4. 分区优化
spark.conf.set("spark.sql.shuffle.partitions", "200")
```

## 10. 与 Flink 对比

| 特性 | Spark Structured Streaming | Apache Flink |
|------|---------------------------|--------------|
| **执行模型** | 微批处理 | 原生流处理 |
| **延迟** | 秒级 | 毫秒级 |
| **API** | DataFrame/SQL | DataStream/Table API |
| **状态管理** | 内置，有限 | 强大，可扩展 |
| **事件时间支持** | 完善 | 原生支持 |
| **适用场景** | 近实时分析、ETL | 实时计算、CEP |
| **生态集成** | Spark 生态 | Flink 生态 |

## 11. 总结

Structured Streaming 的优势：

- **统一 API**：批处理和流处理使用相同 API
- **高吞吐**：基于 Spark SQL 引擎优化
- **容错性**：Checkpoint 机制保证 Exactly-Once
- **易用性**：基于 DataFrame 的高级抽象

适用场景：

- 近实时数据管道
- 连续 ETL 处理
- 实时报表和监控
- 与 Spark 生态深度集成
