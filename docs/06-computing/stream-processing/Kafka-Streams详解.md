# Kafka Streams 详解

## 1. 架构概述

Kafka Streams 是一个用于构建流处理应用的客户端库，它与 Apache Kafka 深度集成，提供轻量级、可扩展的流处理能力。无需独立集群，直接在应用程序中嵌入运行。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Kafka Streams 架构                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                  Kafka Streams Application                     │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │               StreamsBuilder (拓扑构建器)                  │ │ │
│  │  │                                                         │ │ │
│  │  │   Source ──▶ Processor ──▶ Processor ──▶ Sink          │ │ │
│  │  │     │           │            │            │             │ │ │
│  │  │     ▼           ▼            ▼            ▼             │ │ │
│  │  │  ┌─────┐    ┌─────┐     ┌─────┐     ┌─────┐           │ │ │
│  │  │  │Topic│───▶│Map/ │────▶│Group│────▶│Topic│           │ │ │
│  │  │  │input│    │Filter     │By/Agg│     │output│          │ │ │
│  │  │  └─────┘    └─────┘     └─────┘     └─────┘           │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  │                              │                               │ │
│  │                              ▼                               │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │                 Kafka Streams Engine                     │ │ │
│  │  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌─────────┐ │ │ │
│  │  │  │ Consumer │  │ Processor│  │ State    │  │Producer │ │ │ │
│  │  │  │ (消费)    │  │ (处理)   │  │ Store    │  │(生产)   │ │ │ │
│  │  │  └──────────┘  └──────────┘  │ (状态)   │  └─────────┘ │ │ │
│  │  │                             └──────────┘              │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                      Kafka Cluster                            │ │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐      │ │
│  │  │ Partition│  │ Partition│  │ Partition│  │ Partition│      │ │
│  │  │   0      │  │   1      │  │   2      │  │   N      │      │ │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘      │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │              __consumer_offsets (内部Topic)              │  │ │
│  │  └─────────────────────────────────────────────────────────┘  │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心特点

| 特性 | 说明 |
|------|------|
| **轻量级** | 纯 Java 库，无需独立集群 |
| **无缝集成** | 与 Kafka 深度集成，自动处理分区分配 |
| **状态管理** | 内置本地状态存储，支持容错恢复 |
| **Exactly-Once** | 支持精确一次处理语义 |
| **弹性伸缩** | 自动重平衡，动态扩缩容 |

## 2. 拓扑（Topology）

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Kafka Streams 拓扑结构                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Stream Topology                                                    │
│  ═══════════════                                                    │
│                                                                     │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐     ┌─────────┐       │
│  │ Source  │────▶│ FlatMap │────▶│  Filter │────▶│  Group  │       │
│  │  Node   │     │  Node   │     │  Node   │     │  Node   │       │
│  └────┬────┘     └─────────┘     └─────────┘     └────┬────┘       │
│       │                                               │             │
│       │                                               ▼             │
│       │                                          ┌─────────┐        │
│       │                                          │  Agg    │        │
│       │                                          │  Node   │        │
│       │                                          └────┬────┘        │
│       │                                               │             │
│       │                                               ▼             │
│       │                                          ┌─────────┐        │
│       │                                          │  Sink   │        │
│       │                                          │  Node   │        │
│       │                                          └─────────┘        │
│       │                                                             │
│       │          ┌──────────────────────────────────────┐           │
│       └─────────▶│         State Store                  │           │
│                  │   (RocksDB / In-Memory)              │           │
│                  └──────────────────────────────────────┘           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. 核心 API

### 3.1 High-Level DSL

```java
import org.apache.kafka.streams.KafkaStreams;
import org.apache.kafka.streams.StreamsBuilder;
import org.apache.kafka.streams.kstream.KStream;
import org.apache.kafka.streams.kstream.KTable;
import org.apache.kafka.streams.kstream.Materialized;
import org.apache.kafka.streams.kstream.Produced;

import java.util.Arrays;
import java.util.Properties;

public class WordCountApplication {

    public static void main(String[] args) {
        Properties props = new Properties();
        props.put(StreamsConfig.APPLICATION_ID_CONFIG, "wordcount-application");
        props.put(StreamsConfig.BOOTSTRAP_SERVERS_CONFIG, "localhost:9092");
        props.put(StreamsConfig.DEFAULT_KEY_SERDE_CLASS_CONFIG,
                  Serdes.String().getClass());
        props.put(StreamsConfig.DEFAULT_VALUE_SERDE_CLASS_CONFIG,
                  Serdes.String().getClass());

        StreamsBuilder builder = new StreamsBuilder();

        // 创建 Source Stream
        KStream<String, String> source = builder.stream("input-topic");

        // 处理逻辑
        KStream<String, Long> wordCounts = source
            .flatMapValues(value -> Arrays.asList(value.toLowerCase().split("\\W+")))
            .groupBy((key, word) -> word)
            .count(Materialized.as("counts-store"))
            .toStream();

        // 输出到 Sink
        wordCounts.to("output-topic", Produced.with(Serdes.String(), Serdes.Long()));

        // 构建并启动
        KafkaStreams streams = new KafkaStreams(builder.build(), props);
        streams.start();

        // 优雅关闭
        Runtime.getRuntime().addShutdownHook(new Thread(streams::close));
    }
}
```

### 3.2 Processor API (底层 API)

```java
import org.apache.kafka.streams.processor.api.Processor;
import org.apache.kafka.streams.processor.api.ProcessorContext;
import org.apache.kafka.streams.processor.api.Record;
import org.apache.kafka.streams.state.KeyValueStore;

public class CustomProcessor implements Processor<String, String, String, Long> {

    private ProcessorContext<String, Long> context;
    private KeyValueStore<String, Long> kvStore;

    @Override
    public void init(ProcessorContext<String, Long> context) {
        this.context = context;
        // 获取状态存储
        this.kvStore = context.getStateStore("my-store");
    }

    @Override
    public void process(Record<String, String> record) {
        String key = record.key();
        String value = record.value();

        // 自定义处理逻辑
        Long current = kvStore.get(key);
        if (current == null) {
            current = 0L;
        }
        current++;
        kvStore.put(key, current);

        // 转发记录
        context.forward(record.withValue(current));

        // 提交 (可选，用于精确控制)
        context.commit();
    }

    @Override
    public void close() {
        // 清理资源
    }
}
```

## 4. 状态存储

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Kafka Streams 状态存储                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                   KeyValueStore                              │   │
│  │  ┌─────────────────────────────────────────────────────────┐ │   │
│  │  │                    RocksDB                              │ │   │
│  │  │  - 持久化到本地磁盘                                      │ │   │
│  │  │  - 支持大数据集                                          │ │   │
│  │  │  - 自动变更日志到 Kafka                                  │ │   │
│  │  └─────────────────────────────────────────────────────────┘ │   │
│  │                              │                                │   │
│  │                              ▼                                │   │
│  │  ┌─────────────────────────────────────────────────────────┐ │   │
│  │  │            changelog-topic (内部 Topic)                 │ │   │
│  │  │   用于故障恢复和重平衡时的状态重建                       │ │   │
│  │  └─────────────────────────────────────────────────────────┘ │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │              WindowStore / SessionStore                      │   │
│  │  ┌─────────────┬─────────────┬─────────────┬─────────────┐  │   │
│  │  │  Window 1   │  Window 2   │  Window 3   │  Window N   │  │   │
│  │  │  [0-10s]    │  [10-20s]   │  [20-30s]   │             │  │   │
│  │  │  key:value  │  key:value  │  key:value  │             │  │   │
│  │  └─────────────┴─────────────┴─────────────┴─────────────┘  │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.1 状态存储配置

```java
// 配置状态存储
StreamsBuilder builder = new StreamsBuilder();

// KeyValue Store
KTable<String, Long> counts = builder
    .stream("input-topic", Consumed.with(Serdes.String(), Serdes.String()))
    .groupByKey()
    .count(Materialized.<String, Long, KeyValueStore<Bytes, byte[]>>as("counts-store")
        .withKeySerde(Serdes.String())
        .withValueSerde(Serdes.Long()));

// Window Store
TimeWindowedKStream<String, String> windowed = builder
    .stream("input-topic")
    .groupByKey()
    .windowedBy(TimeWindows.of(Duration.ofMinutes(5)));

// 自定义 Store Supplier
public class CustomStoreSupplier implements KeyValueBytesStoreSupplier {
    @Override
    public String name() {
        return "custom-store";
    }

    @Override
    public KeyValueStore<Bytes, byte[]> get() {
        return Stores.persistentKeyValueStore(name()).get();
    }
}
```

## 5. 窗口操作

```java
import org.apache.kafka.streams.kstream.TimeWindows;
import org.apache.kafka.streams.kstream.SessionWindows;
import org.apache.kafka.streams.kstream.SlidingWindows;

// 滚动窗口 (Tumbling Window)
KStream<String, String> stream = builder.stream("input-topic");
stream.groupByKey()
    .windowedBy(TimeWindows.of(Duration.ofMinutes(5)))
    .count()
    .toStream()
    .to("output-topic");

// 滑动窗口 (Hopping Window)
stream.groupByKey()
    .windowedBy(TimeWindows.of(Duration.ofMinutes(10))
        .advanceBy(Duration.ofMinutes(2)))
    .aggregate(
        () -> 0L,
        (key, value, aggregate) -> aggregate + 1,
        Materialized.with(Serdes.String(), Serdes.Long())
    );

// 会话窗口 (Session Window)
stream.groupByKey()
    .windowedBy(SessionWindows.with(Duration.ofMinutes(5)))
    .count();

// 滑动窗口 (Sliding Window) -  Kafka 3.0+
stream.groupByKey()
    .windowedBy(SlidingWindows.ofTimeDifferenceWithNoGrace(Duration.ofSeconds(10)))
    .count();
```

## 6. 连接（Join）操作

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Kafka Streams Join 类型                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  KStream + KStream ──▶ KStream   (Windowed Join)                  │
│  KStream + KTable  ──▶ KStream   (Stream Table Join)              │
│  KTable  + KTable  ──▶ KTable    (Table Table Join)               │
│                                                                     │
│  ┌─────────────┐         ┌─────────────┐                          │
│  │   Stream    │         │    Table    │                          │
│  │   (实时)     │         │   (最新状态) │                          │
│  │  ┌───────┐  │         │  ┌───────┐  │                          │
│  │  │event 1│  │         │  │ key1  │──┼────▶ Join ──▶ Enriched  │
│  │  │event 2│──┼────┐    │  │ key2  │  │         Event           │
│  │  │event 3│  │    │    │  │ key3  │  │                          │
│  │  └───────┘  │    │    │  └───────┘  │                          │
│  └─────────────┘    └───▶│  按 key 查找 │                          │
│                          └─────────────┘                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```java
// Stream-Table Join
KStream<String, String> events = builder.stream("events");
KTable<String, String> users = builder.table("users");

KStream<String, String> enriched = events.join(
    users,
    (event, user) -> event + ":" + user,  // ValueJoiner
    Joined.with(Serdes.String(), Serdes.String(), Serdes.String())
);

// Stream-Stream Join (需要窗口)
KStream<String, String> left = builder.stream("left-topic");
KStream<String, String> right = builder.stream("right-topic");

KStream<String, String> joined = left.join(
    right,
    (leftValue, rightValue) -> leftValue + "-" + rightValue,
    JoinWindows.of(Duration.ofMinutes(5)),
    StreamJoined.with(Serdes.String(), Serdes.String(), Serdes.String())
);

// Table-Table Join
KTable<String, String> table1 = builder.table("topic1");
KTable<String, String> table2 = builder.table("topic2");

KTable<String, String> merged = table1.join(
    table2,
    (v1, v2) -> v1 + v2
);
```

## 7. Exactly-Once 语义

```java
Properties props = new Properties();
props.put(StreamsConfig.APPLICATION_ID_CONFIG, "exactly-once-app");
props.put(StreamsConfig.BOOTSTRAP_SERVERS_CONFIG, "localhost:9092");

// 启用 Exactly-Once 语义
props.put(StreamsConfig.PROCESSING_GUARANTEE_CONFIG,
          StreamsConfig.EXACTLY_ONCE_V2);

// 事务配置
props.put(StreamsConfig.PRODUCER_PREFIX + ProducerConfig.TRANSACTION_TIMEOUT_CONFIG,
          "60000");
props.put(StreamsConfig.PRODUCER_PREFIX + ProducerConfig.ENABLE_IDEMPOTENCE_CONFIG,
          "true");

// 消费者隔离级别
props.put(StreamsConfig.CONSUMER_PREFIX + ConsumerConfig.ISOLATION_LEVEL_CONFIG,
          "read_committed");
```

## 8. 监控与指标

```java
// 配置指标报告
props.put(StreamsConfig.METRICS_RECORDING_LEVEL_CONFIG, "DEBUG");

// 自定义状态监听器
streams.setStateListener((newState, oldState) -> {
    System.out.printf("State transition from %s to %s%n", oldState, newState);
});

// 获取指标
Map<MetricName, ? extends Metric> metrics = streams.metrics();
for (Map.Entry<MetricName, ? extends Metric> entry : metrics.entrySet()) {
    System.out.println(entry.getKey() + ": " + entry.getValue().metricValue());
}

// 关键指标：
// - records-consumed-total
// - records-produced-total
// - commit-total
// - poll-records-avg
// - process-latency-avg
```

## 9. 配置优化

```java
Properties props = new Properties();

// 基本配置
props.put(StreamsConfig.APPLICATION_ID_CONFIG, "my-app");
props.put(StreamsConfig.BOOTSTRAP_SERVERS_CONFIG, "kafka:9092");

// 线程配置
props.put(StreamsConfig.NUM_STREAM_THREADS_CONFIG, "4");

// 缓存和缓冲区
props.put(StreamsConfig.CACHE_MAX_BYTES_BUFFERING_CONFIG, "10485760"); // 10MB
props.put(StreamsConfig.COMMIT_INTERVAL_MS_CONFIG, "30000"); // 30s

// 状态存储配置
props.put(StreamsConfig.STATE_DIR_CONFIG, "/var/lib/kafka-streams");
props.put(StreamsConfig.REPLICATION_FACTOR_CONFIG, "3");

// RocksDB 调优
props.put(StreamsConfig.ROCKSDB_CONFIG_SETTER_CLASS_CONFIG,
          CustomRocksDbConfig.class.getName());
```

## 10. 与 Flink 对比

| 特性 | Kafka Streams | Apache Flink |
|------|---------------|--------------|
| **部署模式** | 嵌入式库 | 独立集群 |
| **依赖** | 仅需 Kafka | 独立集群基础设施 |
| **延迟** | 毫秒-秒级 | 毫秒级 |
| **状态存储** | 本地 RocksDB | 本地 + 远程 |
| **生态** | Kafka 生态 | 丰富的大数据生态 |
| **SQL 支持** | KSQL DB | Flink SQL |
| **适用场景** | Kafka 为中心的处理 | 通用流处理 |

## 11. 总结

Kafka Streams 的优势：

- **轻量级**：无需额外基础设施，直接在应用中使用
- **深度集成**：与 Kafka 原生集成，自动处理分区分配
- **开发友好**：简洁的 Java API，易于开发和测试
- **弹性伸缩**：自动重平衡，支持动态扩缩容

适用场景：

- Kafka 为中心的流处理应用
- 微服务架构中的事件处理
- 实时 ETL 管道
- 与 KSQL DB 配合使用

局限性：

- 仅支持 Kafka 作为数据源
- 不支持复杂的窗口类型（如 Watermark）
- 状态管理相对简单
