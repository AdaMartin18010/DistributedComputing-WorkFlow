# Apache Flink Runtime 详解

## 1. 架构概述

Apache Flink 是一个分布式流处理框架，具有高性能、低延迟和精确一次（Exactly-Once）语义的特点。Flink Runtime 是其核心执行引擎，负责作业的调度和执行。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Apache Flink 架构                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                        Client                                 │ │
│  │                (提交作业/生成 JobGraph)                        │ │
│  └───────────────────────────────┬───────────────────────────────┘ │
│                                  │                                  │
│                                  ▼                                  │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    JobManager (JM)                            │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │ Dispatcher  │  │ JobMaster   │  │ ResourceManager     │   │ │
│  │  │ (接收作业)   │  │ (调度执行)   │  │ (资源管理)          │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  └───────────────────────────────┬───────────────────────────────┘ │
│                                  │                                  │
│                                  ▼                                  │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    TaskManager (TM) Pool                      │ │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌────────────────┐ │ │
│  │  │   TaskManager 1 │  │   TaskManager 2 │  │  TaskManager N │ │ │
│  │  │  ┌───────────┐  │  │  ┌───────────┐  │  │ ┌───────────┐  │ │ │
│  │  │  │ Slot 1    │  │  │  │ Slot 1    │  │  │ │ Slot 1    │  │ │ │
│  │  │  │ Slot 2    │  │  │  │ Slot 2    │  │  │ │ Slot 2    │  │ │ │
│  │  │  │ Slot 3    │  │  │  │ Slot 3    │  │  │ │ Slot 3    │  │ │ │
│  │  │  └───────────┘  │  │  └───────────┘  │  │ └───────────┘  │ │ │
│  │  └─────────────────┘  └─────────────────┘  └────────────────┘ │ │
│  │         │                    │                    │           │ │
│  │         └────────────────────┼────────────────────┘           │ │
│  │                              ▼                                │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │                    Checkpoint Storage                    │ │ │
│  │  │              (HDFS/S3/RocksDB State Backend)            │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心组件

| 组件 | 职责 | 高可用 |
|------|------|--------|
| **Client** | 提交作业、生成 JobGraph | 无状态 |
| **Dispatcher** | 接收作业、启动 JobMaster | 多实例 |
| **JobMaster** | 调度执行、协调 Checkpoint | 单点（故障重启） |
| **ResourceManager** | 管理 TM 资源 | 多实例 |
| **TaskManager** | 执行任务、维护本地状态 | 多实例 |

## 2. 作业执行流程

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Flink 作业执行流程                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  StreamGraph ──▶ JobGraph ──▶ ExecutionGraph ──▶ Physical Execution│
│      │              │              │                  │             │
│      │              │              │                  │             │
│      ▼              ▼              ▼                  ▼             │
│  ┌─────────┐   ┌─────────┐   ┌─────────────┐   ┌─────────────┐     │
│  │ 逻辑图  │──▶│ 优化图  │──▶│   并行图    │──▶│  物理执行   │     │
│  │ API     │   │ JobVertex│   │ Execution  │   │  Task Slot  │     │
│  │ 调用    │   │ JobEdge  │   │ Vertex     │   │  Assignment │     │
│  └─────────┘   └─────────┘   └─────────────┘   └─────────────┘     │
│                                                                     │
│  客户端生成      提交到 JM       JM 调度              TM 执行        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.1 代码示例：WordCount

```java
import org.apache.flink.api.common.eventtime.WatermarkStrategy;
import org.apache.flink.api.common.functions.FlatMapFunction;
import org.apache.flink.api.java.tuple.Tuple2;
import org.apache.flink.streaming.api.datastream.DataStream;
import org.apache.flink.streaming.api.environment.StreamExecutionEnvironment;
import org.apache.flink.streaming.api.windowing.assigners.TumblingEventTimeWindows;
import org.apache.flink.streaming.api.windowing.time.Time;
import org.apache.flink.util.Collector;

public class FlinkWordCount {

    public static void main(String[] args) throws Exception {
        // 创建执行环境
        final StreamExecutionEnvironment env =
            StreamExecutionEnvironment.getExecutionEnvironment();

        // 设置并行度
        env.setParallelism(4);

        // 启用 Checkpoint
        env.enableCheckpointing(5000);
        env.getCheckpointConfig().setCheckpointingMode(
            CheckpointingMode.EXACTLY_ONCE);

        // 创建数据源
        DataStream<String> source = env
            .fromSource(
                KafkaSource.<String>builder()
                    .setBootstrapServers("kafka:9092")
                    .setTopics("input-topic")
                    .setGroupId("flink-group")
                    .setStartingOffsets(OffsetsInitializer.earliest())
                    .setValueOnlyDeserializer(new SimpleStringSchema())
                    .build(),
                WatermarkStrategy.forBoundedOutOfOrderness(
                    Duration.ofSeconds(5)),
                "Kafka Source"
            );

        // 处理流程
        DataStream<Tuple2<String, Integer>> wordCounts = source
            .flatMap(new Tokenizer())
            .keyBy(value -> value.f0)
            .window(TumblingEventTimeWindows.of(Time.minutes(1)))
            .sum(1);

        // 输出
        wordCounts.print();

        // 执行
        env.execute("Flink WordCount");
    }

    // 自定义 FlatMapFunction
    public static class Tokenizer implements FlatMapFunction<String, Tuple2<String, Integer>> {
        @Override
        public void flatMap(String value, Collector<Tuple2<String, Integer>> out) {
            for (String word : value.toLowerCase().split("\\W+")) {
                if (word.length() > 0) {
                    out.collect(new Tuple2<>(word, 1));
                }
            }
        }
    }
}
```

### 2.2 Python API (PyFlink)

```python
from pyflink.datastream import StreamExecutionEnvironment
from pyflink.table import StreamTableEnvironment, EnvironmentSettings

# 创建环境
env = StreamExecutionEnvironment.get_execution_environment()
env.set_parallelism(4)

# 启用 Checkpoint
env.enable_checkpointing(5000)

# 从 Kafka 读取
ds = env.from_source(
    source=KafkaSource.builder()
        .set_bootstrap_servers('kafka:9092')
        .set_topics('input-topic')
        .set_group_id('pyflink-group')
        .set_starting_offsets(KafkaOffsetsInitializer.earliest())
        .set_value_only_deserializer(SimpleStringSchema())
        .build(),
    watermark_strategy=WatermarkStrategy.for_bounded_out_of_orderness(
        Duration.of_seconds(5)),
    source_name='Kafka Source'
)

# 处理
result = ds.flat_map(lambda x: [(word, 1) for word in x.lower().split()]) \
           .key_by(lambda x: x[0]) \
           .window(TumblingProcessingTimeWindows.of(Time.minutes(1))) \
           .sum(1)

result.print()
env.execute("PyFlink WordCount")
```

## 3. Checkpoint 与容错

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Flink Checkpoint 机制                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Time ──────────────────────────────────────────────▶               │
│                                                                     │
│  │  数据流                                                         │
│  │  ────────▶ a ──▶ b ──▶ c ──▶ d ──▶ e ──▶ f ──▶ g              │
│  │                                                                │
│  │  Checkpoint Barriers                                           │
│  │  ════════▶|─────────▶|─────────▶|─────────▶|                  │
│  │           │          │          │          │                   │
│  │           ▼          ▼          ▼          ▼                   │
│  │         CP-n       CP-n+1     CP-n+2     CP-n+3               │
│  │                                                                │
│  │  State Snapshot                                                │
│  │  [State@a]     [State@c]     [State@e]     [State@g]          │
│  │                                                                │
│  │  Snapshot Storage (HDFS/S3)                                   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐           │
│  │  │ chk-1   │  │ chk-2   │  │ chk-3   │  │ chk-4   │           │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘           │
│  │                                                                │
│  └───────────────────────────────────────────────────────────────│
│                                                                     │
│  Checkpoint 是 Flink 实现 Exactly-Once 语义的核心机制              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.1 Checkpoint 配置

```java
// Checkpoint 配置
env.enableCheckpointing(60000);  // 每 60 秒触发一次
env.getCheckpointConfig().setCheckpointingMode(
    CheckpointingMode.EXACTLY_ONCE);
env.getCheckpointConfig().setMinPauseBetweenCheckpoints(30000);
env.getCheckpointConfig().setCheckpointTimeout(600000);
env.getCheckpointConfig().setMaxConcurrentCheckpoints(1);
env.getCheckpointConfig().enableExternalizedCheckpoints(
    ExternalizedCheckpointCleanup.RETAIN_ON_CANCELLATION);

// 状态后端配置
env.setStateBackend(new HashMapStateBackend());
env.getCheckpointConfig().setCheckpointStorage("hdfs://checkpoint-dir");

// 或使用 RocksDB 状态后端（大状态）
env.setStateBackend(new EmbeddedRocksDBStateBackend());
```

### 3.2 Savepoint

```bash
# 触发 Savepoint
flink savepoint <jobId> hdfs://savepoint-dir

# 从 Savepoint 恢复
flink run -s hdfs://savepoint-dir/... <jarFile>

# 代码中设置 Savepoint 路径
env.setDefaultSavepointDirectory("hdfs://savepoint-dir");
```

## 4. 状态管理

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Flink 状态类型                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Keyed State                               │   │
│  │  (键控状态，用于 KeyedStream)                                 │   │
│  │                                                             │   │
│  │  ValueState<T>        ──▶ 单值状态                          │   │
│  │  ListState<T>         ──▶ 列表状态                          │   │
│  │  MapState<UK, UV>     ──▶ Map 状态                          │   │
│  │  ReducingState<T>     ──▶ 用于聚合的 Reducing 状态           │   │
│  │  AggregatingState<T>  ──▶ 用于聚合的 Aggregating 状态        │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                   Operator State                             │   │
│  │  (算子状态，用于非 KeyedStream)                               │   │
│  │                                                             │   │
│  │  ListState<T>         ──▶ 算子列表状态                      │   │
│  │  BroadcastState<K, V> ──▶ 广播状态                          │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.1 Keyed State 使用示例

```java
public class CountFunction extends KeyedProcessFunction<String, Event, Result> {

    private ValueState<Long> countState;
    private ValueState<Long> timerState;

    @Override
    public void open(Configuration parameters) {
        countState = getRuntimeContext().getState(
            new ValueStateDescriptor<>("count", Types.LONG));
        timerState = getRuntimeContext().getState(
            new ValueStateDescriptor<>("timer", Types.LONG));
    }

    @Override
    public void processElement(Event value, Context ctx, Collector<Result> out)
            throws Exception {

        Long current = countState.value();
        if (current == null) {
            current = 0L;
        }
        current++;
        countState.update(current);

        // 注册定时器
        if (timerState.value() == null) {
            long timer = ctx.timerService().currentProcessingTime() + 60000;
            ctx.timerService().registerProcessingTimeTimer(timer);
            timerState.update(timer);
        }
    }

    @Override
    public void onTimer(long timestamp, OnTimerContext ctx, Collector<Result> out)
            throws Exception {
        out.collect(new Result(ctx.getCurrentKey(), countState.value()));
        countState.clear();
        timerState.clear();
    }
}
```

## 5. 时间语义

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Flink 时间语义                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Event Time                Processing Time          Ingestion Time │
│  (事件时间)                 (处理时间)              (摄入时间)      │
│                                                                     │
│  数据产生时间               算子处理时间             数据进入 Flink │
│                                                                     │
│  ┌─────────┐               ┌─────────┐              ┌─────────┐    │
│  │ Source  │               │ Source  │              │ Source  │    │
│  │ t1=10:00│               │         │              │         │    │
│  └────┬────┘               └────┬────┘              └────┬────┘    │
│       │  t2=10:05              │                       │          │
│       │                        │                       │          │
│       ▼  t3=10:03              ▼                       ▼          │
│  ┌─────────┐               ┌─────────┐              ┌─────────┐    │
│  │ Window  │               │ Window  │              │ Window  │    │
│  │ 按事件  │               │ 按系统  │              │ 按摄入  │    │
│  │ 时间戳  │               │ 时钟    │              │ 时间戳  │    │
│  └─────────┘               └─────────┘              └─────────┘    │
│                                                                     │
│  需要 Watermark            最简单                   折中方案        │
│  处理乱序数据              不考虑乱序                自动分配时间戳  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 5.1 Watermark 配置

```java
// 周期性 Watermark
WatermarkStrategy.<MyEvent>forBoundedOutOfOrderness(
    Duration.ofSeconds(5))
    .withTimestampAssigner((event, timestamp) -> event.getEventTime());

// 自定义 Watermark
WatermarkStrategy.<MyEvent>forGenerator(ctx -> new WatermarkGenerator<MyEvent>() {
    private long maxTimestamp = Long.MIN_VALUE;
    private final long outOfOrdernessMillis = 5000;

    @Override
    public void onEvent(MyEvent event, long eventTimestamp, WatermarkOutput output) {
        maxTimestamp = Math.max(maxTimestamp, eventTimestamp);
    }

    @Override
    public void onPeriodicEmit(WatermarkOutput output) {
        output.emitWatermark(new Watermark(maxTimestamp - outOfOrdernessMillis - 1));
    }
});
```

## 6. 性能调优

### 6.1 并行度调优

```java
// 全局并行度
env.setParallelism(4);

// 算子级别并行度
DataStream<Result> result = stream
    .map(new MyMapper()).setParallelism(2)
    .keyBy(event -> event.getUserId())
    .window(TumblingEventTimeWindows.of(Time.minutes(1)))
    .apply(new MyWindowFunction()).setParallelism(4)
    .addSink(new MySink()).setParallelism(1);

// Slot 共享组
stream.map(new MyMapper())
      .slotSharingGroup("group1")
      .keyBy(...)
      .window(...)
      .slotSharingGroup("group2");
```

### 6.2 RocksDB 调优

```java
// RocksDB 状态后端调优
DefaultConfigurableStateBackend stateBackend = new EmbeddedRocksDBStateBackend(true);

// 配置 RocksDB
RocksDBStateBackend rocksDbBackend = new RocksDBStateBackend("hdfs://checkpoints", true);

// 在 flink-conf.yaml 中配置
# state.backend.rocksdb.memory.managed: true
# state.backend.rocksdb.predefined-options: FLASH_SSD_OPTIMIZED
# state.backend.rocksdb.threads.threads-number: 4
# state.backend.rocksdb.memory.fixed-per-slot: 256mb
```

### 6.3 网络缓冲调优

```yaml
# flink-conf.yaml
# 网络内存配置
taskmanager.memory.network.fraction: 0.15
taskmanager.memory.network.min: 256mb
taskmanager.memory.network.max: 512mb

# 网络缓冲
taskmanager.memory.network.memory.max: 256mb
taskmanager.memory.network.memory.min: 128mb
taskmanager.memory.network.memory.fraction: 0.15
```

## 7. 与 Spark Streaming 对比

| 特性 | Apache Flink | Spark Streaming |
|------|--------------|-----------------|
| **执行模型** | 原生流处理 | 微批处理 |
| **延迟** | 毫秒级 | 秒级 |
| **语义** | Exactly-Once | Exactly-Once (较难实现) |
| **状态管理** | 内置，功能强大 | 需借助外部系统 |
| **事件时间支持** | 原生支持 | 较复杂 |
| **容错** | Checkpoint | RDD 检查点 |
| **适用场景** | 实时计算、CEP | 近实时分析 |

## 8. 总结

Flink Runtime 的核心优势：

- **真正的流处理**：毫秒级延迟，而非微批处理
- **精确一次语义**：Checkpoint 机制保证数据不丢不重
- **强大的状态管理**：内置状态后端，支持大状态场景
- **事件时间处理**：原生支持乱序数据和迟到数据
- **灵活的时间语义**：Event Time / Processing Time / Ingestion Time

最佳实践建议：

1. 优先使用 Event Time 处理业务逻辑
2. 根据状态大小选择合适的状态后端
3. 合理设置 Checkpoint 间隔和超时
4. 使用 Slot 共享组优化资源利用
5. 监控反压指标，及时调整并行度


---

## 相关主题

- [Spark-Structured-Streaming](./Spark-Structured-Streaming.md)
- [流处理语义](./流处理语义.md)
- [状态管理](./状态管理.md)

## 参考资源

- [Flink官方文档](https://nightlies.apache.org/flink/flink-docs-stable/)
- [Flink论文](https://asterios.katsifodimos.com/assets/publications/flink-deb.pdf)
