# Spark Core 详解

## 1. 架构概述

Apache Spark 是一个快速、通用、可扩展的大数据计算引擎。Spark Core 是其基础引擎，提供了分布式任务调度、内存计算、故障恢复和存储系统交互等功能。

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Spark Core 架构                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   ┌───────────────────────────────────────────────────────────┐    │
│   │                    Driver Program                          │    │
│   │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │    │
│   │  │  SparkContext│  │ DAGScheduler │  │ TaskScheduler│     │    │
│   │  │              │  │              │  │              │     │    │
│   │  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘     │    │
│   │         │                 │                 │             │    │
│   │         └─────────────────┴─────────────────┘             │    │
│   └───────────────────────────────────────────────────────────┘    │
│                              │                                      │
│                              ▼                                      │
│   ┌───────────────────────────────────────────────────────────┐    │
│   │                  Cluster Manager                           │    │
│   │     (Standalone / YARN / Mesos / Kubernetes)              │    │
│   └───────────────────────────────────────────────────────────┘    │
│                              │                                      │
│           ┌──────────────────┼──────────────────┐                  │
│           ▼                  ▼                  ▼                  │
│   ┌───────────────┐  ┌───────────────┐  ┌───────────────┐         │
│   │  Executor 1   │  │  Executor 2   │  │  Executor N   │         │
│   │ ┌───────────┐ │  │ ┌───────────┐ │  │ ┌───────────┐ │         │
│   │ │ Task 1    │ │  │ │ Task 3    │ │  │ │ Task 5    │ │         │
│   │ │ Task 2    │ │  │ │ Task 4    │ │  │ │ Task 6    │ │         │
│   │ └───────────┘ │  │ └───────────┘ │  │ └───────────┘ │         │
│   │ ┌───────────┐ │  │ ┌───────────┐ │  │ ┌───────────┐ │         │
│   │ │ Block 1   │ │  │ │ Block 2   │ │  │ │ Block 3   │ │         │
│   │ │ (Cache)   │ │  │ │ (Cache)   │ │  │ │ (Cache)   │ │         │
│   │ └───────────┘ │  │ └───────────┘ │  │ └───────────┘ │         │
│   └───────────────┘  └───────────────┘  └───────────────┘         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心组件

| 组件 | 职责 | 部署位置 |
|------|------|----------|
| **Driver** | 运行 main() 函数，创建 SparkContext | 客户端或集群 |
| **SparkContext** | Spark 应用的入口，协调集群资源 | Driver 内 |
| **Cluster Manager** | 资源分配（YARN/Mesos/Standalone） | 集群 |
| **Executor** | 执行任务，存储数据 | Worker 节点 |
| **Task** | 最小执行单元 | Executor 内 |

## 2. RDD（弹性分布式数据集）

RDD 是 Spark 最核心的抽象，代表一个不可变、可分区、可并行计算的元素集合。

```
┌─────────────────────────────────────────────────────────────────────┐
│                         RDD 内部结构                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   ┌─────────────────────────────────────────────────────────────┐  │
│   │                         RDD                                  │  │
│   │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │  │
│   │  │Partition│  │Partition│  │Partition│  │Partition│        │  │
│   │  │   0     │  │   1     │  │   2     │  │   N     │        │  │
│   │  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘        │  │
│   │       │            │            │            │              │  │
│   │   ┌───┴───┐    ┌───┴───┐    ┌───┴───┐    ┌───┴───┐         │  │
│   │   │Record1│    │Record4│    │Record7│    │Record10│        │  │
│   │   │Record2│    │Record5│    │Record8│    │Record11│        │  │
│   │   │Record3│    │Record6│    │Record9│    │Record12│        │  │
│   │   └───────┘    └───────┘    └───────┘    └───────┘         │  │
│   └─────────────────────────────────────────────────────────────┘  │
│                                                                     │
│   RDD 属性：                                                        │
│   - 分区列表 (partitions)                                           │
│   - 计算函数 (compute function)                                     │
│   - 依赖关系 (dependencies)                                         │
│   - 分区器 (partitioner)                                            │
│   - 优先位置 (preferred locations)                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.1 RDD 创建方式

```python
from pyspark import SparkConf, SparkContext

# 初始化 SparkContext
conf = SparkConf().setAppName("RDD-Demo").setMaster("local[*]")
sc = SparkContext(conf=conf)

# 方式1: 从集合创建
rdd1 = sc.parallelize([1, 2, 3, 4, 5], numSlices=3)

# 方式2: 从外部存储创建
rdd2 = sc.textFile("hdfs://path/to/file.txt")

# 方式3: 从其他 RDD 转换
rdd3 = rdd1.map(lambda x: x * 2)
```

```scala
// Scala 版本
import org.apache.spark.{SparkConf, SparkContext}

val conf = new SparkConf().setAppName("RDD-Demo").setMaster("local[*]")
val sc = new SparkContext(conf)

// 从集合创建
val rdd1 = sc.parallelize(Seq(1, 2, 3, 4, 5), 3)

// 从文件创建
val rdd2 = sc.textFile("hdfs://path/to/file.txt")

// 转换
val rdd3 = rdd1.map(_ * 2)
```

### 2.2 RDD 操作类型

```
┌─────────────────────────────────────────────────────────────────────┐
│                      RDD 操作分类                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                     Transformation                          │   │
│  │  (惰性求值，返回新 RDD)                                       │   │
│  │                                                             │   │
│  │   map()        filter()      flatMap()     mapPartitions() │   │
│  │   sample()     union()       intersection  distinct()      │   │
│  │   groupByKey() reduceByKey() aggregateByKey() sortByKey()  │   │
│  │   join()       cogroup()     cartesian()   pipe()          │   │
│  │   coalesce()   repartition() partitionBy()                  │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                        Action                               │   │
│  │  (立即执行，返回结果或写入外部)                                │   │
│  │                                                             │   │
│  │   reduce()     collect()     count()       first()         │   │
│  │   take()       takeSample()  takeOrdered() saveAsTextFile()│   │
│  │   countByKey() foreach()     foreachPartition()             │   │
│  │                                                             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.3 转换操作示例

```python
# map - 一对一映射
rdd = sc.parallelize([1, 2, 3, 4])
mapped = rdd.map(lambda x: x * 2)  # [2, 4, 6, 8]

# filter - 过滤
filtered = rdd.filter(lambda x: x > 2)  # [3, 4]

# flatMap - 一对多映射
lines = sc.parallelize(["hello world", "spark rdd"])
words = lines.flatMap(lambda line: line.split(" "))  # ["hello", "world", "spark", "rdd"]

# reduceByKey - 按键聚合
pairs = sc.parallelize([("a", 1), ("b", 2), ("a", 3)])
reduced = pairs.reduceByKey(lambda x, y: x + y)  # [("a", 4), ("b", 2)]
```

```scala
// Scala 函数式风格
val rdd = sc.parallelize(Seq(1, 2, 3, 4))
val mapped = rdd.map(_ * 2)
val filtered = rdd.filter(_ > 2)

val pairs = sc.parallelize(Seq(("a", 1), ("b", 2), ("a", 3)))
val reduced = pairs.reduceByKey(_ + _)
```

## 3. RDD 依赖与容错

```
┌─────────────────────────────────────────────────────────────────────┐
│                      RDD 依赖关系                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Narrow Dependency (窄依赖)          Wide Dependency (宽依赖)      │
│  ┌─────────────────────────┐         ┌─────────────────────────┐   │
│  │   Parent RDD            │         │   Parent RDD            │   │
│  │  ┌───┬───┬───┐         │         │  ┌───┬───┬───┐         │   │
│  │  │ P1│ P2│ P3│         │         │  │ P1│ P2│ P3│         │   │
│  │  └─┬─┴─┬─┴─┬─┘         │         │  └─┬─┴─┬─┴─┬─┘         │   │
│  │    │   │   │           │         │    │   │   │           │   │
│  │    ▼   ▼   ▼           │         │    └───┼───┘           │   │
│  │  ┌───┬───┬───┐         │         │        │               │   │
│  │  │ C1│ C2│ C3│         │         │        ▼               │   │
│  │  └───┴───┴───┘         │         │  ┌───┬───┬───┐         │   │
│  │  Child RDD (map)       │         │  │ C1│ C2│ C3│         │   │
│  │                        │         │  └───┴───┴───┘         │   │
│  │  一对一/多对一           │         │  Child RDD (groupByKey)│   │
│  │  无需 Shuffle           │         │                        │   │
│  │                        │         │  多对多                 │   │
│  │  Pipeline 执行          │         │  需要 Shuffle           │   │
│  └─────────────────────────┘         └─────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.1 RDD 血缘（Lineage）

```python
# 血缘关系示例
rdd1 = sc.textFile("data.txt")           # 读取文件
rdd2 = rdd1.flatMap(lambda x: x.split()) # 分词
rdd3 = rdd2.map(lambda x: (x, 1))        # 映射为 (word, 1)
rdd4 = rdd3.reduceByKey(lambda x, y: x + y) # 按 key 聚合

# 查看血缘
print(rdd4.toDebugString())
# (2) ShuffledRDD[4] at reduceByKey ...
#  +-(2) MappedRDD[3] at map ...
#      |  FlatMappedRDD[2] at flatMap ...
#      |  data.txt MappedRDD[1] at textFile ...
```

## 4. Shuffle 详解

Shuffle 是 Spark 中跨分区重新分配数据的操作，是性能瓶颈的主要来源。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Spark Shuffle 流程                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Map Side                           Reduce Side                    │
│  ┌───────────────────┐             ┌───────────────────┐           │
│  │   Map Task        │             │   Reduce Task     │           │
│  │  ┌─────────────┐  │             │  ┌─────────────┐  │           │
│  │  │ Output      │  │             │  │ Fetch       │  │           │
│  │  │ Records     │──┼──┐       ┌──┼─▶│ Data        │  │           │
│  │  └─────────────┘  │  │       │  │  └─────────────┘  │           │
│  │         │         │  │       │  │         │         │           │
│  │         ▼         │  │       │  │         ▼         │           │
│  │  ┌─────────────┐  │  │       │  │  ┌─────────────┐  │           │
│  │  │ Partition   │  │  │       │  │  │ Merge Sort  │  │           │
│  │  │ Function    │  │  │       │  │  │ (External)  │  │           │
│  │  └─────────────┘  │  │       │  │  └─────────────┘  │           │
│  │         │         │  │       │  │         │         │           │
│  │         ▼         │  │       │  │         ▼         │           │
│  │  ┌─────────────┐  │  │       │  │  ┌─────────────┐  │           │
│  │  │ Memory      │  │  │       │  │  │ Aggregate   │  │           │
│  │  │ Buffer      │──┼──┼───────┼──┼─▶│ Function    │  │           │
│  │  └─────────────┘  │  │       │  │  └─────────────┘  │           │
│  │         │         │  │       │  │         │         │           │
│  │         ▼         │  │       │  │         ▼         │           │
│  │  ┌─────────────┐  │  │       │  │  ┌─────────────┐  │           │
│  │  │ Spill to    │──┼──┘       └──┼─▶│ Output      │  │           │
│  │  │ Disk        │  │  Network    │  │  Result     │  │           │
│  │  └─────────────┘  │             │  └─────────────┘  │           │
│  └───────────────────┘             └───────────────────┘           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.1 Shuffle 优化配置

```python
# Spark 配置
conf = SparkConf()

# Shuffle 相关配置
conf.set("spark.sql.shuffle.partitions", "200")  # Shuffle 分区数
conf.set("spark.default.parallelism", "100")     # 默认并行度
conf.set("spark.shuffle.file.buffer", "64k")     # Shuffle 文件缓冲区
conf.set("spark.shuffle.memoryFraction", "0.2")  # Shuffle 内存占比

# 使用 SortShuffleManager（默认）
conf.set("spark.shuffle.manager", "sort")
```

### 4.2 避免 Shuffle 的技巧

```python
# 1. 使用 mapPartitions 替代 map + reduceByKey
def process_partition(iterator):
    result = {}
    for item in iterator:
        key = item[0]
        result[key] = result.get(key, 0) + item[1]
    return result.items()

# 2. 使用 reduceByKey 替代 groupByKey
# 好：在 Map 端预聚合
rdd.reduceByKey(lambda x, y: x + y)

# 差：先全量收集再聚合
rdd.groupByKey().mapValues(sum)

# 3. 自定义分区器避免倾斜
from pyspark import Partitioner

class HashPartitioner(Partitioner):
    def __init__(self, num_partitions):
        self.num_partitions = num_partitions

    def numPartitions(self):
        return self.num_partitions

    def getPartition(self, key):
        return hash(key) % self.num_partitions
```

## 5. 持久化与缓存

```
┌─────────────────────────────────────────────────────────────────────┐
│                    RDD 持久化级别                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  级别                    内存    磁盘    序列化    复制副本          │
│  ─────────────────────────────────────────────────────────          │
│  MEMORY_ONLY             ✓       ✗        ✗         ✗              │
│  MEMORY_ONLY_SER         ✓       ✗        ✓         ✗              │
│  MEMORY_AND_DISK         ✓       ✓        ✗         ✗              │
│  MEMORY_AND_DISK_SER     ✓       ✓        ✓         ✗              │
│  DISK_ONLY               ✗       ✓        ✓         ✗              │
│  MEMORY_ONLY_2           ✓       ✗        ✗         ✓              │
│  MEMORY_AND_DISK_2       ✓       ✓        ✗         ✓              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```python
# 持久化示例
rdd = sc.textFile("large_file.txt")
words = rdd.flatMap(lambda x: x.split())
word_pairs = words.map(lambda x: (x, 1))

# 缓存中间结果
counted = word_pairs.reduceByKey(lambda x, y: x + y)
counted.persist(StorageLevel.MEMORY_AND_DISK_SER)

# 多次使用
result1 = counted.filter(lambda x: x[1] > 100).collect()
result2 = counted.sortBy(lambda x: x[1], ascending=False).take(10)

# 释放缓存
counted.unpersist()
```

## 6. 性能调优

### 6.1 广播变量

```python
# 使用广播变量减少数据传输
large_dict = {"key1": "value1", "key2": "value2", ...}  # 大字典
broadcast_dict = sc.broadcast(large_dict)

rdd = sc.parallelize(["key1", "key2", "key3"])
result = rdd.map(lambda x: broadcast_dict.value.get(x, "unknown"))
```

### 6.2 累加器

```python
# 使用累加器进行全局计数
error_count = sc.accumulator(0)

def process_record(record):
    try:
        return parse(record)
    except:
        error_count.add(1)
        return None

rdd.map(process_record).filter(lambda x: x is not None).collect()
print(f"Error count: {error_count.value}")
```

### 6.3 数据倾斜处理

```python
# 两阶段聚合解决数据倾斜
# 第一阶段：局部聚合加随机前缀
rdd = pairs.map(lambda x: ((random.randint(0, 9), x[0]), x[1]))
            .reduceByKey(lambda x, y: x + y)

# 第二阶段：去除前缀后全局聚合
result = rdd.map(lambda x: (x[0][1], x[1])).reduceByKey(lambda x, y: x + y)
```

## 7. 与 MapReduce 对比

| 特性 | Spark Core | Hadoop MapReduce |
|------|------------|------------------|
| **执行速度** | 快（内存计算） | 慢（磁盘IO为主） |
| **迭代计算** | 高效（缓存支持） | 低效 |
| **易用性** | 高（丰富API） | 低 |
| **容错** | RDD 血缘重算 | 任务重试 |
| **适用场景** | 迭代计算、实时处理 | 离线批处理 |
| **资源消耗** | 内存要求高 | 内存要求低 |

## 8. 总结

Spark Core 通过 RDD 抽象和内存计算提供了高效的数据处理能力：

- **核心优势**：内存计算、延迟执行、丰富的转换操作
- **关键优化**：避免 Shuffle、合理使用持久化、处理数据倾斜
- **最佳实践**：优先使用 reduceByKey 而非 groupByKey、使用广播变量、监控作业执行


---

## 相关主题

- [Hadoop-MapReduce详解](./Hadoop-MapReduce详解.md)
- [Spark-SQL详解](../query-engine/Spark-SQL详解.md)
- [Flink-Runtime详解](../stream-processing/Flink-Runtime详解.md)

## 参考资源

- [Spark官方文档](https://spark.apache.org/docs/latest/)
- [RDD论文](https://www.usenix.org/system/files/conference/nsdi12/nsdi12-final138.pdf)
