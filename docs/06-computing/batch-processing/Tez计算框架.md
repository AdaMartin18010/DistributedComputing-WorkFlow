# Apache Tez 计算框架详解

## 1. 架构概述

Apache Tez 是一个基于 YARN 的通用分布式计算框架，旨在为 Hadoop 生态系统提供比 MapReduce 更灵活、更高效的数据处理能力。Tez 通过有向无环图（DAG）模型来定义计算任务，消除了 MapReduce 中不必要的同步屏障。

```
┌─────────────────────────────────────────────────────────────────────┐
│                     Apache Tez 架构                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                     Client (AM Client)                        │ │
│  │                     - 提交 DAG 作业                            │ │
│  │                     - 监控执行状态                             │ │
│  └────────────────────────────┬──────────────────────────────────┘ │
│                               │                                     │
│                               ▼                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │              AppMaster (DAGAppMaster)                         │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │ DAG Parser  │  │ Scheduler   │  │ Task Communicator   │   │ │
│  │  │ (DAG解析)    │  │ (调度器)     │  │ (任务通信)          │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  └────────────────────────────┬──────────────────────────────────┘ │
│                               │                                     │
│                               ▼                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Task Execution (Containers)                │ │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐          │ │
│  │  │ Task 1  │  │ Task 2  │  │ Task 3  │  │ Task N  │          │ │
│  │  │ Input   │  │ Process │  │ Shuffle │  │ Output  │          │ │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘          │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 Tez vs MapReduce

```
┌─────────────────────────────────────────────────────────────────────┐
│              MapReduce 与 Tez 执行模型对比                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  MapReduce (多作业链)                  Tez (单 DAG)                │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌───────────────────┐   │
│  │  Job 1  │──▶│  Job 2  │──▶│  Job 3  │──▶│     Result        │   │
│  │  M  R   │   │  M  R   │   │  M  R   │   │                   │   │
│  └────┬────┘   └────┬────┘   └────┬────┘   └───────────────────┘   │
│       │             │             │                                 │
│       ▼             ▼             ▼                                 │
│  [HDFS Write]  [HDFS Write]  [HDFS Write]    多次磁盘写             │
│                                                                     │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                        DAG                                  │   │
│  │  Vertex 1 (Map) ──▶ Vertex 2 (Reduce) ──▶ Vertex 3 (Output)│   │
│  │       │                  │                  │               │   │
│  │       │                  │                  │               │   │
│  │       └──────────────────┴──────────────────┘               │   │
│  │                    内存/本地传输                            │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. 核心概念

### 2.1 DAG（有向无环图）

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Tez DAG 结构                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│                         ┌─────────────┐                            │
│                         │    DAG      │                            │
│                         └──────┬──────┘                            │
│                                │                                    │
│           ┌────────────────────┼────────────────────┐              │
│           │                    │                    │              │
│           ▼                    ▼                    ▼              │
│     ┌───────────┐        ┌───────────┐        ┌───────────┐       │
│     │  Vertex 1 │───────▶│  Vertex 2 │───────▶│  Vertex 3 │       │
│     │  (Input)  │        │ (Process) │        │ (Output)  │       │
│     └─────┬─────┘        └─────┬─────┘        └─────┬─────┘       │
│           │                    │                    │              │
│     ┌─────┴─────┐        ┌─────┴─────┐        ┌─────┴─────┐       │
│     │  Task 1.1 │        │  Task 2.1 │        │  Task 3.1 │       │
│     │  Task 1.2 │        │  Task 2.2 │        │  Task 3.2 │       │
│     │  Task 1.3 │        │  Task 2.3 │        │  Task 3.3 │       │
│     └───────────┘        └───────────┘        └───────────┘       │
│                                                                     │
│  Vertex: 计算阶段的抽象（类似 MR 的 Map/Reduce）                     │
│  Task: Vertex 的具体执行单元                                         │
│  Edge: Vertex 之间的数据流动关系                                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 Edge 类型

| Edge 类型 | 数据传递模式 | 适用场景 |
|-----------|-------------|----------|
| **BROADCAST** | 广播到所有任务 | 小表join、配置分发 |
| **SCATTER_GATHER** | 分区 shuffle | 大规模数据重分布 |
| **ONE_TO_ONE** | 一对一传递 | 管道化处理 |
| **CUSTOM** | 自定义分区逻辑 | 特殊业务需求 |

## 3. Tez API 示例

### 3.1 Java API

```java
import org.apache.tez.client.TezClient;
import org.apache.tez.dag.api.DAG;
import org.apache.tez.dag.api.Edge;
import org.apache.tez.dag.api.EdgeProperty;
import org.apache.tez.dag.api.GroupInputEdge;
import org.apache.tez.dag.api.Vertex;
import org.apache.tez.dag.api.client.DAGClient;
import org.apache.tez.dag.api.client.DAGStatus;

public class TezWordCount {

    public static void main(String[] args) throws Exception {
        // 创建 Tez 配置
        TezConfiguration tezConf = new TezConfiguration();
        tezConf.setBoolean(TezConfiguration.TEZ_LOCAL_MODE, false);

        // 创建 Tez 客户端
        TezClient tezClient = TezClient.create("WordCount", tezConf);
        tezClient.start();

        // 构建 DAG
        DAG dag = DAG.create("WordCountDAG");

        // 创建输入 Vertex
        Vertex inputVertex = Vertex.create("Input",
            ProcessorDescriptor.create(InputProcessor.class.getName()))
            .setParallelism(3);

        // 创建处理 Vertex (Tokenizer)
        Vertex tokenizerVertex = Vertex.create("Tokenizer",
            ProcessorDescriptor.create(TokenizerProcessor.class.getName()))
            .setParallelism(5);

        // 创建汇总 Vertex (Summer)
        Vertex summerVertex = Vertex.create("Summer",
            ProcessorDescriptor.create(SummerProcessor.class.getName()))
            .setParallelism(2);

        // 添加 Edge: Input -> Tokenizer
        Edge edge1 = Edge.create(inputVertex, tokenizerVertex,
            EdgeProperty.create(DataMovementType.BROADCAST,
                               DataSourceType.PERSISTED,
                               SchedulingType.SEQUENTIAL));

        // 添加 Edge: Tokenizer -> Summer (SCATTER_GATHER = Shuffle)
        Edge edge2 = Edge.create(tokenizerVertex, summerVertex,
            EdgeProperty.create(DataMovementType.SCATTER_GATHER,
                               DataSourceType.PERSISTED,
                               SchedulingType.SEQUENTIAL));

        // 组装 DAG
        dag.addVertex(inputVertex)
           .addVertex(tokenizerVertex)
           .addVertex(summerVertex)
           .addEdge(edge1)
           .addEdge(edge2);

        // 提交 DAG
        DAGClient dagClient = tezClient.submitDAG(dag);

        // 等待完成
        DAGStatus dagStatus = dagClient.waitForCompletionWithStatusUpdates(null);
        System.out.println("DAG completed with status: " + dagStatus.getState());

        tezClient.stop();
    }
}
```

### 3.2 Processor 实现

```java
// Tokenizer Processor
public class TokenizerProcessor extends SimpleProcessor {

    @Override
    public void run() throws Exception {
        // 获取输入读取器
        List<KeyValueReader> kvReaders = getInputs().get(0).getReaders();

        // 获取输出写入器
        KeyValueWriter kvWriter = getOutputs().get(0).getWriter();

        for (KeyValueReader kvReader : kvReaders) {
            while (kvReader.next()) {
                String line = kvReader.getCurrentValue().toString();
                String[] words = line.split("\\s+");

                for (String word : words) {
                    // 输出 (word, 1)
                    kvWriter.write(new Text(word), new IntWritable(1));
                }
            }
        }
    }
}

// Summer Processor
public class SummerProcessor extends SimpleProcessor {

    @Override
    public void run() throws Exception {
        Map<String, Integer> counts = new HashMap<>();

        List<KeyValueReader> kvReaders = getInputs().get(0).getReaders();

        for (KeyValueReader kvReader : kvReaders) {
            while (kvReader.next()) {
                String word = kvReader.getCurrentKey().toString();
                int count = ((IntWritable) kvReader.getCurrentValue()).get();
                counts.merge(word, count, Integer::sum);
            }
        }

        KeyValueWriter kvWriter = getOutputs().get(0).getWriter();
        for (Map.Entry<String, Integer> entry : counts.entrySet()) {
            kvWriter.write(new Text(entry.getKey()), new IntWritable(entry.getValue()));
        }
    }
}
```

## 4. Tez 在 Hive 中的应用

Tez 是 Hive 的默认执行引擎，显著提升了 Hive 查询性能。

### 4.1 Hive on Tez 配置

```xml
<!-- hive-site.xml -->
<property>
    <name>hive.execution.engine</name>
    <value>tez</value>
    <description>使用 Tez 作为执行引擎</description>
</property>

<property>
    <name>hive.tez.container.size</name>
    <value>4096</value>
    <description>Tez 容器大小(MB)</description>
</property>

<property>
    <name>hive.tez.java.opts</name>
    <value>-Xmx3276m</value>
    <description>Tez JVM 参数</description>
</property>

<property>
    <name>tez.grouping.split-count</name>
    <value>128</value>
    <description>每个 DAG 的 map 任务数</description>
</property>

<property>
    <name>tez.runtime.io.sort.mb</name>
    <value>512</value>
    <description>排序缓冲区大小</description>
</property>
```

### 4.2 Hive 查询优化示例

```sql
-- 启用 Tez 执行
set hive.execution.engine=tez;

-- 启用向量化查询
set hive.vectorized.execution.enabled=true;

-- 启用 CBO (Cost-Based Optimizer)
set hive.cbo.enable=true;
set hive.compute.query.using.stats=true;

-- 示例查询：Tez 会自动优化为 DAG 执行
SELECT
    d.department_name,
    COUNT(*) as emp_count,
    AVG(e.salary) as avg_salary
FROM employees e
JOIN departments d ON e.department_id = d.department_id
WHERE e.hire_date > '2020-01-01'
GROUP BY d.department_name
HAVING COUNT(*) > 5;
```

## 5. 性能调优

### 5.1 内存优化

```xml
<!-- tez-site.xml -->
<property>
    <name>tez.task.resource.memory.mb</name>
    <value>2048</value>
</property>

<property>
    <name>tez.runtime.unordered.output.buffer.size-mb</name>
    <value>100</value>
    <description>无序输出缓冲区</description>
</property>

<property>
    <name>tez.runtime.shuffle.fetch.buffer.percent</name>
    <value>0.4</value>
    <description>Shuffle 获取缓冲区占比</description>
</property>
```

### 5.2 任务并行度

```xml
<property>
    <name>tez.grouping.min-size</name>
    <value>16777216</value>
    <description>最小分组大小(16MB)</description>
</property>

<property>
    <name>tez.grouping.max-size</name>
    <value>1073741824</value>
    <description>最大分组大小(1GB)</description>
</property>
```

## 6. Tez UI 监控

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Tez UI 界面                                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │ DAG Name: WordCountDAG                    Status: SUCCEEDED │   │
│  │ Application ID: application_1234567890_0001                │   │
│  │ Duration: 45.2s                                              │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐            │
│  │   Input     │───▶│  Tokenizer  │───▶│   Summer    │            │
│  │   (3/3)     │    │   (5/5)     │    │   (2/2)     │            │
│  │  12.3s      │    │   28.5s     │    │   15.2s     │            │
│  └─────────────┘    └─────────────┘    └─────────────┘            │
│                                                                     │
│  Vertex Details:                                                    │
│  ┌──────────┬────────┬─────────┬──────────┬────────────┐          │
│  │ Vertex   │ Tasks  │ Status  │ Duration │ Input Size │          │
│  ├──────────┼────────┼─────────┼──────────┼────────────┤          │
│  │ Input    │   3    │ SUCCESS │  12.3s   │   2.5 GB   │          │
│  │ Tokenizer│   5    │ SUCCESS │  28.5s   │   2.5 GB   │          │
│  │ Summer   │   2    │ SUCCESS │  15.2s   │  500 MB    │          │
│  └──────────┴────────┴─────────┴──────────┴────────────┘          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 7. 与 Spark 对比

| 特性 | Apache Tez | Apache Spark |
|------|------------|--------------|
| **执行模型** | DAG | DAG + RDD |
| **编程语言** | Java | Java/Scala/Python/R |
| **内存计算** | 有限支持 | 核心特性 |
| **适用场景** | Hive/Pig 查询加速 | 通用计算、ML、流处理 |
| **生态集成** | 深度集成 Hadoop | 独立生态 |
| **延迟** | 中（秒级） | 低（毫秒级） |
| **学习曲线** | 陡峭 | 平缓 |

## 8. 总结

Apache Tez 的优势和适用场景：

- **优势**：
  - 消除 MapReduce 的同步屏障
  - 深度集成 Hive、Pig
  - 复用 YARN 资源管理
  - 细粒度的资源控制

- **适用场景**：
  - 大规模 Hive SQL 查询
  - 复杂的 ETL 管道
  - 需要细粒度控制的批处理作业

- **局限性**：
  - 编程模型较底层
  - 生态不如 Spark 丰富
  - 流处理能力有限
