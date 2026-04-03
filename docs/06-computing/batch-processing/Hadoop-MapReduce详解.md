# Hadoop MapReduce 详解

## 1. 架构概述

Hadoop MapReduce 是一个分布式计算框架，用于处理和生成大规模数据集。其核心思想是将计算任务分解为两个阶段：Map（映射）阶段和 Reduce（归约）阶段。

```
┌─────────────────────────────────────────────────────────────────┐
│                    Hadoop MapReduce 架构                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐         ┌─────────────────────────────┐   │
│  │   JobClient     │────────▶│        JobTracker           │   │
│  │  (作业提交)      │         │      (作业调度管理)           │   │
│  └─────────────────┘         └──────────────┬──────────────┘   │
│                                             │                   │
│                                             ▼                   │
│                          ┌─────────────────────────────┐       │
│                          │      TaskTracker Pool       │       │
│                          │  ┌─────┐ ┌─────┐ ┌─────┐    │       │
│                          │  │TT-1 │ │TT-2 │ │TT-3 │... │       │
│                          │  └──┬──┘ └──┬──┘ └──┬──┘    │       │
│                          └─────┼───────┼───────┼────────┘       │
│                                │       │       │                │
│                                ▼       ▼       ▼                │
│                          ┌─────────────────────────────┐       │
│                          │         HDFS                │       │
│                          │    (分布式存储系统)           │       │
│                          └─────────────────────────────┘       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.1 核心组件

| 组件 | 职责 | 运行位置 |
|------|------|----------|
| **JobClient** | 提交作业、监控作业状态 | 客户端 |
| **JobTracker** | 资源分配、任务调度、故障恢复 | Master 节点 |
| **TaskTracker** | 执行任务、汇报心跳 | Slave 节点 |
| **Task** | 实际执行 Map/Reduce 计算 | TaskTracker 内 |

## 2. 执行流程详解

```
┌────────────────────────────────────────────────────────────────────┐
│                      MapReduce 执行流程                             │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│  Input ──▶ Split ──▶ Map ──▶ Shuffle ──▶ Reduce ──▶ Output        │
│         │          │          │           │                        │
│         │          │          │           │                        │
│         ▼          ▼          ▼           ▼                        │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐               │
│  │Block 1  │  │Record   │  │Partition│  │Merge    │               │
│  │Block 2  │──│Reader   │──│& Sort   │──│& Group  │               │
│  │Block 3  │  │(K,V)    │  │(K,V)    │  │(K,List) │               │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘               │
│                                                                    │
│  InputFormat   Mapper    Combiner/     Reducer                     │
│                           Partitioner                              │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

### 2.1 Map 阶段

```java
public class WordCountMapper extends Mapper<LongWritable, Text, Text, IntWritable> {

    private final static IntWritable one = new IntWritable(1);
    private Text word = new Text();

    @Override
    protected void map(LongWritable key, Text value, Context context)
            throws IOException, InterruptedException {
        // 输入：key=行偏移量, value=行内容
        String line = value.toString();
        StringTokenizer tokenizer = new StringTokenizer(line);

        while (tokenizer.hasMoreTokens()) {
            word.set(tokenizer.nextToken());
            // 输出：key=单词, value=1
            context.write(word, one);
        }
    }
}
```

**Map 阶段关键步骤：**

1. **InputFormat**：定义输入数据格式，默认使用 `TextInputFormat`
2. **RecordReader**：读取输入分片，转换为键值对
3. **Mapper**：用户自定义映射逻辑
4. **Partitioner**：决定数据发送到哪个 Reduce 任务
5. **Combiner**（可选）：本地预聚合，减少网络传输

### 2.2 Shuffle 阶段

Shuffle 是 MapReduce 中最复杂的阶段，负责 Map 输出到 Reduce 输入的数据传输：

```
┌─────────────────────────────────────────────────────────────────┐
│                         Shuffle 流程                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐                      ┌──────────────┐        │
│  │  Map Task 1  │                      │  Reduce Task │        │
│  │  ┌────────┐  │                      │  ┌────────┐  │        │
│  │  │Output  │  │    ┌──────────┐      │  │ Copy   │  │        │
│  │  │(内存)   │──┼───▶│Spill to │──────┼─▶│ Phase  │  │        │
│  │  │Buffer  │  │    │Disk      │      │  │(拉取)   │  │        │
│  │  └────────┘  │    └──────────┘      │  └───┬────┘  │        │
│  └──────────────┘                      │      │       │        │
│         │                              │  ┌───┴────┐  │        │
│         │                              │  │ Merge  │  │        │
│         │                              │  │ Sort   │  │        │
│         │                              │  └───┬────┘  │        │
│  ┌──────────────┐                      │      │       │        │
│  │  Map Task 2  │                      │  ┌───┴────┐  │        │
│  │  (同上...)    │──────────────────────┼─▶│Reduce  │  │        │
│  └──────────────┘                      │  │Function│  │        │
│                                        │  └────────┘  │        │
│                                        └──────────────┘        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Shuffle 优化参数：**

```xml
<!-- mapred-site.xml -->
<property>
    <name>mapreduce.task.io.sort.mb</name>
    <value>512</value>
    <description>Map 端排序缓冲区大小(MB)</description>
</property>

<property>
    <name>mapreduce.map.sort.spill.percent</name>
    <value>0.8</value>
    <description>缓冲区溢出阈值</description>
</property>

<property>
    <name>mapreduce.reduce.shuffle.parallelcopies</name>
    <value>10</value>
    <description>Reduce 并行拷贝线程数</description>
</property>
```

### 2.3 Reduce 阶段

```java
public class WordCountReducer extends Reducer<Text, IntWritable, Text, IntWritable> {

    private IntWritable result = new IntWritable();

    @Override
    protected void reduce(Text key, Iterable<IntWritable> values, Context context)
            throws IOException, InterruptedException {
        int sum = 0;
        // 相同 key 的 values 会被分组聚合
        for (IntWritable val : values) {
            sum += val.get();
        }
        result.set(sum);
        // 输出：key=单词, value=总计数
        context.write(key, result);
    }
}
```

## 3. 完整示例：WordCount

### 3.1 驱动程序

```java
public class WordCount {

    public static void main(String[] args) throws Exception {
        Configuration conf = new Configuration();

        // 设置作业名称
        Job job = Job.getInstance(conf, "word count");
        job.setJarByClass(WordCount.class);

        // 设置 Mapper 和 Reducer
        job.setMapperClass(WordCountMapper.class);
        job.setCombinerClass(WordCountReducer.class);
        job.setReducerClass(WordCountReducer.class);

        // 设置输出键值类型
        job.setOutputKeyClass(Text.class);
        job.setOutputValueClass(IntWritable.class);

        // 设置输入输出路径
        FileInputFormat.addInputPath(job, new Path(args[0]));
        FileOutputFormat.setOutputPath(job, new Path(args[1]));

        // 提交作业并等待完成
        System.exit(job.waitForCompletion(true) ? 0 : 1);
    }
}
```

### 3.2 编译与运行

```bash
# 编译
javac -cp $(hadoop classpath) WordCount.java
jar cvf wordcount.jar -C . .

# 运行
hadoop jar wordcount.jar WordCount /input /output

# 查看结果
hdfs dfs -cat /output/part-r-00000
```

## 4. 性能调优

### 4.1 输入分片优化

```java
// 自定义 InputFormat 控制分片大小
FileInputFormat.setMinInputSplitSize(job, 128 * 1024 * 1024);  // 128MB
FileInputFormat.setMaxInputSplitSize(job, 256 * 1024 * 1024);  // 256MB
```

**分片大小计算：**

```
splitSize = max(minSize, min(maxSize, blockSize))
```

### 4.2 压缩优化

```xml
<!-- 启用 Map 输出压缩 -->
<property>
    <name>mapreduce.map.output.compress</name>
    <value>true</value>
</property>

<property>
    <name>mapreduce.map.output.compress.codec</name>
    <value>org.apache.hadoop.io.compress.SnappyCodec</value>
</property>

<!-- 启用 Reduce 输出压缩 -->
<property>
    <name>mapreduce.output.fileoutputformat.compress</name>
    <value>true</value>
</property>
```

### 4.3 JVM 重用

```xml
<property>
    <name>mapreduce.job.jvm.numtasks</name>
    <value>10</value>
    <description>每个 JVM 实例运行的任务数</description>
</property>
```

### 4.4 推测执行

```xml
<!-- Map 推测执行 -->
<property>
    <name>mapreduce.map.speculative</name>
    <value>true</value>
</property>

<!-- Reduce 推测执行 -->
<property>
    <name>mapreduce.reduce.speculative</name>
    <value>true</value>
</property>
```

## 5. 与其他系统对比

| 特性 | Hadoop MapReduce | Apache Spark | Apache Flink |
|------|------------------|--------------|--------------|
| **执行模式** | 批处理 | 批处理+流处理 | 批处理+流处理 |
| **内存计算** | 否（磁盘为主） | 是 | 是 |
| **延迟** | 高（分钟级） | 中（秒级） | 低（毫秒级） |
| **容错** | 任务重算 | RDD 血缘 | Checkpoint |
| **API 丰富度** | 低 | 高 | 高 |
| **适用场景** | 离线批处理 | 迭代计算、ML | 实时流处理 |

## 6. 常见问题与解决方案

### 6.1 数据倾斜

```java
// 自定义 Partitioner 解决数据倾斜
public class SkewedPartitioner extends Partitioner<Text, IntWritable> {
    @Override
    public int getPartition(Text key, IntWritable value, int numPartitions) {
        // 对热点 key 进行二次分区
        if (isHotKey(key)) {
            return (key.hashCode() + random.nextInt(numPartitions)) % numPartitions;
        }
        return Math.abs(key.hashCode() % numPartitions);
    }
}
```

### 6.2 小文件问题

```java
// 使用 CombineTextInputFormat 合并小文件
job.setInputFormatClass(CombineTextInputFormat.class);
CombineTextInputFormat.setMaxInputSplitSize(job, 256 * 1024 * 1024);
```

## 7. 总结

Hadoop MapReduce 作为分布式计算的奠基性框架，具有以下特点：

- **优点**：成熟稳定、容错性强、适合超大规模离线计算
- **缺点**：延迟高、API 简陋、不适合迭代计算

在现代数据处理场景中，建议在以下情况使用 MapReduce：

1. 超大规模离线数据处理（PB级）
2. 与现有 Hadoop 生态系统深度集成
3. 对稳定性要求极高的生产环境
