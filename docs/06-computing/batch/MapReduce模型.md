# MapReduce模型 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

MapReduce是一种用于大规模数据并行处理的编程模型和执行框架，由Google提出，通过"Map（映射）+ Reduce（归约）"的两阶段计算抽象，实现了在普通硬件集群上的海量数据（PB级）处理能力，是大数据处理领域的奠基性技术。

---

## 一、核心概念

### 1.1 定义与原理

MapReduce采用**分治（Divide and Conquer）**思想，将复杂的数据处理任务分解为两个阶段：

**Map阶段**：
- 输入数据被切分为多个分片（Split）
- 每个Mapper并行处理一个数据分片
- 将输入键值对 $(k_1, v_1)$ 映射为中间键值对 $(k_2, v_2)$

**Reduce阶段**：
- 相同键的中间值被分组聚合
- 每个Reducer处理一组相同键的数据
- 将中间键值对 $(k_2, [v_2])$ 归约为输出 $(k_3, v_3)$

**核心原理**：
```
数据处理 = Map(分解转换) + Shuffle(重新分布) + Reduce(聚合归约)
```

### 1.2 关键特性

- **水平扩展**：数据量增加时，增加机器即可线性扩展
- **容错性**：自动检测和处理节点故障，重新调度任务
- **数据本地性**：优先在数据所在节点执行计算，减少网络传输
- **简单编程模型**：开发者只需关注Map和Reduce逻辑
- **异构数据处理**：可处理结构化、半结构化、非结构化数据

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 日志分析 | ⭐⭐⭐⭐⭐ | 大规模日志统计、聚合分析 |
| ETL数据清洗 | ⭐⭐⭐⭐⭐ | 数据转换、过滤、格式化 |
| 倒排索引构建 | ⭐⭐⭐⭐⭐ | 搜索引擎索引构建 |
| 机器学习预处理 | ⭐⭐⭐⭐⭐ | 特征提取、数据归一化 |
| 图计算 | ⭐⭐⭐⭐ | 迭代的图算法（通过Pregel扩展）|
| 实时计算 | ⭐⭐ | 延迟高（分钟级），不适合实时场景 |
| 迭代算法 | ⭐⭐⭐ | 需要多轮MR作业，效率低 |

---

## 二、技术细节

### 2.1 MapReduce架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                   MapReduce 架构 (YARN模式)                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   ResourceManager                        │   │
│  │   • 全局资源管理                                          │   │
│  │   • 调度策略：FIFO / Capacity / Fair                      │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│              ┌─────────────┼─────────────┐                      │
│              ▼             ▼             ▼                      │
│  ┌──────────────────┐ ┌──────────┐ ┌──────────────────┐       │
│  │   NodeManager 1  │ │   ...    │ │   NodeManager N  │       │
│  │   ┌──────────┐   │ │          │ │   ┌──────────┐   │       │
│  │   │ Container│   │ │          │ │   │ Container│   │       │
│  │   │ ┌──────┐ │   │ │          │ │   │ ┌──────┐ │   │       │
│  │   │ │Mapper│ │   │ │          │ │   │ │Mapper│ │   │       │
│  │   │ │ /    │ │   │ │          │ │   │ │Reduce│ │   │       │
│  │   │ │Reduce│ │   │ │          │ │   │ │  /   │ │   │       │
│  │   │ └──────┘ │   │ │          │ │   │ └──────┘ │   │       │
│  │   └──────────┘   │ │          │ │   └──────────┘   │       │
│  └──────────────────┘ └──────────┘ └──────────────────┘       │
│                                                                 │
│  【作业执行流程】                                                │
│                                                                 │
│  Client提交Job → JobClient初始化 → 获取JobID                  │
│       │                                              │          │
│       ▼                                              ▼          │
│  复制Job资源    →    RM启动MRAppMaster    →    申请Containers  │
│  (jar/conf)         (作业协调者)                (Mapper/Reducer)│
│       │                                              │          │
│       ▼                                              ▼          │
│  监控进度 ←────────── 任务执行 ──────────────→ 任务完成汇报     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 MapReduce编程模型

#### 完整数据流

```
┌─────────────────────────────────────────────────────────────────┐
│                 MapReduce 完整数据流                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【输入分片】                                                    │
│  InputFormat → InputSplit[] → RecordReader → (K1, V1)         │
│                                                                 │
│       ↓ Mapper处理                                               │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    Map 阶段                              │   │
│  │  map(K1, V1) → List<(K2, V2)>                           │   │
│  │  • 解析输入数据                                          │   │
│  │  • 执行业务转换                                          │   │
│  │  • 输出中间键值对                                        │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│       ↓ 分区（Partitioner）                                     │
│  决定(K2, V2)发送到哪个Reducer                                 │
│  默认：hash(K2) % numReducers                                  │
│                                                                 │
│       ↓ 排序                                                   │
│  内存缓冲区溢写 → 分区排序 → 合并（Combiner可选）               │
│                                                                 │
│       ↓ Shuffle（数据拉取）                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   Shuffle 阶段                           │   │
│  │  • Reducer从各Mapper拉取属于自己分区的数据               │   │
│  │  • 归并排序（Merge Sort）                                │   │
│  │  • 按键分组：Group(K2, Iterator<V2>)                    │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│       ↓ Reduce处理                                             │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   Reduce 阶段                            │   │
│  │  reduce(K2, Iterator<V2>) → List<(K3, V3)>              │   │
│  │  • 聚合中间结果                                          │   │
│  │  • 生成最终输出                                          │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│       ↓ 输出                                                   │
│  OutputFormat → RecordWriter → HDFS                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

#### MapReduce Java API示例

```java
// WordCount 示例

// Mapper类
public class WordCountMapper extends Mapper<LongWritable, Text, Text, IntWritable> {
    private final static IntWritable one = new IntWritable(1);
    private Text word = new Text();
    
    @Override
    protected void map(LongWritable key, Text value, Context context) 
            throws IOException, InterruptedException {
        String[] words = value.toString().split("\\s+");
        for (String w : words) {
            word.set(w);
            context.write(word, one);  // 输出 (word, 1)
        }
    }
}

// Reducer类
public class WordCountReducer extends Reducer<Text, IntWritable, Text, IntWritable> {
    @Override
    protected void reduce(Text key, Iterable<IntWritable> values, Context context) 
            throws IOException, InterruptedException {
        int sum = 0;
        for (IntWritable val : values) {
            sum += val.get();
        }
        context.write(key, new IntWritable(sum));  // 输出 (word, sum)
    }
}

// Job配置
public class WordCount {
    public static void main(String[] args) throws Exception {
        Configuration conf = new Configuration();
        Job job = Job.getInstance(conf, "word count");
        
        job.setJarByClass(WordCount.class);
        job.setMapperClass(WordCountMapper.class);
        job.setCombinerClass(WordCountReducer.class);  // 可选的Combiner
        job.setReducerClass(WordCountReducer.class);
        
        job.setOutputKeyClass(Text.class);
        job.setOutputValueClass(IntWritable.class);
        
        FileInputFormat.addInputPath(job, new Path(args[0]));
        FileOutputFormat.setOutputPath(job, new Path(args[1]));
        
        System.exit(job.waitForCompletion(true) ? 0 : 1);
    }
}
```

### 2.3 Shuffle机制详解

```
┌─────────────────────────────────────────────────────────────────┐
│                   Shuffle 机制详解                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【Map端 Shuffle】                                               │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    Mapper 节点                           │   │
│  │                                                          │   │
│  │  输出缓冲区 (MapOutputBuffer)                            │   │
│  │  ┌─────────────────────────────────────────────────────┐ │   │
│  │  │ 环形缓冲区 (默认100MB)                               │ │   │
│  │  │                                                     │ │   │
│  │  │  [元数据区]  <-- 分割线 -->  [数据区]               │ │   │
│  │  │  (索引、校验和)        (KV记录)                     │ │   │
│  │  └─────────────────────────────────────────────────────┘ │   │
│  │                          │                               │   │
│  │                          ▼ (达到阈值80%，启动溢写)        │   │
│  │  ┌─────────────────────────────────────────────────────┐ │   │
│  │  │ 溢写线程                                            │ │   │
│  │  │ • 按分区排序（QuickSort）                           │ │   │
│  │  │ • 分区内按键排序                                    │ │   │
│  │  │ • 可选Combiner聚合                                  │ │   │
│  │  │ • 写入本地磁盘 (spill文件)                          │ │   │
│  │  └─────────────────────────────────────────────────────┘ │   │
│  │                          │                               │   │
│  │                          ▼ (Map完成，归并所有spill文件)   │   │
│  │  ┌─────────────────────────────────────────────────────┐ │   │
│  │  │ 归并排序 (Merge)                                    │ │   │
│  │  │ • 多路归并 (默认10路)                               │ │   │
│  │  │ • 生成最终输出文件 (index + data)                   │ │   │
│  │  │ • 通知Reduce拉取                                    │ │   │
│  │  └─────────────────────────────────────────────────────┘ │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  【Reduce端 Shuffle】                                            │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   Reducer 节点                           │   │
│  │                                                          │   │
│  │  1. Copy阶段                                            │   │
│  │     • 启动Fetcher线程从各Mapper HTTP拉取数据            │   │
│  │     • 使用HttpServer响应Reduce请求                      │   │
│  │     • 拉取数据写入内存缓冲区或磁盘                        │   │
│  │                                                          │   │
│  │  2. Merge阶段                                           │   │
│  │     ┌─────────────────────────────────────────────┐     │   │
│  │     │ 内存缓冲区 (默认与JVM堆内存成比例)           │     │   │
│  │     │         ↓ 达到阈值                           │     │   │
│  │     │ 内存 → 归并 → 磁盘文件                       │     │   │
│  │     │         ↓ 最终归并                           │     │   │
│  │     │ 磁盘文件 + 内存数据 → 最终归并排序           │     │   │
│  │     └─────────────────────────────────────────────┘     │   │
│  │                                                          │   │
│  │  3. Reduce阶段                                          │   │
│  │     • 按键分组（GroupingComparator）                    │   │
│  │     • 调用reduce()处理每组数据                          │   │
│  │                                                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Shuffle优化参数**：

| 参数 | 默认值 | 说明 |
|-----|-------|------|
| mapreduce.task.io.sort.mb | 100MB | Map端环形缓冲区大小 |
| mapreduce.map.sort.spill.percent | 0.8 | 溢写阈值比例 |
| mapreduce.task.io.sort.factor | 10 | 归并因子（合并流数）|
| mapreduce.reduce.shuffle.parallelcopies | 5 | Reduce端并行拉取数 |
| mapreduce.reduce.shuffle.input.buffer.percent | 0.7 | Reduce端缓冲区比例 |

### 2.4 容错机制

```
┌─────────────────────────────────────────────────────────────────┐
│                   MapReduce 容错机制                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【任务失败检测】                                                │
│                                                                 │
│  TaskTracker/NodeManager 定期发送心跳给 JobTracker/RM          │
│       │                                                         │
│       ├── 心跳超时（默认10分钟）→ 标记节点失效                  │
│       └── 进度汇报 → 记录任务进度                               │
│                                                                 │
│  【任务失败类型与处理】                                          │
│                                                                 │
│  1. 任务执行失败 (Task Failure)                                │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ • 异常抛出 / JVM崩溃                                │    │
│     │ • 处理：                                            │    │
│     │   - 记录失败原因                                    │    │
│     │   - 重新调度到新节点执行                            │    │
│     │   - 最多重试4次（默认mapreduce.map.maxattempts）   │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  2. 节点失败 (Node Failure)                                    │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ • 心跳超时 / 节点宕机                               │    │
│     │ • 处理：                                            │    │
│     │   - 将该节点所有运行中任务标记为失败                │    │
│     │   - 重新调度到健康节点                              │    │
│     │   - 已完成的Map任务输出丢失，需重新执行             │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  3. 作业失败 (Job Failure)                                     │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ • 达到最大失败比例（mapreduce.map.failures.maxpercent）│   │
│     │ • 处理：                                            │    │
│     │   - 终止整个作业                                    │    │
│     │   - 清理临时数据                                    │    │
│     │   - 返回失败状态                                    │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
│  【推测执行（Speculative Execution）】                           │
│                                                                 │
│  问题："拖后腿"任务（Straggler）延缓整个作业                    │
│                                                                 │
│  解决方案：                                                      │
│  • 监控所有任务的进度                                            │
│  • 发现进度明显慢于平均的任务                                    │
│  • 在备用节点启动相同任务的备份                                  │
│  • 任一完成即终止另一个                                          │
│                                                                 │
│  配置：                                                          │
│  mapreduce.map.speculative: true                                │
│  mapreduce.reduce.speculative: true                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.5 性能优化

```
┌─────────────────────────────────────────────────────────────────┐
│                   MapReduce 性能优化                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 数据本地性优化 (Data Locality)                              │
│                                                                 │
│     优先顺序：                                                   │
│     数据本地 (Data-local) > 机架本地 (Rack-local) > 机架间       │
│     延迟：0ms                ~1ms                  ~10ms+        │
│                                                                 │
│     优化方法：                                                   │
│     • 控制InputSplit大小 = block size (默认128MB)               │
│     • 增加mapreduce.jobtracker.taskcache.levels                │
│     • 使用CombineFileInputFormat处理小文件                      │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  2. 数据倾斜优化 (Data Skew)                                    │
│                                                                 │
│     问题：某些key的数据量远大于其他                              │
│     导致：某个Reducer处理时间过长                                │
│                                                                 │
│     解决方案：                                                   │
│     ┌─────────────────────────────────────────────────────┐    │
│     │ 方案A：自定义分区器                                 │    │
│     │   - 打散热点key（如添加随机前缀）                   │    │
│     │   - 二次MR聚合结果                                  │    │
│     │                                                     │    │
│     │ 方案B：增大Reducer数量                            │    │
│     │   - 减少单个Reducer负载                             │    │
│     │                                                     │    │
│     │ 方案C：使用Combiner                               │    │
│     │   - Map端预聚合，减少传输                           │    │
│     └─────────────────────────────────────────────────────┘    │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  3. 小文件问题优化                                              │
│                                                                 │
│     问题：大量小文件（< block size）                             │
│     导致：大量Map任务启动开销                                    │
│                                                                 │
│     解决方案：                                                   │
│     • 使用CombineFileInputFormat合并输入                        │
│     • 数据预处理合并（SequenceFile/Parquet）                    │
│     • 使用Har（Hadoop Archive）归档                             │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  4. JVM重用优化                                                 │
│                                                                 │
│     问题：每个任务启动新JVM开销大                                │
│                                                                 │
│     优化：JVM重用                                                │
│     mapreduce.job.jvm.numtasks: 10  # 一个JVM运行10个任务       │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  5. 压缩优化                                                    │
│                                                                 │
│     Map输出压缩：                                                │
│     mapreduce.map.output.compress: true                         │
│     mapreduce.map.output.compress.codec: SnappyCodec            │
│                                                                 │
│     Reduce输出压缩：                                             │
│     mapreduce.output.fileoutputformat.compress: true            │
│                                                                 │
│     压缩格式选择：                                               │
│     • 速度优先：Snappy、LZO                                     │
│     • 压缩比优先：Gzip、Bzip2                                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.6 与Spark对比

```
┌─────────────────────────────────────────────────────────────────┐
│                   MapReduce vs Spark 对比                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【执行模型对比】                                                │
│                                                                 │
│  MapReduce:                                                     │
│  磁盘 → Map → 磁盘 → Reduce → 磁盘                              │
│  （每轮计算都读写HDFS，磁盘IO重）                                │
│                                                                 │
│  Spark:                                                         │
│  磁盘 → 内存计算 → 内存计算 → 内存计算 → 磁盘（可选）             │
│  （中间结果缓存内存，支持迭代计算）                              │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【架构对比】                                                    │
│                                                                 │
│  特性              │  MapReduce         │  Spark                │
│  ──────────────────┼────────────────────┼───────────────────────│
│  执行引擎          │  Job/Task粒度      │  DAG调度 + 任务流水线 │
│  内存使用          │  磁盘为主          │  内存为主             │
│  迭代计算          │  每轮都是独立Job   │  缓存RDD，支持迭代    │
│  容错机制          │  任务重算          │  RDD血缘 + 检查点     │
│  编程模型          │  Map + Reduce      │  丰富的算子（map/filter/join等）│
│  SQL支持           │  Hive (MR引擎)     │  Spark SQL            │
│  流处理            │  不支持            │  Spark Streaming      │
│  机器学习          │  Mahout (逐步迁移) │  MLlib                │
│  图计算            │  不支持            │  GraphX               │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【性能对比】                                                    │
│                                                                 │
│  场景                    │ MapReduce    │ Spark      │ 提升倍数  │
│  ────────────────────────┼──────────────┼────────────┼──────────│
│  WordCount (单次)        │ 120s         │ 80s        │ 1.5x     │
│  迭代ML算法 (10轮)       │ 1200s        │ 100s       │ 12x      │
│  交互式查询              │ 60s          │ 2s         │ 30x      │
│  图算法 (PageRank)       │ 不支持       │ 60s        │ -        │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  【选型建议】                                                    │
│                                                                 │
│  选择 MapReduce：                                                │
│  • 超大规模数据（PB级）且内存不足                                │
│  • 简单的一次性批处理任务                                        │
│  • 已有成熟MR生态，迁移成本高                                    │
│  • 对稳定性要求极高，Spark复杂场景调试困难                       │
│                                                                 │
│  选择 Spark：                                                    │
│  • 迭代计算（机器学习、图计算）                                  │
│  • 交互式数据分析                                                │
│  • 实时流处理需求                                                │
│  • 需要SQL/DataFrame高级API                                      │
│  • 内存充足（集群内存/数据 > 1:3）                               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 三、系统对比

### 3.1 批处理框架对比矩阵

| 维度 | MapReduce | Spark Core | Flink DataSet | Tez |
|------|-----------|------------|---------------|-----|
| **执行模型** | 两阶段（Map+Reduce） | DAG执行 | DAG执行 | DAG执行 |
| **中间结果存储** | HDFS | 内存（RDD） | 内存/磁盘 | 内存 |
| **迭代支持** | 差（多轮Job） | 优秀 | 优秀 | 良好 |
| **容错机制** | 任务重算 | RDD血缘 | 检查点 | 任务重算 |
| **延迟** | 分钟级 | 秒级 | 秒级 | 秒级 |
| **SQL支持** | Hive | Spark SQL | Table API | Hive on Tez |
| **资源管理** | YARN/Mesos | YARN/Mesos/K8s | YARN/Mesos/K8s | YARN |
| **生态成熟度** | 非常成熟 | 非常成熟 | 快速迭代 | Hive生态 |

### 3.2 选型决策树

```
批处理框架选型决策
│
├─ 是否有迭代计算需求？
│  ├─ 是 → Spark / Flink（内存迭代优势）
│  └─ 否 → 继续判断
│
├─ 是否需要极低延迟？
│  ├─ 是 → Spark / Flink（DAG优化）
│  └─ 否 → MapReduce可用
│
├─ 是否需要流批一体？
│  ├─ 是 → Flink / Spark Structured Streaming
│  └─ 否 → 继续判断
│
├─ 集群内存资源？
│  ├─ 充足（内存/数据 > 1:3）→ Spark / Flink
│  └─ 有限 → MapReduce / Tez
│
├─ 已有Hadoop生态？
│  ├─ 是且稳定 → MapReduce / Hive
│  └─ 是且要升级 → Spark / Flink
│
└─ 最终推荐
   ├─ 通用场景 → Apache Spark
   ├─ 流批一体 → Apache Flink
   └─ 历史稳定 → MapReduce
```

---

## 四、实践指南

### 4.1 MapReduce生产配置

```xml
<!-- mapred-site.xml 生产配置 -->
<configuration>
    <!-- 内存配置 -->
    <property>
        <name>mapreduce.map.memory.mb</name>
        <value>2048</value>
    </property>
    <property>
        <name>mapreduce.reduce.memory.mb</name>
        <value>4096</value>
    </property>
    <property>
        <name>mapreduce.map.java.opts</name>
        <value>-Xmx1638m</value>  <!-- 0.8 * map memory -->
    </property>
    <property>
        <name>mapreduce.reduce.java.opts</name>
        <value>-Xmx3276m</value>  <!-- 0.8 * reduce memory -->
    </property>
    
    <!-- Shuffle优化 -->
    <property>
        <name>mapreduce.task.io.sort.mb</name>
        <value>256</value>
    </property>
    <property>
        <name>mapreduce.map.sort.spill.percent</name>
        <value>0.8</value>
    </property>
    
    <!-- 压缩 -->
    <property>
        <name>mapreduce.map.output.compress</name>
        <value>true</value>
    </property>
    <property>
        <name>mapreduce.map.output.compress.codec</name>
        <value>org.apache.hadoop.io.compress.SnappyCodec</value>
    </property>
    
    <!-- 推测执行 -->
    <property>
        <name>mapreduce.map.speculative</name>
        <value>true</value>
    </property>
    <property>
        <name>mapreduce.reduce.speculative</name>
        <value>false</value>  <!-- Reduce推测执行可能浪费资源 -->
    </property>
    
    <!-- 慢启动 -->
    <property>
        <name>mapreduce.job.reduce.slowstart.completedmaps</name>
        <value>0.95</value>  <!-- 95% Map完成才启动Reduce -->
    </property>
</configuration>
```

### 4.2 最佳实践

1. **Combiner合理使用**
   - 适用于满足结合律的聚合操作（sum、count、max）
   - 在Map端预聚合，减少Shuffle数据量
   - 注意：求平均值不能用Combiner（需要sum+count）

2. **分区优化**
   - 确保数据均匀分布到各Reducer
   - 自定义Partitioner处理热点key
   - 合理设置Reducer数量：$0.95 \times (节点数 \times 每个节点最大容器数)$

3. **数据格式选择**
   - 优先使用列式存储（Parquet、ORC）
   - 使用压缩（Snappy推荐）
   - 避免小文件，使用CombineFileInputFormat

4. **JVM调优**
   - 启用JVM重用
   - 调整堆内存比例
   - 使用G1GC减少停顿

5. **监控指标**
   - Map/Reduce任务执行时间
   - Shuffle数据量
   - 数据本地性比例
   - 任务失败率

### 4.3 常见问题

**Q1: MapReduce vs Hive/Pig如何选择？**
A:
- Hive/Pig是高级抽象，最终生成MapReduce/Tez/Spark任务
- 简单ETL用Hive SQL，复杂逻辑用原生MR
- 性能敏感场景用原生MR或Spark

**Q2: Map任务数过多？**
A:
- 检查小文件问题
- 调整InputSplit大小：
  ```java
  // 设置最小分片大小为256MB
  FileInputFormat.setMinInputSplitSize(job, 256 * 1024 * 1024);
  ```
- 使用CombineFileInputFormat

**Q3: Reduce阶段OOM？**
A:
- 增加Reduce内存
- 优化数据倾斜
- 减少单次reduce处理的数据量
- 启用溢写阈值调整

**Q4: Shuffle阶段网络瓶颈？**
A:
- 启用Map输出压缩
- 使用Combiner减少数据量
- 调整Reduce拉取并行度
- 优化网络拓扑

---

## 五、形式化分析

### 5.1 MapReduce形式化定义

**定义（MapReduce计算模型）**：
给定输入数据集 $D$，MapReduce计算由以下函数定义：

$$Map: (k_1, v_1) \rightarrow [(k_2, v_2)]$$
$$Reduce: (k_2, [v_2]) \rightarrow [(k_3, v_3)]$$

**执行流程**：
1. **输入分片**：$D \rightarrow \{S_1, S_2, ..., S_m\}$
2. **Map阶段**：$\forall i \in [1,m]: Map(S_i) \rightarrow M_i$
3. **Shuffle阶段**：$\{M_1, ..., M_m\} \rightarrow \{R_1, ..., R_n\}$（按键分区）
4. **Reduce阶段**：$\forall j \in [1,n]: Reduce(R_j) \rightarrow O_j$
5. **输出合并**：$\{O_1, ..., O_n\} \rightarrow Output$

### 5.2 正确性保证

**定理（MapReduce正确性）**：
若Map和Reduce函数满足：
- Map是确定性的
- Reduce是满足结合律的聚合操作
则MapReduce计算结果与数据分片方式无关。

**证明**：
- Map阶段各分片独立处理，无交叉依赖
- Reduce按key聚合，同一key的所有value最终进入同一Reducer
- 结合律保证聚合顺序不影响最终结果 ∎

### 5.3 复杂度分析

**时间复杂度**：

设：
- $N$：输入数据总量
- $M$：Map任务数
- $R$：Reduce任务数
- $C_{map}$：单条记录Map处理时间
- $C_{reduce}$：单组Reduce处理时间
- $C_{shuffle}$：单位数据传输时间

$$T_{total} = T_{map} + T_{shuffle} + T_{reduce}$$
$$T_{map} = O(\frac{N}{M} \times C_{map})$$
$$T_{shuffle} = O(N' \times C_{shuffle})$$  
其中 $N'$ 为Shuffle数据量
$$T_{reduce} = O(\frac{K}{R} \times C_{reduce})$$
其中 $K$ 为不同key的数量

**空间复杂度**：

$$S_{map} = O(B + S)$$
其中 $B$ 为缓冲区大小，$S$ 为单条记录最大大小

$$S_{reduce} = O(M' \times S)$$
其中 $M'$ 为单个Reduce处理的最大数据量

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [HDFS分布式文件系统](../../04-storage/HDFS详解.md)
- [YARN资源管理](../../03-scheduling/YARN架构.md)

### 6.2 下游应用

- [Hive数据仓库](../../07-data-warehouse/Hive详解.md)
- [图计算框架](../graph/图计算框架.md)

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| Spark | 演进 | Spark基于MR思想，优化了中间结果存储 |
| DAG计算 | 扩展 | Tez/Spark使用DAG模型优化MR的两阶段限制 |
| 流处理 | 对比 | 批处理处理有界数据，流处理处理无界数据 |

---

## 七、参考资源

### 7.1 学术论文

1. [MapReduce: Simplified Data Processing on Large Clusters](https://dl.acm.org/doi/10.1145/1327452.1327492) - Dean & Ghemawat, OSDI 2004
2. [The Hadoop Distributed File System](https://ieeexplore.ieee.org/document/5496972) - Shvachko et al., MSST 2010
3. [Resilient Distributed Datasets: A Fault-Tolerant Abstraction for In-Memory Cluster Computing](https://www.usenix.org/conference/nsdi12/technical-sessions/presentation/zaharia) - Zaharia et al., NSDI 2012
4. [Apache Hadoop YARN: Yet Another Resource Negotiator](https://dl.acm.org/doi/10.1145/2523616.2523633) - Vavilapalli et al., SOCC 2013

### 7.2 开源项目

1. [Apache Hadoop MapReduce](https://hadoop.apache.org/docs/stable/hadoop-mapreduce-client/hadoop-mapreduce-client-core/MapReduceTutorial.html) - 官方实现
2. [Apache Spark](https://spark.apache.org/) - 下一代大数据计算引擎
3. [Apache Tez](https://tez.apache.org/) - 基于DAG的批处理引擎
4. [Apache Hive](https://hive.apache.org/) - 基于MR的数据仓库

### 7.3 学习资料

1. [Hadoop权威指南](https://www.oreilly.com/library/view/hadoop-the-definitive/9781491901687/) - O'Reilly经典书籍
2. [MapReduce设计模式](https://www.oreilly.com/library/view/mapreduce-design-patterns/9781449341954/) - 常见模式总结
3. [Hadoop性能调优](https://cwiki.apache.org/confluence/display/HADOOP/PerformanceTuning) - 官方调优指南

### 7.4 相关文档

- [流处理框架对比](../stream/流处理框架对比.md)
- [图计算框架](../graph/图计算框架.md)
- [YARN资源调度](../../03-scheduling/YARN架构.md)

---

**维护者**：项目团队
**最后更新**：2026年
