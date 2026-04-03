# Pregel 模型详解

## 1. 概述

Pregel 是 Google 提出的分布式图计算框架，采用"以顶点为中心"（Vertex-Centric）的编程模型。其核心思想是模拟图算法的并行执行过程，通过超步（Superstep）迭代完成计算。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Pregel 计算模型                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  以顶点为中心的编程模型                                             │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      Superstep 1                             │   │
│  │                                                              │   │
│  │    ┌─────┐      ┌─────┐      ┌─────┐                       │   │
│  │    │ V1  │─────▶│ V2  │─────▶│ V3  │                       │   │
│  │    │ A:5 │      │ A:? │      │ A:? │                       │   │
│  │    └─────┘      └─────┘      └─────┘                       │   │
│  │       │                                              激活    │   │
│  │       └─────────────────────────────────────────────▶ 顶点   │   │
│  │                                                              │   │
│  │  每个顶点并行执行 Compute() 函数                              │   │
│  │  - 接收上一轮的 Messages                                      │   │
│  │  - 更新顶点状态 (Vertex Value)                                │   │
│  │  - 发送 Messages 给邻居                                       │   │
│  │  - 投票决定是否继续 (Vote to Halt)                            │   │
│  │                                                              │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      Superstep 2                             │   │
│  │                                                              │   │
│  │    ┌─────┐      ┌─────┐      ┌─────┐                       │   │
│  │    │ V1  │      │ V2  │─────▶│ V3  │                       │   │
│  │    │ A:5 │      │ A:6 │      │ A:? │                       │   │
│  │    │ HALT│      │     │      │     │                       │   │
│  │    └─────┘      └─────┘      └─────┘                       │   │
│  │       ▲                                              激活    │   │
│  │       └─────────────────────────────────────────────▶ 顶点   │   │
│  │                                                              │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│                    ... (直到所有顶点 Halt) ...                      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心概念

| 概念 | 说明 |
|------|------|
| **顶点 (Vertex)** | 图中的节点，包含唯一 ID 和可修改的值 |
| **边 (Edge)** | 连接顶点的有向边，可包含值 |
| **消息 (Message)** | 顶点间传递的数据，沿边发送 |
| **超步 (Superstep)** | 一轮全局同步的计算迭代 |
| **激活 (Active)** | 顶点是否参与当前超步的计算 |
| **Vote to Halt** | 顶点宣布完成计算，不再激活 |

## 2. Pregel 执行流程

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Pregel 执行流程                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Initialize ──▶ Superstep Loop ──▶ Terminate                       │
│       │              │                  │                          │
│       ▼              ▼                  ▼                          │
│  ┌─────────┐   ┌─────────────┐   ┌─────────────┐                  │
│  │ 加载图   │   │ 1. 接收消息  │   │ 所有顶点    │                  │
│  │ 数据到   │──▶│ 2. 执行计算  │──▶│ Vote to     │                  │
│  │ 各节点   │   │ 3. 发送消息  │   │ Halt?       │                  │
│  └─────────┘   │ 4. 全局同步  │   └─────────────┘                  │
│                └─────────────┘         │                           │
│                      ▲                 │ No                        │
│                      └─────────────────┘                           │
│                                                                     │
│  特点：                                                             │
│  - BSP (Bulk Synchronous Parallel) 模型                            │
│  - 每个超步结束时全局同步 (Barrier Synchronization)                  │
│  - 消息在超步间异步传递                                              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Pregel API

### 3.1 核心接口

```java
// Pregel 计算接口
public interface VertexProgram<I extends WritableComparable, 
                               V extends Writable,
                               E extends Writable,
                               M extends Writable> {
    
    /**
     * 在每个超步中执行
     * @param vertex 当前顶点
     * @param messages 接收到的消息
     */
    void compute(Vertex<I, V, E> vertex, Iterable<M> messages);
    
    /**
     * 初始化顶点值
     */
    void initialize(Vertex<I, V, E> vertex);
    
    /**
     * 聚合器 - 全局通信
     */
    void aggregate(String name, Writable value);
}

// 顶点类
public class Vertex<I, V, E> {
    private I id;                    // 顶点 ID
    private V value;                 // 顶点值
    private List<Edge<I, E>> edges;  // 出边列表
    private boolean active;          // 激活状态
    
    // 发送消息给邻居
    public void sendMessageToAllEdges(M message);
    public void sendMessageTo(I targetId, M message);
    
    // 投票停止
    public void voteToHalt();
}
```

### 3.2 单源最短路径 (SSSP) 实现

```java
public class SSSPVertexProgram implements 
    VertexProgram<LongWritable, DoubleWritable, FloatWritable, DoubleWritable> {
    
    public static final LongWritable SOURCE_ID = new LongWritable(1);
    
    @Override
    public void compute(Vertex<LongWritable, DoubleWritable, FloatWritable> vertex,
                       Iterable<DoubleWritable> messages) {
        
        double minDist = (vertex.getId().equals(SOURCE_ID)) ? 0 : Double.MAX_VALUE;
        
        // 接收消息，更新最短距离
        for (DoubleWritable msg : messages) {
            minDist = Math.min(minDist, msg.get());
        }
        
        // 如果距离被更新，继续传播
        if (minDist < vertex.getValue().get()) {
            vertex.setValue(new DoubleWritable(minDist));
            
            // 发送消息给所有邻居
            for (Edge<LongWritable, FloatWritable> edge : vertex.getEdges()) {
                double distance = minDist + edge.getValue().get();
                sendMessage(edge.getTargetVertexId(), new DoubleWritable(distance));
            }
        }
        
        // 投票停止
        vertex.voteToHalt();
    }
}
```

### 3.3 PageRank 实现

```java
public class PageRankVertexProgram implements
    VertexProgram<LongWritable, DoubleWritable, NullWritable, DoubleWritable> {
    
    private static final double DAMPING_FACTOR = 0.85;
    private static final double EPSILON = 0.001;
    
    @Override
    public void compute(Vertex<LongWritable, DoubleWritable, NullWritable> vertex,
                       Iterable<DoubleWritable> messages) {
        
        double sum = 0;
        for (DoubleWritable msg : messages) {
            sum += msg.get();
        }
        
        double oldRank = vertex.getValue().get();
        double newRank = (1 - DAMPING_FACTOR) + DAMPING_FACTOR * sum;
        
        vertex.setValue(new DoubleWritable(newRank));
        
        // 检查收敛
        if (Math.abs(newRank - oldRank) > EPSILON) {
            // 继续传播
            int edgeCount = vertex.getNumEdges();
            if (edgeCount > 0) {
                double sendValue = newRank / edgeCount;
                sendMessageToAllEdges(new DoubleWritable(sendValue));
            }
        } else {
            vertex.voteToHalt();
        }
    }
}
```

## 4. 聚合器（Aggregator）

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Pregel 聚合器机制                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Worker 1              Worker 2              Worker 3               │
│  ┌─────────┐          ┌─────────┐          ┌─────────┐             │
│  │ V1: 10  │          │ V3: 20  │          │ V5: 30  │             │
│  │ V2: 15  │          │ V4: 25  │          │ V6: 35  │             │
│  └────┬────┘          └────┬────┘          └────┬────┘             │
│       │                    │                    │                  │
│       │  local aggregate   │  local aggregate   │  local aggregate │
│       ▼                    ▼                    ▼                  │
│     ┌───┐                ┌───┐                ┌───┐               │
│     │25 │                │45 │                │65 │               │
│     └─┬─┘                └─┬─┘                └─┬─┘               │
│       │                    │                    │                  │
│       └────────────────────┼────────────────────┘                  │
│                            ▼                                       │
│                      ┌─────────────┐                               │
│                      │   Master    │                               │
│                      │  全局聚合    │                               │
│                      │  25+45+65   │                               │
│                      │    = 135    │                               │
│                      └──────┬──────┘                               │
│                             │                                      │
│                             ▼                                      │
│                      广播给所有 Worker                             │
│                                                                     │
│  常用聚合器：                                                        │
│  - LongSum / DoubleSum - 求和                                       │
│  - LongMax / DoubleMax - 最大值                                     │
│  - LongMin / DoubleMin - 最小值                                     │
│  - BooleanAnd / BooleanOr - 布尔运算                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```java
// 使用聚合器
public class CommunityDetection implements VertexProgram<...> {
    
    @Override
    public void compute(Vertex<...> vertex, Iterable<...> messages) {
        // 本地计算
        int community = detectCommunity(vertex);
        
        // 聚合到全局
        aggregate("communityCount", new LongWritable(1));
        
        // 获取全局聚合结果
        LongWritable total = getAggregatedValue("communityCount");
        System.out.println("Total communities: " + total.get());
    }
}
```

## 5. Combiner 优化

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Message Combiner 优化                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  无 Combiner：                                                      │
│  ┌─────────┐                      ┌─────────┐                      │
│  │   V1    │──▶ 5  ─────────────▶│   V2    │                      │
│  │         │──▶ 3  ─────────────▶│         │  3 条消息             │
│  │         │──▶ 7  ─────────────▶│         │                      │
│  └─────────┘                      └─────────┘                      │
│                                                                     │
│  有 Combiner (求和)：                                                │
│  ┌─────────┐                      ┌─────────┐                      │
│  │   V1    │──▶ 5                │   V2    │                      │
│  │         │──▶ 3  ─┐  合并      │         │                      │
│  │         │──▶ 7  ─┴─▶ 15 ────▶│         │  1 条消息             │
│  └─────────┘                      └─────────┘                      │
│                                                                     │
│  效果：减少网络传输，降低内存占用                                    │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

```java
// 自定义 Combiner
public class MinValueCombiner implements MessageCombiner<LongWritable, DoubleWritable> {
    
    @Override
    public DoubleWritable combine(Iterable<DoubleWritable> messages) {
        double min = Double.MAX_VALUE;
        for (DoubleWritable msg : messages) {
            min = Math.min(min, msg.get());
        }
        return new DoubleWritable(min);
    }
}
```

## 6. Pregel 系统架构

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Pregel 系统架构                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                        Master                                  │ │
│  │  - 协调超步执行                                                │ │
│  │  - 收集 Worker 完成信号                                        │ │
│  │  - 全局同步点 (Barrier)                                        │ │
│  │  - 处理故障恢复                                                │ │
│  └───────────────────────┬───────────────────────────────────────┘ │
│                          │                                          │
│           ┌──────────────┼──────────────┐                          │
│           │              │              │                          │
│           ▼              ▼              ▼                          │
│  ┌─────────────────────────────────────────────────────────────┐  │
│  │                      Worker Pool                             │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │  │
│  │  │  Worker 1   │  │  Worker 2   │  │  Worker N   │          │  │
│  │  │ ┌─────────┐ │  │ ┌─────────┐ │  │ ┌─────────┐ │          │  │
│  │  │ │ V1, V2  │ │  │ │ V3, V4  │ │  │ │ V5, V6  │ │          │  │
│  │  │ │ In-Mem  │ │  │ │ In-Mem  │ │  │ │ In-Mem  │ │          │  │
│  │  │ │ Store   │ │  │ │ Store   │ │  │ │ Store   │ │          │  │
│  │  │ └─────────┘ │  │ └─────────┘ │  │ └─────────┘ │          │  │
│  │  │ - 执行计算  │  │ - 执行计算  │  │ - 执行计算  │          │  │
│  │  │ - 收发消息  │  │ - 收发消息  │  │ - 收发消息  │          │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘          │  │
│  └─────────────────────────────────────────────────────────────┘  │
│                                                                     │
│  数据分区策略：                                                      │
│  - Hash Partitioning: vertex_id % num_workers                     │
│  - Range Partitioning: 按 ID 范围                                  │
│  - Custom Partitioning: 用户自定义                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 7. 容错机制

```
┌─────────────────────────────────────────────────────────────────────┐
│                   Pregel 容错机制                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Checkpoint 机制：                                                  │
│                                                                     │
│  Superstep 1    Superstep 5    Superstep 10    Failure    Recover  │
│       │              │              │             │          │      │
│       ▼              ▼              ▼             ▼          ▼      │
│     ┌───┐          ┌───┐          ┌───┐        ┌───┐      ┌───┐    │
│     │CP1│─────────▶│CP2│─────────▶│CP3│──X────▶│   │─────▶│CP3│    │
│     └───┘          └───┘          └───┘        └───┘      └───┘    │
│       ▲                                                      │      │
│       └──────────────────────────────────────────────────────┘      │
│                    从 CP3 恢复，重放 Superstep 11                    │
│                                                                     │
│  Checkpoint 内容：                                                  │
│  - 顶点值 (Vertex Values)                                           │
│  - 边值 (Edge Values)                                               │
│  - 出消息队列 (Outgoing Messages)                                    │
│  - 聚合器值 (Aggregator Values)                                     │
│                                                                     │
│  故障检测：                                                          │
│  - Master 通过心跳检测 Worker                                        │
│  - 超时未响应则认为故障                                              │
│  - 重新分配分区到其他 Worker                                         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 8. 与其他图计算框架对比

| 特性 | Pregel | GraphX | Giraph | PowerGraph |
|------|--------|--------|--------|------------|
| **提出者** | Google | Apache | Apache | CMU |
| **执行模型** | BSP | BSP | BSP | GAS |
| **存储** | 内存 | 内存/RDD | 内存 | 内存 |
| **容错** | Checkpoint | RDD 血缘 | Checkpoint | Checkpoint |
| **编程模型** | 顶点中心 | 顶点中心 | 顶点中心 | 顶点+边中心 |
| **分区策略** | Hash/Range | 边切割 | Hash | 顶点切割 |
| **适用场景** | 通用图计算 | Spark 生态 | 大规模图 | 幂律图 |

## 9. 总结

Pregel 模型的核心优势：

1. **简单易用**：以顶点为中心的编程模型，隐藏分布式复杂性
2. **高效并行**：BSP 模型适合图算法的天然并行性
3. **容错性强**：基于 Checkpoint 的故障恢复
4. **可扩展性好**：支持大规模图处理

最佳实践：
- 合理使用 Combiner 减少消息传输
- 使用聚合器进行全局通信
- 及时调用 voteToHalt() 减少计算量
- 根据图特性选择合适的分区策略
