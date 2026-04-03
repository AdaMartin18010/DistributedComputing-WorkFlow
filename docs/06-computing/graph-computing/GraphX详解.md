# Apache Spark GraphX 详解

## 1. 架构概述

GraphX 是 Apache Spark 的图计算组件，在 Spark 的基础上扩展了图处理功能。它将图计算与 Spark 的批处理能力相结合，提供了灵活的图算法实现和高效的图并行计算。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    GraphX 架构                                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Spark Core                                  │ │
│  │                 (RDD Foundation)                               │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    GraphX Layer                                │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │  Graph      │  │  VertexRDD  │  │  EdgeRDD            │   │ │
│  │  │  Abstraction│  │  (V-Table)  │  │  (E-Table)          │   │ │
│  │  └──────┬──────┘  └─────────────┘  └─────────────────────┘   │ │
│  │         │                                                      │ │
│  │         ▼                                                      │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │                Graph Algorithms                          │  │ │
│  │  │  - PageRank        - Connected Components                │  │ │
│  │  │  - Triangle Count  - Shortest Paths                      │  │ │
│  │  │  - Label Propagation  - SVD++                            │  │ │
│  │  └─────────────────────────────────────────────────────────┘  │ │
│  │                                                                 │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │                Graph Operators                           │  │ │
│  │  │  - mapVertices   - mapEdges   - subgraph                 │  │ │
│  │  │  - joinVertices  - aggregateMessages  - Pregel API       │  │ │
│  │  └─────────────────────────────────────────────────────────┘  │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 核心抽象

| 抽象 | 说明 | 底层实现 |
|------|------|----------|
| **Graph** | 图数据结构 | VertexRDD + EdgeRDD |
| **VertexRDD** | 顶点集合 | RDD[(VertexId, VD)] |
| **EdgeRDD** | 边集合 | RDD[Edge[ED]] |
| **EdgeTriplet** | 包含顶点和边的三元组 | (src, dst, edge) |
| **EdgePartition** | 边的分区 | 优化存储和访问 |

## 2. GraphX 数据模型

```
┌─────────────────────────────────────────────────────────────────────┐
│                   GraphX 数据模型                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Graph = VertexRDD + EdgeRDD + Routing Table                        │
│                                                                     │
│  ┌─────────────────┐          ┌─────────────────┐                  │
│  │   VertexRDD     │          │    EdgeRDD      │                  │
│  │  ┌───────────┐  │          │  ┌───────────┐  │                  │
│  │  │ (1, "A")  │  │          │  │ Edge(1,2) │  │                  │
│  │  │ (2, "B")  │  │          │  │ Edge(2,3) │  │                  │
│  │  │ (3, "C")  │  │          │  │ Edge(3,1) │  │                  │
│  │  │ (4, "D")  │  │          │  │ Edge(1,3) │  │                  │
│  │  └───────────┘  │          │  └───────────┘  │                  │
│  │  RDD[(Long, V)] │          │  RDD[Edge[E]]   │                  │
│  └─────────────────┘          └─────────────────┘                  │
│           │                            │                           │
│           └────────────┬───────────────┘                           │
│                        ▼                                           │
│  ┌─────────────────────────────────────────────────────────────┐  │
│  │                    Graph Instance                            │  │
│  │                                                              │  │
│  │         (1)"A"──────────────▶(2)"B"                         │  │
│  │           ▲ ╲                  │                             │  │
│  │           │  ╲                 │                             │  │
│  │           │   ╲                ▼                             │  │
│  │           │    ╲────────────(3)"C"                          │  │
│  │           │                  /                               │  │
│  │           │                 /                                │  │
│  │           └────────────────/                                 │  │
│  │         (4)"D" (孤立顶点)                                     │  │
│  │                                                              │  │
│  └─────────────────────────────────────────────────────────────┘  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. 快速开始

### 3.1 Scala API

```scala
import org.apache.spark.graphx._
import org.apache.spark.rdd.RDD

// 创建 SparkContext
val conf = new SparkConf().setAppName("GraphXExample").setMaster("local[*]")
val sc = new SparkContext(conf)

// 创建顶点 RDD
val users: RDD[(VertexId, (String, String))] = sc.parallelize(Array(
  (3L, ("rxin", "student")),
  (7L, ("jgonzal", "postdoc")),
  (5L, ("franklin", "prof")),
  (2L, ("istoica", "prof"))
))

// 创建边 RDD
val relationships: RDD[Edge[String]] = sc.parallelize(Array(
  Edge(3L, 7L, "collab"),
  Edge(5L, 3L, "advisor"),
  Edge(2L, 5L, "colleague"),
  Edge(5L, 7L, "pi")
))

// 定义默认顶点（处理缺失顶点）
val defaultUser = ("John Doe", "Missing")

// 构建图
val graph: Graph[(String, String), String] = Graph(users, relationships, defaultUser)

// 图操作示例
// 1. 统计顶点数
val numVertices = graph.numVertices

// 2. 统计边数
val numEdges = graph.numEdges

// 3. 度分布
val degrees: VertexRDD[Int] = graph.degrees
val inDegrees: VertexRDD[Int] = graph.inDegrees
val outDegrees: VertexRDD[Int] = graph.outDegrees

// 4. 筛选子图
val validGraph = graph.subgraph(vpred = (id, attr) => attr._2 != "Missing")

// 5. 转换顶点属性
val userNames = graph.mapVertices((id, attr) => attr._1)
```

### 3.2 Python API (GraphFrames)

```python
from pyspark.sql import SparkSession
from graphframes import GraphFrame

# 创建 SparkSession
spark = SparkSession.builder \
    .appName("GraphFrames") \
    .getOrCreate()

# 创建顶点 DataFrame
vertices = spark.createDataFrame([
    ("a", "Alice", 34),
    ("b", "Bob", 36),
    ("c", "Charlie", 30),
    ("d", "David", 29),
    ("e", "Esther", 32),
    ("f", "Fanny", 36)
], ["id", "name", "age"])

# 创建边 DataFrame
edges = spark.createDataFrame([
    ("a", "b", "friend"),
    ("b", "c", "follow"),
    ("c", "b", "follow"),
    ("f", "c", "follow"),
    ("e", "f", "follow"),
    ("e", "d", "friend"),
    ("d", "a", "friend")
], ["src", "dst", "relationship"])

# 创建图
graph = GraphFrame(vertices, edges)

# 基本操作
print("顶点数:", graph.vertices.count())
print("边数:", graph.edges.count())

# 入度/出度
graph.inDegrees.show()
graph.outDegrees.show()

# PageRank
results = graph.pageRank(resetProbability=0.15, maxIter=10)
results.vertices.select("id", "pagerank").show()
```

## 4. 核心操作

### 4.1 属性操作

```scala
// mapVertices - 转换顶点属性
val graph2 = graph.mapVertices((id, attr) => (attr._1.toUpperCase, attr._2))

// mapEdges - 转换边属性
val graph3 = graph.mapEdges(e => e.attr.toUpperCase)

// mapTriplets - 转换三元组
val graph4 = graph.mapTriplets(triplet => 
  triplet.srcAttr._1 + " - " + triplet.attr + " -> " + triplet.dstAttr._1
)
```

### 4.2 结构操作

```scala
// reverse - 反转边方向
val reversedGraph = graph.reverse

// subgraph - 子图
val validGraph = graph.subgraph(
  epred = e => e.attr != "bad",
  vpred = (id, attr) => attr._2 != "Missing"
)

// mask - 基于另一个图过滤
val maskedGraph = graph.mask(otherGraph)

// groupEdges - 合并重复边
val groupedGraph = graph.groupEdges((e1, e2) => e1 + e2)
```

### 4.3 Join 操作

```scala
// joinVertices - 与 RDD 连接
val newGraph = graph.joinVertices(extraInfoRDD) {
  case (id, (name, pos), extra) => (name, pos + extra)
}

// outerJoinVertices - 外连接
val outDegrees: VertexRDD[Int] = graph.outDegrees
val degreeGraph = graph.outerJoinVertices(outDegrees) {
  case (id, oldAttr, outDegOpt) =>
    val outDegree = outDegOpt.getOrElse(0)
    (oldAttr._1, oldAttr._2, outDegree)
}
```

## 5. Pregel API

GraphX 实现了 Pregel 模型用于迭代图计算。

```
┌─────────────────────────────────────────────────────────────────────┐
│                   GraphX Pregel API                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Pregel 执行流程：                                                   │
│                                                                     │
│  Init ──▶ Message Passing ──▶ Vertex Program ──▶ Check Convergence │
│             │                      │                      │         │
│             │                      │                      │         │
│             ▼                      ▼                      ▼         │
│  ┌─────────────────┐  ┌──────────────────┐  ┌──────────────────┐   │
│  │ 发送消息给邻居   │  │ 接收消息并更新   │  │ 所有顶点投票     │   │
│  │ sendMsgToSrc   │  │ 顶点属性         │  │ 停止?            │   │
│  │ sendMsgToDst   │  │ mergeMsg         │  │                  │   │
│  └─────────────────┘  └──────────────────┘  └──────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 5.1 单源最短路径 (SSSP)

```scala
import org.apache.spark.graphx._
import org.apache.spark.graphx.util.GraphGenerators

// 创建示例图
val graph: Graph[Long, Double] = 
  GraphGenerators.logNormalGraph(sc, numVertices = 100).mapEdges(e => e.attr.toDouble)

val sourceId: VertexId = 42 // 源顶点

// 初始化图：源顶点距离为0，其他为无穷大
val initialGraph = graph.mapVertices((id, _) => 
  if (id == sourceId) 0.0 else Double.PositiveInfinity
)

// Pregel 计算
val sssp = initialGraph.pregel(Double.PositiveInfinity)(
  // 顶点程序
  (id, dist, newDist) => math.min(dist, newDist),
  
  // 发送消息
  triplet => {
    if (triplet.srcAttr + triplet.attr < triplet.dstAttr) {
      Iterator((triplet.dstId, triplet.srcAttr + triplet.attr))
    } else {
      Iterator.empty
    }
  },
  
  // 合并消息
  (a, b) => math.min(a, b)
)

// 输出结果
println(sssp.vertices.collect().mkString("\n"))
```

## 6. 内置算法

### 6.1 PageRank

```scala
// 静态 PageRank
val ranks = graph.pageRank(0.0001).vertices

// 动态 PageRank（个性化）
val personalizedRanks = graph.personalizedPageRank(1L, 0.0001).vertices
```

### 6.2 连通分量

```scala
// 连通分量
val cc = graph.connectedComponents().vertices

// 强连通分量
val scc = graph.stronglyConnectedComponents(10).vertices
```

### 6.3 三角形计数

```scala
// 三角形计数
val triCounts = graph.triangleCount().vertices
```

### 6.4 标签传播 (LPA)

```scala
// 社区检测
val communities = graph.labelPropagation(maxSteps = 5)
```

## 7. 性能优化

### 7.1 分区策略

```scala
// 边分区策略
import org.apache.spark.graphx.PartitionStrategy._

// 随机分区
val graph1 = graph.partitionBy(RandomVertexCut)

// 边切割分区（源顶点 ID 哈希）
val graph2 = graph.partitionBy(EdgePartition1D)

// 2D 分区
val graph3 = graph.partitionBy(CanonicalRandomVertexCut)

// 定向边切割
val graph4 = graph.partitionBy(EdgePartition2D)
```

### 7.2 缓存策略

```scala
// 缓存图
graph.cache()
graph.persist(StorageLevel.MEMORY_AND_DISK)

// 只缓存顶点或边
graph.vertices.cache()
graph.edges.cache()

// 解持久化
graph.unpersist()
```

## 8. 与其他框架对比

| 特性 | GraphX | Giraph | GraphLab | Neo4j |
|------|--------|--------|----------|-------|
| **底层** | Spark | Hadoop | 原生 | 原生 |
| **执行模型** | BSP | BSP | GAS | 原生图存储 |
| **容错** | RDD 血缘 | Checkpoint | 快照 | 事务日志 |
| **适用规模** | 大规模 | 超大规模 | 大规模 | 中小规模 |
| **图查询** | 有限 | 有限 | 有限 | 强大 |
| **适用场景** | 分析计算 | 批处理计算 | 迭代计算 | 在线查询 |
| **学习曲线** | 中等 | 陡峭 | 中等 | 平缓 |

## 9. 总结

GraphX 的核心优势：

- **与 Spark 集成**：无缝使用 Spark 生态
- **灵活性**：同时支持图计算和批处理
- **容错性**：基于 RDD 的自动容错
- **表达力**：丰富的图操作和算法库

最佳实践：
1. 选择合适的分区策略优化性能
2. 合理使用缓存减少重复计算
3. 使用 Pregel API 实现自定义迭代算法
4. 对于交互式查询，考虑使用 GraphFrames
