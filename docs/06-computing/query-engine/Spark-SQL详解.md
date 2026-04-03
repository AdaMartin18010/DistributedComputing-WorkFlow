# Spark SQL 详解

## 1. 架构概述

Spark SQL 是 Apache Spark 的结构化数据处理模块，提供了 SQL 查询接口和 DataFrame/Dataset API。它将 SQL 查询优化与 Spark 的分布式计算能力相结合，实现了高性能的数据分析。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Spark SQL 架构                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    SQL / DataFrame API                         │ │
│  │  spark.sql("SELECT ...")  /  df.select(...)                   │ │
│  └───────────────────────────────┬───────────────────────────────┘ │
│                                  │                                  │
│                                  ▼                                  │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Catalyst Optimizer                          │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │   Parser    │─▶│  Analyzer   │─▶│  Logical Optimizer  │   │ │
│  │  │ (SQL解析)    │  │ (语义分析)   │  │ (逻辑优化)          │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  │                                              │                 │ │
│  │                                              ▼                 │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │                  Physical Planner                        │  │ │
│  │  │  - Cost-based Optimization (CBO)                        │  │ │
│  │  │  - Join reordering                                      │  │ │
│  │  │  - Predicate pushdown                                   │  │ │
│  │  └─────────────────────────────────────────────────────────┘  │ │
│  └───────────────────────────────┬───────────────────────────────┘ │
│                                  │                                  │
│                                  ▼                                  │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Spark Core Execution                        │ │
│  │                    (RDD / WholeStageCodegen)                   │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 Catalyst 优化器

```
┌─────────────────────────────────────────────────────────────────────┐
│                 Catalyst 优化流程                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  SQL Query                                                          │
│  SELECT name, age FROM people WHERE age > 20                        │
│       │                                                             │
│       ▼                                                             │
│  ┌─────────────────┐                                               │
│  │  Unresolved     │  未解析的逻辑计划                              │
│  │  Logical Plan   │  'Project ['name, 'age]                      │
│  │                 │  'Filter ('age > 20)                         │
│  │                 │  'UnresolvedRelation 'people                 │
│  └────────┬────────┘                                               │
│           │                                                         │
│           ▼  Catalog 解析                                          │
│  ┌─────────────────┐                                               │
│  │  Resolved       │  解析后的逻辑计划                              │
│  │  Logical Plan   │  Project [name#1, age#2]                     │
│  │                 │  Filter (age#2 > 20)                         │
│  │                 │  Relation [name#1,age#2] parquet             │
│  └────────┬────────┘                                               │
│           │                                                         │
│           ▼ 规则优化 (RBO)                                          │
│  ┌─────────────────┐                                               │
│  │  Optimized      │  优化后的逻辑计划                              │
│  │  Logical Plan   │  Project [name#1, age#2]                     │
│  │                 │  Filter (age#2 > 20)                         │
│  │                 │  Relation [name#1,age#2] parquet             │
│  │                 │  (谓词下推完成)                               │
│  └────────┬────────┘                                               │
│           │                                                         │
│           ▼ 物理计划生成                                            │
│  ┌─────────────────┐                                               │
│  │  Physical Plan  │  物理执行计划                                  │
│  │                 │  ProjectExec [name#1, age#2]                 │
│  │                 │  FilterExec (age#2 > 20)                     │
│  │                 │  FileSourceScanExec parquet [name,age]       │
│  └─────────────────┘                                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. DataFrame API

### 2.1 创建 DataFrame

```python
from pyspark.sql import SparkSession
from pyspark.sql.types import *

spark = SparkSession.builder \
    .appName("SparkSQL") \
    .getOrCreate()

# 从 RDD 创建
rdd = spark.sparkContext.parallelize([
    ("Alice", 25, "Engineer"),
    ("Bob", 30, "Manager"),
    ("Charlie", 35, "Director")
])
df1 = spark.createDataFrame(rdd, ["name", "age", "job"])

# 从列表创建
data = [
    {"name": "Alice", "age": 25, "salary": 5000},
    {"name": "Bob", "age": 30, "salary": 6000}
]
df2 = spark.createDataFrame(data)

# 从文件读取
df3 = spark.read.json("path/to/file.json")
df4 = spark.read.parquet("path/to/file.parquet")
df5 = spark.read.csv("path/to/file.csv", header=True, inferSchema=True)

# 从 JDBC 读取
df6 = spark.read \
    .format("jdbc") \
    .option("url", "jdbc:mysql://localhost:3306/db") \
    .option("dbtable", "employees") \
    .option("user", "user") \
    .option("password", "password") \
    .load()
```

### 2.2 基本操作

```python
from pyspark.sql.functions import *

# 选择列
df.select("name", "age")
df.select(col("name").alias("employee_name"))
df.selectExpr("name as employee_name", "age + 1 as next_year_age")

# 过滤
df.filter(df.age > 25)
df.filter((df.age > 25) & (df.salary > 5000))
df.where("age > 25 and salary > 5000")

# 聚合
df.groupBy("department").agg(
    count("*").alias("count"),
    avg("salary").alias("avg_salary"),
    max("salary").alias("max_salary"),
    sum("salary").alias("total_salary")
)

# 排序
df.orderBy(df.age.desc())
df.sort(asc("department"), desc("salary"))

# Join
inner_join = df1.join(df2, "id")
left_join = df1.join(df2, df1.id == df2.id, "left")

# Window 函数
from pyspark.sql.window import Window

window_spec = Window.partitionBy("department").orderBy(desc("salary"))
df.withColumn("rank", rank().over(window_spec)) \
  .withColumn("dense_rank", dense_rank().over(window_spec)) \
  .withColumn("row_number", row_number().over(window_spec))
```

## 3. SQL 查询

```python
# 注册临时视图
df.createOrReplaceTempView("employees")

# 执行 SQL
result = spark.sql("""
    SELECT 
        department,
        COUNT(*) as emp_count,
        AVG(salary) as avg_salary,
        MAX(salary) as max_salary
    FROM employees
    WHERE age > 25
    GROUP BY department
    HAVING COUNT(*) > 5
    ORDER BY avg_salary DESC
""")

# 复杂查询
spark.sql("""
    WITH dept_stats AS (
        SELECT 
            department,
            AVG(salary) as avg_salary
        FROM employees
        GROUP BY department
    )
    SELECT 
        e.name,
        e.department,
        e.salary,
        d.avg_salary,
        e.salary - d.avg_salary as diff
    FROM employees e
    JOIN dept_stats d ON e.department = d.department
    WHERE e.salary > d.avg_salary
""").show()
```

## 4. 性能优化

### 4.1 广播 Join

```python
# 自动广播小表
spark.conf.set("spark.sql.autoBroadcastJoinThreshold", "100MB")

# 强制广播
from pyspark.sql.functions import broadcast

result = large_df.join(broadcast(small_df), "join_key")
```

### 4.2 分区优化

```python
# 设置 Shuffle 分区数
spark.conf.set("spark.sql.shuffle.partitions", "200")

# 自适应查询执行 (AQE)
spark.conf.set("spark.sql.adaptive.enabled", "true")
spark.conf.set("spark.sql.adaptive.coalescePartitions.enabled", "true")
spark.conf.set("spark.sql.adaptive.skewJoin.enabled", "true")

# 数据倾斜处理
spark.conf.set("spark.sql.adaptive.skewJoin.skewedPartitionFactor", "5")
spark.conf.set("spark.sql.adaptive.skewJoin.skewedPartitionThresholdInBytes", "256MB")
```

### 4.3 谓词下推

```python
# 自动谓词下推（对于 Parquet/ORC）
df = spark.read.parquet("s3://bucket/large_table")
filtered = df.filter(col("date") >= "2024-01-01")  # 自动下推

# 手动提示
spark.sql("""
    SELECT /*+ REPARTITION(100) */ *
    FROM large_table
    WHERE date >= '2024-01-01'
""")
```

### 4.4 缓存

```python
# 缓存 DataFrame
df.cache()
df.persist(StorageLevel.MEMORY_AND_DISK)

# 取消缓存
df.unpersist()

# 最佳实践：缓存中间结果
aggregated = df.groupBy("key").agg(sum("value"))
aggregated.cache()

result1 = aggregated.filter(col("sum(value)") > 100).collect()
result2 = aggregated.orderBy(desc("sum(value)")).take(10)

aggregated.unpersist()
```

## 5. 高级特性

### 5.1 自定义函数 (UDF)

```python
from pyspark.sql.functions import udf
from pyspark.sql.types import IntegerType

# Python UDF
@udf(returnType=IntegerType())
def calculate_bonus(salary, performance):
    if performance == "A":
        return int(salary * 0.2)
    elif performance == "B":
        return int(salary * 0.1)
    else:
        return 0

df.withColumn("bonus", calculate_bonus(col("salary"), col("performance")))

# Pandas UDF（向量化，性能更好）
from pyspark.sql.functions import pandas_udf
import pandas as pd

@pandas_udf(IntegerType())
def vectorized_bonus(salary: pd.Series, performance: pd.Series) -> pd.Series:
    return salary * np.where(performance == "A", 0.2,
                    np.where(performance == "B", 0.1, 0))
```

### 5.2 动态分区写入

```python
# 动态分区写入
df.write \
    .partitionBy("year", "month", "day") \
    .mode("overwrite") \
    .parquet("output_path")

# 配置
spark.conf.set("spark.sql.sources.partitionOverwriteMode", "dynamic")
```

### 5.3 桶表

```python
# 创建桶表
spark.sql("""
    CREATE TABLE users_bucketed (
        id INT,
        name STRING,
        age INT
    )
    USING parquet
    CLUSTERED BY (id) INTO 8 BUCKETS
    STORED AS parquet
""")

# 写入桶表
df.write \
    .bucketBy(8, "id") \
    .sortBy("id") \
    .mode("overwrite") \
    .saveAsTable("users_bucketed")
```

## 6. 与 Hive 集成

```python
# 启用 Hive 支持
spark = SparkSession.builder \
    .appName("SparkHive") \
    .enableHiveSupport() \
    .getOrCreate()

# 使用 Hive 表
spark.sql("USE my_database")
hive_df = spark.table("hive_table")

# 创建 Hive 表
spark.sql("""
    CREATE TABLE IF NOT EXISTS new_table (
        id INT,
        name STRING
    )
    PARTITIONED BY (dt STRING)
    STORED AS ORC
""")

# 插入数据
spark.sql("""
    INSERT OVERWRITE TABLE new_table PARTITION (dt='2024-01-01')
    SELECT id, name FROM source_table
""")
```

## 7. 性能调优清单

| 配置项 | 说明 | 建议值 |
|--------|------|--------|
| spark.sql.shuffle.partitions | Shuffle 分区数 | 200-1000 |
| spark.sql.adaptive.enabled | 自适应查询执行 | true |
| spark.sql.autoBroadcastJoinThreshold | 广播阈值 | 100MB |
| spark.sql.files.maxPartitionBytes | 最大分区大小 | 128MB |
| spark.sql.files.openCostInBytes | 文件打开开销 | 4MB |
| spark.serializer | 序列化器 | KryoSerializer |

## 8. 总结

Spark SQL 的核心优势：

- **统一接口**：SQL 和 DataFrame API 无缝切换
- **自动优化**：Catalyst 优化器自动优化查询
- **高性能**：Code Generation 和 Whole-Stage 优化
- **生态丰富**：与 Hive、JDBC、Parquet 等深度集成

最佳实践：
1. 优先使用 DataFrame/Dataset API 而非 RDD
2. 合理使用广播 Join 避免 Shuffle
3. 启用 AQE 自动处理数据倾斜
4. 使用 Parquet/ORC 等列式存储格式
5. 缓存重复使用的中间结果
