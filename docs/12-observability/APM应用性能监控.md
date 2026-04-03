# APM 应用性能监控专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

APM（Application Performance Monitoring）是用于监控和管理应用程序性能的一套技术体系，通过追踪请求链路、采集性能指标和分析代码级别的耗时，帮助开发和运维团队快速定位和解决性能问题。本文档深度分析 SkyWalking、Pinpoint、CAT 和 Elastic APM 四大主流开源 APM 工具。

---

## 一、核心概念

### 1.1 定义与原理

APM 是一种软件监控实践，主要关注以下三个维度：

- **Tracing（链路追踪）**：追踪请求在分布式系统中的完整调用链路
- **Metrics（指标监控）**：采集应用的性能指标（响应时间、吞吐量、错误率等）
- **Logging（日志关联）**：将日志与 Trace/Span 关联，提供上下文信息

**核心工作原理**：

1. **探针注入**：通过 Java Agent、Sidecar 或 SDK 在应用中植入监控代码
2. **上下文传播**：通过 HTTP Header 等方式传递 Trace Context
3. **数据采集**：采集 Span 数据、性能指标和元数据
4. **数据处理**：收集器接收、清洗、聚合数据
5. **存储分析**：时序数据库存储，提供查询和可视化界面

### 1.2 关键特性

- **分布式追踪**：追踪跨服务、跨线程的完整调用链路
- **自动发现**：自动识别服务拓扑和依赖关系
- **代码级诊断**：定位到具体方法和代码行的性能问题
- **多维分析**：按服务、实例、端点、时间等多维度分析
- **告警通知**：基于 SLA/SLO 的智能告警

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 分布式系统故障定位 | ⭐⭐⭐⭐⭐ | 快速定位跨服务调用问题 |
| 性能瓶颈分析 | ⭐⭐⭐⭐⭐ | 代码级别耗时分析 |
| 服务依赖梳理 | ⭐⭐⭐⭐⭐ | 自动生成服务拓扑图 |
| SLA/SLO 监控 | ⭐⭐⭐⭐ | 基于响应时间、错误率的 SLA 监控 |
| 业务指标追踪 | ⭐⭐⭐ | 需配合业务埋点 |
| 基础设施监控 | ⭐⭐ | 非其强项，需配合 Prometheus |

---

## 二、技术细节

### 2.1 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          APM 通用架构                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌────────────────────────────────────────────────────────────────┐   │
│   │                        数据采集层                               │   │
│   │                                                                │   │
│   │   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │   │
│   │   │  Java Agent │  │  Sidecar    │  │     Language SDK    │   │   │
│   │   │  (字节码增强)│  │  (Envoy)    │  │   (Python/Go/Node)  │   │   │
│   │   └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘   │   │
│   │          │                │                    │              │   │
│   │          └────────────────┼────────────────────┘              │   │
│   │                           │                                   │   │
│   │                    ┌──────┴──────┐                           │   │
│   │                    │   Traces    │                           │   │
│   │                    │   Metrics   │                           │   │
│   │                    │   Metadata  │                           │   │
│   │                    └──────┬──────┘                           │   │
│   └───────────────────────────┼──────────────────────────────────┘   │
│                               │                                       │
│                               ▼                                       │
│   ┌────────────────────────────────────────────────────────────────┐   │
│   │                        数据处理层                               │   │
│   │                                                                │   │
│   │   ┌─────────────────┐    ┌─────────────────┐                  │   │
│   │   │    Collector    │    │   Aggregator    │                  │   │
│   │   │   (数据收集器)   │───▶│   (聚合分析)    │                  │   │
│   │   └─────────────────┘    └─────────────────┘                  │   │
│   │            │                                              │   │
│   │            ▼                                              │   │
│   │   ┌─────────────────┐                                    │   │
│   │   │  Queue (Kafka)  │    缓冲削峰填谷                      │   │
│   │   └─────────────────┘                                    │   │
│   └────────────────────────────────────────────────────────────┘   │
│                                                                     │
│                               │                                     │
│                               ▼                                     │
│   ┌────────────────────────────────────────────────────────────────┐ │
│   │                        数据存储层                               │ │
│   │                                                                │ │
│   │   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│   │   │   Trace     │  │   Metric    │  │      Metadata       │   │ │
│   │   │   Storage   │  │   Storage   │  │      Storage        │   │ │
│   │   │(ES/Cassandra│  │(TSDB/ES)    │  │  (MySQL/ES)         │   │ │
│   │   └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│   └────────────────────────────────────────────────────────────────┘ │
│                                                                       │
│                               │                                       │
│                               ▼                                       │
│   ┌────────────────────────────────────────────────────────────────┐   │
│   │                        可视化层                                 │   │
│   │                                                                │   │
│   │   ┌─────────────────────────────────────────────────────────┐ │   │
│   │   │                      Web UI                              │ │   │
│   │   │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │ │   │
│   │   │  │ Topology│ │  Trace  │ │ Dashboard│ │  Alert  │        │ │   │
│   │   │  │  拓扑图  │ │  链路   │ │  仪表板  │ │  告警   │        │ │   │
│   │   │  └─────────┘ └─────────┘ └─────────┘ └─────────┘        │ │   │
│   │   └─────────────────────────────────────────────────────────┘ │   │
│   └────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 OpenTelemetry 标准

**W3C Trace Context**：

```
# HTTP Header 格式
traceparent: 00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01

# 字段解析
00                                    - 版本
0af7651916cd43dd8448eb211c80319c      - Trace ID (16字节)
b7ad6b7169203331                      - Parent Span ID (8字节)
01                                    - 标志位 (采样标志)

tracestate: rojo=00f067aa0ba902b7,congo=t61rcWkgMzE
```

**OpenTelemetry 数据模型**：

```protobuf
// Span 结构
message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  bytes parent_span_id = 3;
  string name = 4;
  SpanKind kind = 5;
  fixed64 start_time_unix_nano = 6;
  fixed64 end_time_unix_nano = 7;
  repeated KeyValue attributes = 8;
  repeated Event events = 9;
  repeated Link links = 10;
  Status status = 11;
}

// SpanKind 类型
enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;    // 内部方法
  SPAN_KIND_SERVER = 2;      // 服务端入口
  SPAN_KIND_CLIENT = 3;      // 客户端调用
  SPAN_KIND_PRODUCER = 4;    // 消息生产者
  SPAN_KIND_CONSUMER = 5;    // 消息消费者
}
```

### 2.3 字节码增强原理

**Java Agent 机制**：

```java
// JVM 启动参数
-javaagent:/path/to/apm-agent.jar

// Agent 入口
public class ApmAgent {
    public static void premain(String args, Instrumentation inst) {
        // 注册 ClassFileTransformer
        inst.addTransformer(new ApmClassTransformer());
    }
}

// 字节码转换
public class ApmClassTransformer implements ClassFileTransformer {
    @Override
    public byte[] transform(ClassLoader loader, String className,
                          Class<?> classBeingRedefined,
                          ProtectionDomain protectionDomain,
                          byte[] classfileBuffer) {
        // 使用 ASM/Javassist/ByteBuddy 修改字节码
        ClassReader reader = new ClassReader(classfileBuffer);
        ClassWriter writer = new ClassWriter(reader, ClassWriter.COMPUTE_FRAMES);
        ClassVisitor visitor = new TracingClassVisitor(writer);
        reader.accept(visitor, ClassReader.EXPAND_FRAMES);
        return writer.toByteArray();
    }
}
```

**方法增强示例**：

```java
// 原始方法
public void processOrder(Order order) {
    validate(order);
    save(order);
    notify(order);
}

// 增强后（伪代码）
public void processOrder(Order order) {
    Span span = Tracer.startSpan("processOrder");
    try {
        span.setTag("order.id", order.getId());

        Span child1 = Tracer.startSpan("validate", span);
        validate(order);
        child1.finish();

        Span child2 = Tracer.startSpan("save", span);
        save(order);
        child2.finish();

        Span child3 = Tracer.startSpan("notify", span);
        notify(order);
        child3.finish();

        span.setStatus(Status.OK);
    } catch (Exception e) {
        span.setStatus(Status.ERROR);
        span.log(e);
        throw e;
    } finally {
        span.finish();
    }
}
```

---

## 三、主流 APM 系统详解

### 3.1 Apache SkyWalking

**项目背景**：

- 创建者：吴晟（Apache 基金会首位中国本土当选 VP）
- 发源地：华为开源，2017 年进入 Apache 孵化器
- 定位：云原生、多语言支持的 APM 系统

**架构特点**：

```
┌─────────────────────────────────────────────────────────────┐
│                      SkyWalking 架构                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                    OAP Server                        │  │
│   │  (Observability Analysis Platform)                   │  │
│   │                                                      │  │
│   │   ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │  │
│   │   │  Receiver   │  │   Core      │  │   Query     │ │  │
│   │   │  (gRPC/HTTP)│  │  Processor  │  │   Module    │ │  │
│   │   └──────┬──────┘  └──────┬──────┘  └──────┬──────┘ │  │
│   │          │                │                │        │  │
│   │          └────────────────┼────────────────┘        │  │
│   │                           │                         │  │
│   │                    ┌──────┴──────┐                 │  │
│   │                    │   Storage   │                 │  │
│   │                    │(ES/H2/MySQL/│                 │  │
│   │                    │TiDB/BanyanDB)│                 │  │
│   │                    └─────────────┘                 │  │
│   └─────────────────────────────────────────────────────┘  │
│                                                             │
│   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐│
│   │ Java Agent  │  │  SWCK       │  │   Satellite         ││
│   │(自动探针)    │  │(K8s Operator)│  │   (Sidecar)         ││
│   └─────────────┘  └─────────────┘  └─────────────────────┘│
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**核心特性**：

- **多语言支持**：Java、.NET、Node.js、Go、Python、PHP、Lua 等
- **多种探针模式**：
  - Java Agent：字节码增强，无侵入
  - Mesh：Envoy/istio 接入
  - Sidecar：Satellite 代理
  - SDK：多语言原生 SDK
- **内置存储**：支持 Elasticsearch、H2、MySQL、TiDB、BanyanDB
- **服务网格原生**：支持 Envoy ALS、Istio telemetry

**Java Agent 使用**：

```bash
# 下载 Agent
wget https://archive.apache.org/dist/skywalking/9.6.0/apache-skywalking-apm-9.6.0.tar.gz

# JVM 参数配置
-javaagent:/path/to/skywalking-agent.jar \
-DSW_AGENT_NAME=order-service \
-DSW_AGENT_COLLECTOR_BACKEND_SERVICES=127.0.0.1:11800
```

**docker-compose 部署**：

```yaml
version: '3.8'
services:
  oap:
    image: apache/skywalking-oap-server:9.6.0
    environment:
      SW_STORAGE: elasticsearch
      SW_STORAGE_ES_CLUSTER_NODES: elasticsearch:9200
    ports:
      - "11800:11800"  # gRPC
      - "12800:12800"  # HTTP

  ui:
    image: apache/skywalking-ui:9.6.0
    environment:
      SW_OAP_ADDRESS: http://oap:12800
    ports:
      - "8080:8080"

  elasticsearch:
    image: elasticsearch:8.11.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
    volumes:
      - es-data:/usr/share/elasticsearch/data

volumes:
  es-data:
```

---

### 3.2 Pinpoint

**项目背景**：

- 创建者：韩国 Naver 公司（Line 母公司）
- 开发时间：2012 年开源
- 定位：大规模分布式系统的 APM 工具

**架构特点**：

```
┌─────────────────────────────────────────────────────────────┐
│                       Pinpoint 架构                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                   Collector                          │  │
│   │            (UDP/TCP 数据接收)                         │  │
│   └──────────────────────────┬──────────────────────────┘  │
│                              │                             │
│                              ▼                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                   HBase Storage                      │  │
│   │                                                      │  │
│   │   Span Table      ┌─ AgentStat Table                │  │
│   │   Trace Table     ┌─ ApplicationStat Table          │  │
│   │   Annotation Table┌─ ...                            │  │
│   │                                                      │  │
│   └─────────────────────────────────────────────────────┘  │
│                              │                             │
│                              ▼                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                      Web UI                          │  │
│   └─────────────────────────────────────────────────────┘  │
│                                                             │
│   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐│
│   │ Java Agent  │  │  Tomcat     │  │   Jetty/Undertow    ││
│   │(字节码增强)   │  │  Plugin     │  │   Plugin            ││
│   └─────────────┘  └─────────────┘  └─────────────────────┘│
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**核心特性**：

- **无侵入部署**：纯 Java Agent，无需修改代码
- **字节码增强深度**：支持追踪 HTTP 客户端、数据库、缓存、MQ 等
- **HBase 存储**：专为大规模数据设计，支持水平扩展
- **Server Map**：自动生成服务间调用关系图
- **Call Stack**：详细的调用栈展示

**技术亮点**：

```java
// Pinpoint 使用 ASM 进行字节码增强
// 支持 Interceptor 模式

//  around 增强
@TargetMethod(name="execute", paramTypes={"java.lang.Runnable"})
public class ThreadPoolInterceptor implements AroundInterceptor {
    @Override
    public void before(Object target, Object[] args) {
        // 提取 Trace Context
        TraceContext context = TraceContext.getCurrentContext();
        // 包装 Runnable 传递 Context
        args[0] = new TraceRunnableWrapper((Runnable)args[0], context);
    }

    @Override
    public void after(Object target, Object[] args, Object result, Throwable throwable) {
        // 记录执行结果
    }
}
```

---

### 3.3 CAT (Central Application Tracking)

**项目背景**：

- 创建者：大众点评（现美团）
- 开发时间：2011 年开源
- 定位：企业级高可用 APM 系统

**架构特点**：

```
┌─────────────────────────────────────────────────────────────┐
│                        CAT 架构                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                    CAT Server                        │  │
│   │                                                      │  │
│   │   ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │  │
│   │   │   Console   │  │   Router    │  │   Analyzer  │ │  │
│   │   │   (控制台)   │  │  (路由分发) │  │   (分析器)  │ │  │
│   │   └──────┬──────┘  └──────┬──────┘  └──────┬──────┘ │  │
│   │          │                │                │        │  │
│   │          └────────────────┼────────────────┘        │  │
│   │                           ▼                         │  │
│   │                    ┌─────────────┐                 │  │
│   │                    │  HDFS/MySQL │                 │  │
│   │                    │  (存储层)   │                 │  │
│   │                    └─────────────┘                 │  │
│   └─────────────────────────────────────────────────────┘  │
│                                                             │
│   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐│
│   │  CAT Client │  │  Message    │  │   埋点 API          ││
│   │ (Java/CPP/  │  │  Tree       │  │   Transaction       ││
│   │  Python/Node│  │  消息树      │  │   Event/Heartbeat   ││
│   └─────────────┘  └─────────────┘  └─────────────────────┘│
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**核心特性**：

- **消息树（Message Tree）**：将 Transaction、Event、Heartbeat 组织成树形结构
- **实时处理**：秒级延迟的监控数据展示
- **报表丰富**：
  - Transaction 报表：接口调用统计
  - Event 报表：事件发生统计
  - Problem 报表：异常/超时问题汇总
  - Heartbeat 报表：JVM/系统指标
- **告警机制**：内置完善的告警规则

**客户端埋点示例**：

```java
// 创建 Transaction
Transaction t = Cat.newTransaction("URL", "/api/order/create");
try {
    // 记录业务指标
    Cat.logMetricForCount("order.created");
    Cat.logMetricForDuration("order.process", duration);

    // 记录 Event
    Cat.logEvent("Cache.Get", "order:12345", Event.SUCCESS, "hit");

    // 嵌套子 Transaction
    Transaction dbT = Cat.newTransaction("SQL", "SELECT");
    try {
        // 执行 SQL
        dbT.setStatus(Transaction.SUCCESS);
    } catch (Exception e) {
        dbT.setStatus(e);
        Cat.logError(e);
    } finally {
        dbT.complete();
    }

    t.setStatus(Transaction.SUCCESS);
} catch (Exception e) {
    t.setStatus(e);
    Cat.logError(e);
} finally {
    t.complete();
}
```

---

### 3.4 Elastic APM

**项目背景**：

- 创建者：Elastic 公司
- 发布时间：2018 年
- 定位：Elastic Stack 生态的 APM 解决方案

**架构特点**：

```
┌─────────────────────────────────────────────────────────────┐
│                      Elastic APM 架构                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                   APM Server                         │  │
│   │         (接收 agent 数据，验证转换)                   │  │
│   └──────────────────────────┬──────────────────────────┘  │
│                              │                             │
│                              ▼                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                  Elasticsearch                       │  │
│   │                                                      │  │
│   │   apm-*-transaction   ┌─ Metrics                    │  │
│   │   apm-*-span          ┌─ Logs                        │  │
│   │   apm-*-error         ┌─ Profiling                   │  │
│   │   apm-*-metricset     ┌─ RUM Real User Monitoring    │  │
│   │                                                      │  │
│   └──────────────────────────┬──────────────────────────┘  │
│                              │                             │
│                              ▼                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                     Kibana                           │  │
│   │               (APM UI / Lens)                        │  │
│   │                                                      │  │
│   │   - Service Map       - Trace Viewer                 │  │
│   │   - Metrics Explorer  - Error Group                  │  │
│   └─────────────────────────────────────────────────────┘  │
│                                                             │
│   ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐│
│   │ APM Agent   │  │  RUM Agent  │  │  AWS Lambda         ││
│   │(Java/Go/   │  │  (浏览器)   │  │  Extension          ││
│   │ Python/Node│  │  真实用户监控│  │                     ││
│   └─────────────┘  └─────────────┘  └─────────────────────┘│
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**核心特性**：

- **Elastic Stack 原生集成**：与 ES、Kibana 无缝整合
- **多语言 Agent**：Java、Go、Python、Node.js、.NET、PHP、Ruby、RUM
- **RUM 真实用户监控**：浏览器端性能监控
- **持续剖析（Profiling）**：代码级 CPU/Memory 分析
- **机器学习集成**：异常检测、日志模式识别

**部署配置**：

```yaml
# docker-compose.yml
version: '3.8'
services:
  apm-server:
    image: docker.elastic.co/apm/apm-server:8.11.0
    volumes:
      - ./apm-server.yml:/usr/share/apm-server/apm-server.yml
    ports:
      - "8200:8200"
    environment:
      - output.elasticsearch.hosts=["elasticsearch:9200"]

  elasticsearch:
    image: docker.elastic.co/elasticsearch/elasticsearch:8.11.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false

  kibana:
    image: docker.elastic.co/kibana/kibana:8.11.0
    environment:
      - ELASTICSEARCH_HOSTS=http://elasticsearch:9200
    ports:
      - "5601:5601"
```

**Java Agent 使用**：

```bash
java -javaagent:/path/to/elastic-apm-agent.jar \
  -Delastic.apm.service_name=order-service \
  -Delastic.apm.server_urls=http://apm-server:8200 \
  -Delastic.apm.application_packages=com.example \
  -jar application.jar
```

---

## 四、系统对比

### 4.1 四大 APM 对比矩阵

| 维度 | Apache SkyWalking | Pinpoint | CAT | Elastic APM |
|------|-------------------|----------|-----|-------------|
| **开发背景** | Apache 基金会 | Naver (韩国) | 美团 | Elastic |
| **社区活跃度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **多语言支持** | Java/Go/Node/Python/PHP/.NET/... | Java (最佳) | Java/CPP/Python/Node | Java/Go/Python/Node/.NET/... |
| **探针方式** | Agent/Sidecar/SDK | Java Agent | 代码埋点 | Agent/RUM |
| **侵入性** | 低（字节码） | 低（字节码） | 中（代码埋点） | 低（字节码） |
| **存储方案** | ES/H2/MySQL/TiDB/BanyanDB | HBase | MySQL/HDFS | Elasticsearch |
| **UI 体验** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **拓扑图** | ✅ 自动 | ✅ 自动 | ❌ | ✅ 自动 |
| **Trace 详情** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **告警能力** | ⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **云原生适配** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **与日志集成** | 中等 | 弱 | 中等 | ⭐⭐⭐⭐⭐（ES原生）|
| **RUM 监控** | ❌ | ❌ | ❌ | ✅ |
| **学习曲线** | 中等 | 中等 | 陡峭 | 较低 |

### 4.2 选型决策树

```
APM 系统选型
├── 已有 Elastic Stack 生态？
│   ├── 是 → Elastic APM（集成度高，UI优秀）
│   └── 否 → 主要使用 Java？
│       ├── 是 → 需要深度代码分析？
│       │   ├── 是 → Pinpoint（调用栈最详细）
│       │   └── 否 → 云原生/多语言环境？
│       │       ├── 是 → SkyWalking（多语言、K8s友好）
│       │       └── 否 → 企业级告警要求高？
│       │           ├── 是 → CAT（告警完善）
│       │           └── 否 → SkyWalking（生态全面）
│       └── 否 → 多语言混合环境？
│           ├── 是 → SkyWalking（多语言支持最好）
│           └── 否 → Elastic APM（通用性强）
└── 预算敏感？
    ├── 是 → SkyWalking（Apache 开源，无商业限制）
    └── 否 → 综合考虑生态和运维成本
```

### 4.3 性能基准参考

| 指标 | SkyWalking | Pinpoint | CAT | Elastic APM |
|------|------------|----------|-----|-------------|
| Agent 性能损耗 | 3-5% | 5-10% | 2-3% | 5-8% |
| 单节点吞吐 | 100K spans/s | 50K spans/s | 200K msg/s | 80K spans/s |
| 存储压缩比 | 较好 | 优秀(HBase) | 一般 | 一般(ES膨胀) |
| 延迟（Trace查看）| < 1s | < 2s | < 1s | < 1s |
| Agent 内存占用 | 50-100MB | 100-200MB | 30-50MB | 50-100MB |

---

## 五、实践指南

### 5.1 部署配置

**SkyWalking 生产部署建议**：

```yaml
# docker-compose.prod.yml
version: '3.8'
services:
  oap1:
    image: apache/skywalking-oap-server:9.6.0
    environment:
      SW_CLUSTER: nacos
      SW_SERVICE_NAME: oap-server
      SW_STORAGE: elasticsearch
      SW_STORAGE_ES_CLUSTER_NODES: es1:9200,es2:9200,es3:9200
      JAVA_OPTS: "-Xms4g -Xmx4g"
    deploy:
      replicas: 2

  oap2:
    image: apache/skywalking-oap-server:9.6.0
    environment:
      SW_CLUSTER: nacos
      SW_SERVICE_NAME: oap-server
      SW_STORAGE: elasticsearch
      SW_STORAGE_ES_CLUSTER_NODES: es1:9200,es2:9200,es3:9200
      JAVA_OPTS: "-Xms4g -Xmx4g"
    deploy:
      replicas: 2

  ui:
    image: apache/skywalking-ui:9.6.0
    environment:
      SW_OAP_ADDRESS: http://oap1:12800,http://oap2:12800
    ports:
      - "8080:8080"
```

### 5.2 最佳实践

1. **采样策略配置**：

   ```yaml
   # SkyWalking 采样配置
   agent.sample_n_per_3_secs: 5  # 每3秒采样5条
   agent.trace.ignore_path: /health,/actuator/**  # 忽略健康检查

   # 或百分比采样
   agent.sample_rate: 0.1  # 10% 采样
   ```

2. **性能调优**：
   - 调整缓存大小减少上报频率
   - 使用异步队列缓冲 Span 数据
   - 生产环境开启采样，避免全量采集

3. **与日志集成**：

   ```java
   // 在日志中输出 Trace ID
   MDC.put("traceId", TraceContext.traceId());
   log.info("Processing order {}", orderId);

   // Logstash 解析 Trace ID
   filter {
     grok {
       match => { "message" => "%{TIMESTAMP_ISO8601:timestamp} \[%{DATA:traceId}\]" }
     }
   }
   ```

4. **告警规则示例**（SkyWalking）：

   ```yaml
   rules:
     - name: service_resp_time_rule
       metrics-name: service_resp_time
       threshold: 1000
       op: ">"
       period: 5
       count: 3
       message: "服务 {name} 响应时间超过 1000ms"
   ```

### 5.3 常见问题

**Q1: APM Agent 导致应用启动变慢？**
A:

- 增加类加载缓存，减少启动时类扫描
- 调整 agent 的 instrumentation 范围
- 使用预编译的类缓存

**Q2: 采样导致问题无法复现？**
A:

- 使用条件采样：仅对错误请求全量采集
- 支持动态调整采样率
- 保留特定用户/请求的 Trace

**Q3: 存储成本过高怎么办？**
A:

- 设置 TTL（数据保留时间）
- 调整采样率
- 分层存储：热数据 SSD，冷数据对象存储
- 使用专门针对 APM 优化的存储（如 BanyanDB）

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [分布式追踪](../13-tracing/分布式追踪.md) - APM 的核心技术基础
- [Java Agent 开发](../09-jvm/Java-Agent开发.md) - 字节码增强技术
- [服务网格](../07-microservices/服务网格Istio.md) - 无侵入采集方案

### 6.2 下游应用

- [性能优化](../11-devops/性能优化.md) - 基于 APM 数据进行优化
- [故障排查](../11-devops/故障排查.md) - 利用 Trace 快速定位问题
- [容量规划](../11-devops/容量规划.md) - 基于性能指标进行规划

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| OpenTelemetry | 行业标准 | 统一的可观测性标准，多 APM 正在支持 |
| Jaeger | 专用链路追踪 | 专注 Tracing，无 Metrics 和 Profiling |
| Prometheus | 指标监控 | 可与 APM 互补，形成完整可观测性方案 |
| SRE | 方法论 | 基于 APM 实现 SLO/SLA 监控 |

---

## 七、参考资源

### 7.1 官方文档

1. [Apache SkyWalking 官方文档](https://skywalking.apache.org/docs/)
2. [Pinpoint GitHub](https://github.com/pinpoint-apm/pinpoint)
3. [CAT 官方文档](https://github.com/dianping/cat/wiki)
4. [Elastic APM 文档](https://www.elastic.co/guide/en/apm/guide/current/index.html)

### 7.2 开源项目

1. [skywalking-showcase](https://github.com/apache/skywalking-showcase) - 演示环境
2. [opentelemetry-java](https://github.com/open-telemetry/opentelemetry-java) - OTel Java SDK

### 7.3 学习资料

1. [OpenTelemetry 官方文档](https://opentelemetry.io/docs/)
2. [Distributed Tracing 白皮书](https://wu-sheng.gitbooks.io/opentracing-io/content/)
3. [W3C Trace Context](https://www.w3.org/TR/trace-context/)

---

**维护者**：项目团队
**最后更新**：2026年
