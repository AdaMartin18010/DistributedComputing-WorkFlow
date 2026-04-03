# Zipkin追踪系统

## 概述

Zipkin是由Twitter开源的分布式追踪系统，基于Google Dapper论文实现。它是分布式追踪领域的先驱项目，提供了完整的链路追踪、查询和可视化功能。Zipkin设计简洁、部署简单，适合中小规模微服务架构的可观测性需求。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Zipkin 架构                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────┐    ┌─────────────┐    ┌─────────────────────────┐   │
│   │  Instrument │───►│   Reporter  │───►│      Collector          │   │
│   │   Library   │    │  (Async)    │    │  (HTTP/Kafka接收)       │   │
│   │             │    │             │    └───────────┬─────────────┘   │
│   │ • brave     │    │ • 批量发送  │                │                 │
│   │ • zipkin-js │    │ • 队列缓冲  │                │                 │
│   │ • zipkin-go │    │ • 失败重试  │                ▼                 │
│   └─────────────┘    └─────────────┘    ┌─────────────────────────┐   │
│                                         │       Storage           │   │
│   ┌─────────────┐                       │  ┌───────┐ ┌─────────┐  │   │
│   │   Agent     │                       │  │MySQL  │ │ Cassandra│  │   │
│   │  (可选)     │──────────────────────►│  │       │ │          │  │   │
│   └─────────────┘                       │  ├───────┤ ├─────────┤  │   │
│                                         │  │ES     │ │  Kafka  │  │   │
│                                         │  │       │ │         │  │   │
│                                         │  └───────┘ └─────────┘  │   │
│                                         └───────────┬─────────────┘   │
│                                                     │                  │
│   ┌─────────────────────────────────────────────────▼──────────────┐  │
│   │                          Query API                              │  │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐    │  │
│   │  │ Span查询    │  │ 依赖分析    │  │   聚合统计          │    │  │
│   │  │ • trace_id  │  │ • 服务拓扑  │  │   • 延迟分布        │    │  │
│   │  │ • service   │  │ • 调用关系  │  │   • 请求量          │    │  │
│   │  │ • time      │  │             │  │   • 错误率          │    │  │
│   │  └─────────────┘  └─────────────┘  └─────────────────────┘    │  │
│   └────────────────────────────────────────────────────────────────┘  │
│                                    │                                   │
│                                    ▼                                   │
│   ┌────────────────────────────────────────────────────────────────┐  │
│   │                          Web UI                                 │  │
│   │  ┌──────────────┐ ┌──────────────┐ ┌────────────────────────┐ │  │
│   │  │  Trace搜索   │ │  Trace详情   │ │   依赖关系图           │ │  │
│   │  │              │ │              │ │                        │ │  │
│   │  │ • 时间范围   │ │ • Span列表   │ │ • 服务拓扑             │ │  │
│   │  │ • 服务名     │ │ • 时序图     │ │ • 调用链路             │ │  │
│   │  │ • 标签过滤   │ │ • 依赖图     │ │ • 延迟热力图           │ │  │
│   │  └──────────────┘ └──────────────┘ └────────────────────────┘ │  │
│   └────────────────────────────────────────────────────────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. Collector

```yaml
# zipkin-server.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: zipkin-server
spec:
  replicas: 2
  template:
    spec:
      containers:
        - name: zipkin
          image: openzipkin/zipkin:latest
          ports:
            - containerPort: 9411
          env:
            # 存储配置 - Elasticsearch
            - name: STORAGE_TYPE
              value: elasticsearch
            - name: ES_HOSTS
              value: http://elasticsearch:9200
            - name: ES_USERNAME
              value: elastic
            - name: ES_PASSWORD
              valueFrom:
                secretKeyRef:
                  name: elastic-secret
                  key: password
            - name: ES_INDEX
              value: zipkin
            - name: ES_INDEX_SHARDS
              value: "5"
            - name: ES_INDEX_REPLICAS
              value: "1"

            # 存储配置 - Cassandra替代方案
            # - name: STORAGE_TYPE
            #   value: cassandra3
            # - name: CASSANDRA_ENSURE_SCHEMA
            #   value: "true"
            # - name: CASSANDRA_CONTACT_POINTS
            #   value: cassandra:9042

            # 采样配置
            - name: SAMPLER_TYPE
              value: count
            - name: SAMPLER_COUNT
              value: "10"

            # 查询配置
            - name: QUERY_TIMEOUT
              value: "10s"
            - name: QUERY_LOG_LEVEL
              value: INFO

            # 自追踪
            - name: SELF_TRACING_ENABLED
              value: "true"
            - name: SELF_TRACING_SAMPLE_RATE
              value: "1.0"

            # 指标
            - name: METRICS_STORAGE_TYPE
              value: prometheus
          resources:
            requests:
              memory: "512Mi"
              cpu: "250m"
            limits:
              memory: "2Gi"
              cpu: "1000m"
          livenessProbe:
            httpGet:
              path: /health
              port: 9411
            initialDelaySeconds: 60
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /health
              port: 9411
            initialDelaySeconds: 10
            periodSeconds: 5
```

### 2. Kafka中间件配置

```yaml
# zipkin-kafka.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: zipkin-collector-kafka
data:
  collector.kafka:
    # Kafka作为缓冲层
    bootstrap-servers: kafka:9092
    topic: zipkin

    # 消费者配置
    consumer:
      group-id: zipkin-collector
      auto-offset-reset: earliest
      max-poll-records: 500

    # 生产者配置(用于写入storage)
    producer:
      acks: all
      retries: 3
      batch-size: 16384
      linger-ms: 5
      buffer-memory: 33554432
```

## 客户端集成

### Java (Brave)

```yaml
# application-zipkin.yml
spring:
  zipkin:
    base-url: http://zipkin-server:9411
    sender:
      type: kafka  # 或 rabbit, web
    kafka:
      topic: zipkin

  sleuth:
    enabled: true
    sampler:
      probability: 0.1  # 采样率10%

    # 异步配置
    async:
      enabled: true
      config:
        core-pool-size: 10
        max-pool-size: 50
        queue-capacity: 1000

    # 标签配置
    baggage:
      correlation-fields:
        - user-id
        - request-id
      tag-fields:
        - user-id

    # 传播配置
    propagation:
      type: W3C,B3  # W3C Trace Context + B3 Propagation

    # 忽略路径
    web:
      skip-pattern: "/api/health|/actuator/.*"
```

### 依赖配置

```xml
<!-- pom.xml -->
<dependencies>
    <!-- Sleuth + Zipkin -->
    <dependency>
        <groupId>org.springframework.cloud</groupId>
        <artifactId>spring-cloud-starter-sleuth</artifactId>
    </dependency>
    <dependency>
        <groupId>org.springframework.cloud</groupId>
        <artifactId>spring-cloud-sleuth-zipkin</artifactId>
    </dependency>

    <!-- Kafka Sender -->
    <dependency>
        <groupId>org.springframework.kafka</groupId>
        <artifactId>spring-kafka</artifactId>
    </dependency>
</dependencies>
```

### Go (zipkin-go)

```yaml
# zipkin-config.yaml
zipkin:
  enabled: true
  service:
    name: payment-service
    version: 1.0.0

  endpoint:
    url: http://zipkin-server:9411/api/v2/spans
    timeout: 5s

  reporter:
    type: http  # http, kafka, log
    batch-size: 100
    batch-timeout: 1s
    max-queue-size: 1000

  sampler:
    type: count  # always, never, count, probability
    param: 10    # 每10个请求采样1个

  propagation:
    format: b3  # b3, w3c

  local-endpoint:
    ip: ${HOST_IP}
    port: 8080
```

### JavaScript/Node.js

```yaml
# zipkin-js.yaml
zipkin:
  service:
    name: frontend-service

  tracer:
    recorder:
      type: http
      endpoint: http://zipkin-server:9411/api/v2/spans

    sampler:
      type: probability
      rate: 0.1

  middleware:
    - type: express
      options:
        port: 3000
    - type: http-client
    - type: fetch

  instrumentation:
    postgres: true
    redis: true
    http: true
```

## B3传播格式

```
┌────────────────────────────────────────────────────────────────┐
│                     B3 Propagation                              │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  Header名称          说明                                      │
│  ──────────────────────────────────────────────────────────    │
│  X-B3-TraceId        追踪ID，64位或128位十六进制               │
│  X-B3-SpanId         Span ID，64位十六进制                     │
│  X-B3-ParentSpanId   父Span ID（可选）                         │
│  X-B3-Sampled        采样标志：0=不采样, 1=采样, d=调试        │
│  X-B3-Flags          调试标志：1=强制采样                      │
│  b3                  单Header模式（W3C兼容）                   │
│                                                                │
│  示例：                                                        │
│  X-B3-TraceId: 463ac35c9f6413ad48485a3953bb6124               │
│  X-B3-SpanId: a2fb4a1d1a96d312                               │
│  X-B3-ParentSpanId: 0020000000000001                         │
│  X-B3-Sampled: 1                                              │
│                                                                │
│  单Header模式：                                                │
│  b3: 463ac35c9f6413ad48485a3953bb6124-a2fb4a1d1a96d312-1    │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

## 采样配置

```yaml
# sampler.yaml
sampling:
  # 基于概率的采样
  probability:
    rate: 0.1  # 10%采样率

  # 基于计数的采样
  count:
    interval: 10  # 每10个请求采样1个

  # 基于速率的采样
  rate_limiting:
    max_per_second: 100

  # 自适应采样
  adaptive:
    enabled: true
    target_rate: 0.1
    min_samples: 10
    max_samples: 1000
    window_size: 60s

  # 按操作采样
  per_operation:
    rules:
      - operation: GET /health
        sampler: never
      - operation: POST /payment
        sampler: always
      - operation: GET /api/.*
        sampler:
          type: probability
          rate: 0.05
```

## API查询示例

```bash
# 查询追踪列表
curl "http://zipkin:9411/api/v2/traces?serviceName=payment-service&limit=10"

# 按时间范围查询
curl "http://zipkin:9411/api/v2/traces?serviceName=order-service&lookback=1h&limit=100"

# 按标签查询
curl "http://zipkin:9411/api/v2/traces?serviceName=user-service&tag=error=true"

# 获取单个追踪
curl "http://zipkin:9411/api/v2/trace/463ac35c9f6413ad48485a3953bb6124"

# 获取依赖关系
curl "http://zipkin:9411/api/v2/dependencies?startTs=$(date -d '1 hour ago' +%s)000"

# 获取服务列表
curl "http://zipkin:9411/api/v2/services"

# 获取Span名称列表
curl "http://zipkin:9411/api/v2/spans?serviceName=payment-service"
```

## 存储配置

```yaml
# storage-mysql.yaml
storage:
  type: mysql
  mysql:
    host: mysql
    port: 3306
    database: zipkin
    username: zipkin
    password: ${MYSQL_PASSWORD}

    # 连接池
    max-connections: 10
    use-ssl: false

    # 优化
    zipkin2.storage.mysql:
      autocomplete-keys: "http.method,http.path"
      autocomplete-ttl: 3600000
      autocomplete-cardinality: 20000
```

## 最佳实践

1. **采样控制**：生产环境使用概率采样，采样率0.1%-1%
2. **异步发送**：使用Kafka/RabbitMQ缓冲，避免影响应用性能
3. **上下文传播**：确保所有服务间调用传递B3 Header
4. **标签限制**：控制Span标签数量，避免数据膨胀
5. **存储选型**：小数据量用MySQL，大数据量用Elasticsearch/Cassandra
