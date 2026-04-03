# Jaeger分布式追踪

## 概述

Jaeger是由Uber开源的分布式追踪系统，受Google Dapper论文启发，实现了OpenTracing标准。它帮助监控和诊断基于微服务架构的分布式系统，提供请求链路可视化、性能分析、依赖关系发现等功能，是解决复杂系统可观测性的关键工具。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        Jaeger 架构                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────┐     ┌─────────────┐     ┌─────────────────────────┐  │
│   │  Client Lib │────►│    Agent    │────►│       Collector         │  │
│   │(OpenTracing)│     │  (Daemon)   │     │    (接收/处理)          │  │
│   └─────────────┘     └─────────────┘     └───────────┬─────────────┘  │
│          │                                            │                 │
│   ┌──────┴──────┐                                    │                 │
│   │  Instrument │                                    │                 │
│   │    Code     │                    ┌───────────────┼───────────────┐ │
│   │ • Span创建  │                    │               │               │ │
│   │ • Context   │                    ▼               ▼               ▼ │ │
│   │   传播      │           ┌────────────┐  ┌────────────┐  ┌─────────┴─┐│
│   │ • 标签设置  │           │  Cassandra │  │Elasticsearch│  │  Kafka    ││
│   │ • 日志记录  │           │            │  │            │  │  (Buffer) ││
│   └─────────────┘           └────────────┘  └────────────┘  └───────────┘│
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                        查询层                                    │  │
│   │  ┌─────────────┐     ┌─────────────┐     ┌─────────────────┐   │  │
│   │  │    Query    │◄────│   Ingester  │◄────│    Storage      │   │  │
│   │  │   Service   │     │  (读取处理)  │     │  (Cassandra/    │   │  │
│   │  └──────┬──────┘     └─────────────┘     │   Elasticsearch)│   │  │
│   │         │                                 └─────────────────┘   │  │
│   │         └─────────────────┬────────────────────────────────────   │  │
│   └───────────────────────────┼───────────────────────────────────────┘  │
│                               │                                          │
│                               ▼                                          │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                        UI / API                                  │  │
│   │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐ │  │
│   │  │  Web UI  │  │  Trace   │  │ Service  │  │   Dependencies   │ │  │
│   │  │(搜索/查看)│  │  View    │  │   Map    │  │      Graph       │ │  │
│   │  └──────────┘  └──────────┘  └──────────┘  └──────────────────┘ │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. Collector

```yaml
# collector.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: jaeger-collector
data:
  collector.yaml: |
    es:
      server-urls: http://elasticsearch:9200
      username: elastic
      password: ${ES_PASSWORD}
      index-prefix: jaeger

    collector:
      num-workers: 50
      queue-size: 2000

      # 批处理配置
      batch:
        size: 100
        min-threshold: 10
        processes: 1

      # OTLP接收器
      otlp:
        enabled: true
        grpc:
          host-port: 0.0.0.0:4317
        http:
          host-port: 0.0.0.0:4318
          cors:
            allowed-origins: "*"
            allowed-headers: "*"

      # Kafka写入
      kafka:
        producer:
          brokers: kafka:9092
          topic: jaeger-spans
          batch-linger: 1s
          batch-min-messages: 100
          batch-max-messages: 1000

      # 健康检查
      health-check:
        http-port: 14269

      # 指标暴露
      metrics:
        backend: prometheus
        http-route: /metrics
```

### 2. Agent

```yaml
# agent.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: jaeger-agent
spec:
  template:
    spec:
      containers:
        - name: agent
          image: jaegertracing/jaeger-agent:latest
          args:
            - --reporter.grpc.host-port=jaeger-collector:14250
            - --reporter.grpc.retry.max=3
            - --reporter.grpc.tls.enabled=false

            # 缓冲区配置
            - --processor.jaeger-binary.server-queue-size=1000
            - --processor.jaeger-binary.workers=10
            - --processor.jaeger-compact.server-queue-size=1000
            - --processor.jaeger-compact.workers=10
            - --processor.zipkin-compact.server-queue-size=1000
            - --processor.zipkin-compact.workers=10

            # 暴露端口
            - --processor.jaeger-binary.server-host-port=0.0.0.0:6832
            - --processor.jaeger-compact.server-host-port=0.0.0.0:6831
            - --processor.zipkin-compact.server-host-port=0.0.0.0:5775

            # 健康检查
            - --http-server.host-port=0.0.0.0:5778
          ports:
            - containerPort: 6831
              protocol: UDP
            - containerPort: 6832
              protocol: UDP
            - containerPort: 5775
              protocol: UDP
            - containerPort: 5778
              protocol: TCP
```

### 3. Query Service

```yaml
# query.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: jaeger-query
data:
  query.yaml: |
    query:
      base-path: /jaeger
      static-files: /go/jaeger-ui/

      # UI配置
      ui:
        menu:
          - label: "关于"
            items:
              - label: "文档"
                url: "https://www.jaegertracing.io/docs/"
                anchorTarget: _blank

      # 依赖图
      dependencies:
        menuEnabled: true

      # 追踪查看
      trace:
        # 默认时间范围
        lookback: 1h
        # 最大追踪数
        maxLimit: 1500

      # 搜索配置
      search:
        maxLookback: 72h
        maxDuration: 1h

      # 认证
      oidc:
        issuer: https://auth.example.com
        client-id: jaeger-query
        client-secret: ${OIDC_SECRET}
```

## 应用集成

### OpenTelemetry SDK配置

```yaml
# otel-collector.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024

  resource:
    attributes:
      - key: service.namespace
        value: production
        action: upsert
      - key: deployment.environment
        value: prod
        action: upsert

  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 1000
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: slow_requests
        type: latency
        latency: {threshold_ms: 500}

exporters:
  jaeger:
    endpoint: jaeger-collector:14250
    tls:
      insecure: true

  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, resource, tail_sampling]
      exporters: [jaeger]
```

### Java应用配置

```yaml
# application-jaeger.yaml
opentelemetry:
  traces:
    exporter: jaeger
    sampler:
      type: parentbased_traceidratio
      ratio: 0.1

  jaeger:
    endpoint: http://jaeger-collector:14250
    timeout: 10s

  resource:
    service:
      name: order-service
      version: 1.2.0
    attributes:
      - key: host.name
        value: ${HOSTNAME}
      - key: service.namespace
        value: ecommerce
      - key: deployment.environment
        value: production
```

### Go应用配置

```yaml
# tracer-config.yaml
tracer:
  enabled: true
  service_name: payment-service
  service_version: v1.0.0

  exporter:
    type: otlp
    endpoint: jaeger-collector:4317
    insecure: true

  sampler:
    type: parentbased_traceidratio
    ratio: 0.05

  propagation:
    - tracecontext
    - baggage
    - jaeger

  resource:
    attributes:
      service.namespace: payment
      deployment.environment: prod
      host.name: ${HOSTNAME}

  span_limits:
    attribute_count_limit: 128
    event_count_limit: 128
    link_count_limit: 128
```

## 上下文传播

```
┌─────────────────────────────────────────────────────────────────┐
│                    分布式上下文传播                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Client          Request          Server                         │
│    │                │               │                           │
│    │  1.创建Span    │               │                           │
│    │◄──────────────┤               │                           │
│    │                │               │                           │
│    │  2.注入上下文  │               │                           │
│    │  trace_id=abc  │               │                           │
│    │  span_id=xyz   │               │                           │
│    │  baggage=k:v   │               │                           │
│    │                │               │                           │
│    │ ──────────────►│               │                           │
│    │  Uber-Trace-Id:abc:xyz:0:1    │                           │
│    │  baggage-user-id:12345        │                           │
│    │                │               │                           │
│    │                │ ─────────────►│  3.提取上下文             │
│    │                │               │  trace_id=abc             │
│    │                │               │  span_id=xyz              │
│    │                │               │                           │
│    │                │               │  4.创建子Span             │
│    │                │               │  parent_span_id=xyz       │
│    │                │               │                           │
└─────────────────────────────────────────────────────────────────┘
```

## 采样策略

```yaml
# sampling.yaml
sampling:
  strategies:
    # 默认采样率
    default:
      type: probabilistic
      param: 0.1

    # 服务级别配置
    per_operation:
      service_a:
        - operation: /api/health
          type: probabilistic
          param: 0.0  # 不采样健康检查
        - operation: /api/payment
          type: probabilistic
          param: 1.0  # 全量采样支付接口

      service_b:
        - operation: /api/search
          type: ratelimiting
          param: 100  # 每秒最多100个

    # 自适应采样
    adaptive:
      enabled: true
      target_traces_per_second: 100
      max_operations: 2000
```

## 存储配置

```yaml
# storage-elasticsearch.yaml
es:
  server-urls: http://elasticsearch:9200
  username: ${ES_USERNAME}
  password: ${ES_PASSWORD}

  # 索引配置
  index-prefix: jaeger
  index-date-separator: "-"

  # 分片配置
  num-shards: 5
  num-replicas: 1

  # 批量配置
  bulk:
    size: 5000000
    workers: 1
    flush-interval: 200ms

  # 超时配置
  timeout: 120s
  max-retry-timeout: 120s

  # 索引生命周期
  ilm:
    enabled: true
    policy-name: jaeger-ilm-policy
    alias: jaeger-span
```

## 告警规则

```yaml
# jaeger-alerts.yaml
groups:
  - name: jaeger-alerts
    rules:
      # 追踪丢失率告警
      - alert: HighTraceDropRate
        expr: |
          (jaeger_collector_spans_dropped_total /
           jaeger_collector_spans_received_total) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Jaeger collector dropping spans"
          description: "Drop rate is {{ $value | humanizePercentage }}"

      # 存储延迟告警
      - alert: HighStorageLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(jaeger_storage_latency_bucket[5m])) by (le)
          ) > 1
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "High storage write latency"

      # 查询延迟告警
      - alert: HighQueryLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(jaeger_query_latency_bucket[5m])) by (le)
          ) > 5
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High query latency"
```

## 最佳实践

1. **采样策略**：生产环境使用自适应采样，平衡存储和完整性
2. **上下文传播**：确保所有服务间调用都传递追踪上下文
3. **标签规范**：统一命名规范，避免标签冲突
4. **关联日志**：日志中嵌入trace_id，实现追踪和日志关联
5. **性能优化**：合理设置缓冲区大小，避免影响应用性能
