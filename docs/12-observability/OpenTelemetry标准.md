# OpenTelemetry标准

## 概述

OpenTelemetry（简称OTel）是CNCF孵化的可观测性框架，由OpenTracing和OpenCensus合并而成。它提供了统一的API、SDK和数据规范，用于收集分布式追踪、指标和日志，是云原生时代可观测性的事实标准。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     OpenTelemetry 架构                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                        应用层                                    │  │
│   │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐ │  │
│   │  │  Auto    │  │  Manual  │  │  SDK     │  │  Collector       │ │  │
│   │  │Instrumentation│Instrumentation│         │  │  (Agent/Standalone)│ │  │
│   │  │ 自动埋点  │  │ 手动埋点  │  │ 初始化   │  │                 │ │  │
│   │  └──────────┘  └──────────┘  └──────────┘  └──────────────────┘ │  │
│   └────────────────────────────────┬──────────────────────────────────┘  │
│                                    │                                     │
│   ┌────────────────────────────────▼──────────────────────────────────┐  │
│   │                        API层                                     │  │
│   │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │  │
│   │  │   Trace API  │  │  Metrics API │  │     Logs API         │   │  │
│   │  │ • Span创建   │  │ • Counter    │  │ • LogRecord          │   │  │
│   │  │ • Context    │  │ • Histogram  │  │ • Severity           │   │  │
│   │  │ • Propagator │  │ • Observable │  │ • Attributes         │   │  │
│   │  └──────────────┘  └──────────────┘  └──────────────────────┘   │  │
│   └────────────────────────────────┬──────────────────────────────────┘  │
│                                    │                                     │
│   ┌────────────────────────────────▼──────────────────────────────────┐  │
│   │                        SDK层                                     │  │
│   │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐   │  │
│   │  │  Tracer      │  │  Meter       │  │     Logger           │   │  │
│   │  │  Provider    │  │  Provider    │  │     Provider         │   │  │
│   │  │              │  │              │  │                      │   │  │
│   │  │ + Sampler    │  │ + View       │  │ + Processor          │   │  │
│   │  │ + Processor  │  │ + Aggregation│  │ + Exporter           │   │  │
│   │  │ + Exporter   │  │ + Exporter   │  │                      │   │  │
│   │  └──────────────┘  └──────────────┘  └──────────────────────┘   │  │
│   └────────────────────────────────┬──────────────────────────────────┘  │
│                                    │                                     │
│                                    ▼                                     │
│   ┌───────────────────────────────────────────────────────────────────┐ │
│   │                      OTLP协议                                    │ │
│   │         (OpenTelemetry Protocol - gRPC/HTTP)                     │ │
│   └────────────────────────────────┬──────────────────────────────────┘ │
│                                    │                                     │
│                                    ▼                                     │
│   ┌───────────────────────────────────────────────────────────────────┐ │
│   │                   OpenTelemetry Collector                        │ │
│   │  ┌─────────────┐  ┌─────────────┐  ┌──────────────────────────┐ │ │
│   │  │  Receiver   │  │  Processor  │  │       Exporter           │ │ │
│   │  │ • OTLP      │  │ • Batch     │  │ • OTLP (Jaeger/Tempo)   │ │ │
│   │  │ • Prometheus│  │ • Memory    │  │ • Prometheus            │ │ │
│   │  │ • Zipkin    │  │ • Resource  │  │ • Zipkin                │ │ │
│   │  │ • Jaeger    │  │ • Sampling  │  │ • Kafka                 │ │ │
│   │  └─────────────┘  └─────────────┘  └──────────────────────────┘ │ │
│   └───────────────────────────────────────────────────────────────────┘ │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心概念

### 信号（Signals）

```yaml
# OpenTelemetry三大信号
signals:
  traces:
    description: 分布式追踪
    components:
      - span: 追踪的基本单元
      - trace: 一组Span组成的调用链
      - context: 传播上下文
    use_case: 请求链路分析、性能瓶颈定位
    
  metrics:
    description: 指标数据
    components:
      - counter: 单调递增计数器
      - up_down_counter: 可增可减计数器
      - histogram: 直方图分布
      - observable_gauge: 可观察仪表盘
    use_case: 性能监控、容量规划
    
  logs:
    description: 日志记录
    components:
      - log_record: 日志记录
      - severity: 严重级别
      - body: 日志内容
    use_case: 故障排查、审计追踪
```

## Collector配置

```yaml
# otel-collector-config.yaml
receivers:
  # OTLP接收器
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 64
        max_concurrent_streams: 100
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins: ["*"]
          allowed_headers: ["*"]
          max_age: 7200

  # Prometheus接收器
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otel-collector'
          scrape_interval: 10s
          static_configs:
            - targets: ['localhost:8888']

  # Zipkin接收器
  zipkin:
    endpoint: 0.0.0.0:9411

  # Jaeger接收器
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
      thrift_compact:
        endpoint: 0.0.0.0:6831

processors:
  # 批处理器
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048

  # 内存限制器
  memory_limiter:
    limit_mib: 1500
    spike_limit_mib: 512
    check_interval: 5s

  # 资源处理器
  resource:
    attributes:
      - key: environment
        value: production
        action: upsert
      - key: host.name
        from_attribute: host.name
        action: upsert
      - key: deployment.environment
        from_attribute: environment
        action: insert

  # 尾部采样
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 1000
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: latency
        type: latency
        latency: {threshold_ms: 500}
      - name: probabilistic
        type: probabilistic
        probabilistic: {sampling_percentage: 10}

  # 属性处理器
  attributes:
    actions:
      - key: http.method
        action: delete
      - key: user.password
        action: hash
        
  # 指标转换
  metricstransform:
    transforms:
      - include: http_requests_total
        action: update
        operations:
          - action: add_label
            new_label: environment
            new_value: production

exporters:
  # OTLP导出
  otlp:
    endpoint: jaeger:4317
    tls:
      insecure: true
    timeout: 30s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s

  # Prometheus远程写入
  prometheusremotewrite:
    endpoint: http://prometheus:9090/api/v1/write
    tls:
      insecure: true

  # Loki导出
  loki:
    endpoint: http://loki:3100/loki/api/v1/push
    tls:
      insecure: true
    labels:
      attributes:
        severity: ""
        service.name: "service"

  # Kafka导出
  kafka:
    brokers:
      - kafka:9092
    topic: otel-data
    encoding: otlp_proto
    producer:
      max_message_bytes: 1000000
      required_acks: 1

  # 日志导出
  logging:
    loglevel: debug
    sampling_initial: 2
    sampling_thereafter: 500

  # 文件导出（用于调试）
  file:
    path: ./otel-data.json

extensions:
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133

  # 性能分析
  pprof:
    endpoint: 0.0.0.0:1777

  # 指标暴露
  prometheus:
    endpoint: 0.0.0.0:8889

  # 内存检查
  memory_ballast:
    size_mib: 512

service:
  extensions: [health_check, pprof, prometheus, memory_ballast]
  
  pipelines:
    traces:
      receivers: [otlp, jaeger, zipkin]
      processors: [memory_limiter, resource, tail_sampling, batch]
      exporters: [otlp, kafka]
      
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, resource, metricstransform, batch]
      exporters: [prometheusremotewrite, kafka]
      
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, attributes, batch]
      exporters: [loki, kafka]
```

## 传播协议

```yaml
# propagator-config.yaml
propagators:
  # W3C Trace Context (推荐)
  tracecontext:
    headers:
      - traceparent
      - tracestate
    format: |
      traceparent: 00-{trace-id}-{parent-id}-{trace-flags}
      tracestate: vendor1=value1,vendor2=value2
    example: |
      traceparent: 00-0af7651916cd43dd8448eb211c80319c-b7ad6b7169203331-01
      tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

  # W3C Baggage
  baggage:
    header: baggage
    format: key1=value1,key2=value2
    example: baggage: userId=alice,serverNode=DF%2028,isProduction=false

  # B3 Propagation (Zipkin兼容)
  b3:
    headers:
      - X-B3-TraceId
      - X-B3-SpanId
      - X-B3-ParentSpanId
      - X-B3-Sampled
      - X-B3-Flags
    single_header: b3

  # Jaeger Propagation
  jaeger:
    headers:
      - uber-trace-id
      - jaeger-baggage

  # OpenTracing Propagation
  opentracing:
    headers:
      - ot-tracer-traceid
      - ot-tracer-spanid
      - ot-tracer-sampled
```

## 采样配置

```yaml
# sampling-config.yaml
sampling:
  # 头部采样（Head-based）
  head_based:
    parent_based:
      root:
        trace_id_ratio:
          ratio: 0.1
      remote_parent_sampled:
        always_on: {}
      remote_parent_not_sampled:
        always_off: {}
      local_parent_sampled:
        always_on: {}
      local_parent_not_sampled:
        always_off: {}

  # 比率采样
  trace_id_ratio:
    ratio: 0.1  # 10%采样率

  # 限速采样
  rate_limiting:
    qps: 100  # 每秒100条

  # 尾部采样（Tail-based）- 需要Collector支持
  tail_based:
    decision_wait: 10s
    policies:
      - name: error_policy
        type: status_code
        status_code: [ERROR]
      - name: latency_policy
        type: latency
        threshold_ms: 1000
      - name: probabilistic_policy
        type: probabilistic
        percentage: 10
```

## OTLP协议规范

```protobuf
// OTLP定义简化示例
syntax = "proto3";

package opentelemetry.proto.trace.v1;

message TracesData {
  repeated ResourceSpans resource_spans = 1;
}

message ResourceSpans {
  Resource resource = 1;
  repeated ScopeSpans scope_spans = 2;
}

message ScopeSpans {
  InstrumentationScope scope = 1;
  repeated Span spans = 2;
}

message Span {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  bytes parent_span_id = 4;
  string name = 5;
  SpanKind kind = 6;
  fixed64 start_time_unix_nano = 7;
  fixed64 end_time_unix_nano = 8;
  repeated KeyValue attributes = 9;
  repeated Event events = 10;
  Status status = 11;
}

enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}
```

## 语义约定

```yaml
# semantic-conventions.yaml
semantic_conventions:
  # 通用属性
  general:
    - service.name: "my-service"
    - service.version: "1.0.0"
    - deployment.environment: "production"
    - host.name: "host-01"
    - host.arch: "amd64"
    - process.pid: 1234
    
  # HTTP属性
  http:
    - http.method: "GET"
    - http.url: "https://example.com/api/users"
    - http.target: "/api/users"
    - http.host: "example.com"
    - http.scheme: "https"
    - http.status_code: 200
    - http.response_content_length: 1024
    - http.route: "/api/users/:id"
    
  # 数据库属性
  db:
    - db.system: "mysql"
    - db.connection_string: "mysql://localhost:3306"
    - db.user: "admin"
    - db.statement: "SELECT * FROM users WHERE id = ?"
    - db.operation: "SELECT"
    - db.sql.table: "users"
    
  # 消息队列属性
  messaging:
    - messaging.system: "kafka"
    - messaging.destination: "orders"
    - messaging.destination_kind: "topic"
    - messaging.operation: "send"
    - messaging.kafka.partition: 0
    - messaging.message_id: "abc123"
    
  # RPC属性
  rpc:
    - rpc.system: "grpc"
    - rpc.service: "mypackage.MyService"
    - rpc.method: "MyMethod"
    - rpc.grpc.status_code: 0
```

## 最佳实践

1. **自动埋点优先**：使用自动Instrumentation减少代码侵入
2. **统一传播**：全链路使用W3C Trace Context标准
3. **尾部采样**：生产环境使用尾部采样降低存储成本
4. **资源属性**：设置service.name、deployment.environment等核心属性
5. **Collector部署**：使用Agent模式收集，Gateway模式汇聚
