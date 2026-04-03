# Loki日志系统

## 概述

Loki是由Grafana Labs开发的水平可扩展、高可用性的日志聚合系统。与传统ELK栈不同，Loki采用"只索引标签、不索引内容"的设计理念，大幅降低了存储成本，同时保持了高效的查询能力。它与Prometheus共享标签系统，实现了指标和日志的无缝关联。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          Loki 架构                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌──────────────┐      │
│   │  Agent  │───►│  Promtail│───►│  Distributor│───►│    Ingester  │     │
│   │(App/Node)│    │ (Agent) │    │  (接收/分发)│    │  (写入/索引) │     │
│   └─────────┘    └─────────┘    └─────────┘    └──────┬───────┘     │
│        │                                              │               │
│   ┌────┴────┐                                         │               │
│   │  Push   │                                         │               │
│   │  API    │    ┌────────────────────────────────────┘               │
│   └─────────┘    │                                                   │
│                  ▼                                                   │
│   ┌─────────────────────────────────────────────────────────┐       │
│   │                      存储层                              │       │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐  │       │
│   │  │   Index     │  │    Chunks   │  │   Object Store  │  │       │
│   │  │  (TSDB/     │  │  (日志内容)  │  │  (S3/GCS/Ceph)  │  │       │
│   │  │  BoltDB)    │  │             │  │                 │  │       │
│   │  └─────────────┘  └─────────────┘  └─────────────────┘  │       │
│   └─────────────────────────┬───────────────────────────────┘       │
│                             │                                         │
│   ┌─────────────────────────▼───────────────────────────────┐       │
│   │                      查询层                              │       │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐  │       │
│   │  │   Query     │  │  Query      │  │   Ruler/        │  │       │
│   │  │  Frontend   │  │  Scheduler  │  │   Alerting      │  │       │
│   │  └─────────────┘  └─────────────┘  └─────────────────┘  │       │
│   └─────────────────────────┬───────────────────────────────┘       │
│                             │                                         │
│                             ▼                                         │
│   ┌─────────────────────────────────────────────────────────┐       │
│   │                        Grafana                           │       │
│   │              (LogQL查询 + 可视化展示)                     │       │
│   └─────────────────────────────────────────────────────────┘       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. Loki Server

```yaml
# loki.yaml
auth_enabled: true

server:
  http_listen_port: 3100
  grpc_listen_port: 9096
  grpc_server_max_recv_msg_size: 104857600
  grpc_server_max_send_msg_size: 104857600

common:
  path_prefix: /loki
  storage:
    filesystem:
      chunks_directory: /loki/chunks
      rules_directory: /loki/rules
  replication_factor: 3
  ring:
    kvstore:
      store: memberlist

memberlist:
  join_members:
    - loki-memberlist
  dead_node_reclaim_time: 30s
  gossip_to_dead_nodes_time: 15s

schema_config:
  configs:
    - from: 2024-01-01
      store: tsdb
      object_store: s3
      schema: v13
      index:
        prefix: index_
        period: 24h
      chunks:
        prefix: chunks_
        period: 24h

storage_config:
  tsdb_shipper:
    active_index_directory: /loki/tsdb-index
    cache_location: /loki/tsdb-cache
    cache_ttl: 24h

  aws:
    s3: s3://us-east-1/loki-logs
    access_key_id: ${AWS_ACCESS_KEY}
    secret_access_key: ${AWS_SECRET_KEY}
    s3forcepathstyle: false
    insecure: false

  boltdb_shipper:
    active_index_directory: /loki/boltdb-shipper-active
    cache_location: /loki/boltdb-shipper-cache
    cache_ttl: 24h

compactor:
  working_directory: /loki/compactor
  shared_store: s3
  compaction_interval: 10m
  retention_enabled: true
  retention_delete_delay: 2h
  retention_delete_worker_count: 150

limits_config:
  reject_old_samples: true
  reject_old_samples_max_age: 168h
  ingestion_rate_mb: 64
  ingestion_burst_size_mb: 128
  per_stream_rate_limit: 10MB
  per_stream_rate_limit_burst: 50MB
  max_global_streams_per_user: 10000
  max_query_parallelism: 32
  max_query_series: 1000
  max_query_length: 721h
  retention_period: 744h

chunk_store_config:
  max_look_back_period: 168h

table_manager:
  retention_deletes_enabled: true
  retention_period: 168h

query_scheduler:
  max_outstanding_requests_per_tenant: 32768

frontend:
  max_outstanding_per_tenant: 4096
  compress_responses: true
  log_queries_longer_than: 5s

querier:
  max_concurrent: 10
  query_timeout: 5m
  engine:
    timeout: 5m
    max_look_back_period: 30s

ruler:
  storage:
    type: s3
    s3:
      bucketnames: loki-rules
  rule_path: /loki/rules
  alertmanager_url: http://alertmanager:9093
  ring:
    kvstore:
      store: memberlist
  enable_api: true
```

### 2. Promtail

```yaml
# promtail.yaml
server:
  http_listen_port: 9080
  grpc_listen_port: 0

positions:
  filename: /tmp/positions.yaml

clients:
  - url: http://loki:3100/loki/api/v1/push
    batchwait: 1s
    batchsize: 1048576
    timeout: 10s
    backoff_config:
      min_period: 500ms
      max_period: 5m
      max_retries: 10

scrape_configs:
  # Kubernetes Pods日志
  - job_name: kubernetes-pods
    kubernetes_sd_configs:
      - role: pod
    pipeline_stages:
      - cri: {}
      - multiline:
          firstline: '^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}'
          max_wait_time: 3s
      - regex:
          expression: '(?P<level>INFO|WARN|ERROR|DEBUG)'
      - labels:
          level:
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_controller_name]
        regex: ([0-9a-z-.]+?)(-[0-9a-f]{8,10})?
        target_label: __tmp_controller_name

      - source_labels: [__meta_kubernetes_pod_label_app_kubernetes_io_name]
        target_label: app

      - source_labels: [__meta_kubernetes_namespace]
        target_label: namespace

      - source_labels: [__meta_kubernetes_pod_name]
        target_label: pod

      - source_labels: [__meta_kubernetes_pod_container_name]
        target_label: container

      - source_labels: [__meta_kubernetes_pod_node_name]
        target_label: node

  # 系统日志
  - job_name: system
    static_configs:
      - targets:
          - localhost
        labels:
          job: varlogs
          __path__: /var/log/*.log
    pipeline_stages:
      - regex:
          expression: '^(?P<timestamp>\w{3}\s+\d{1,2}\s+\d{2}:\d{2}:\d{2})'
      - timestamp:
          source: timestamp
          format: "Jan _2 15:04:05"

  # 应用日志
  - job_name: application
    static_configs:
      - targets:
          - localhost
        labels:
          job: app
          env: production
          __path__: /var/log/app/*.log
    pipeline_stages:
      - json:
          expressions:
            level: level
            message: msg
            timestamp: ts
            trace_id: trace_id
            service: service
      - labels:
          level:
          service:
      - timestamp:
          source: timestamp
          format: RFC3339Nano
```

## 标签设计最佳实践

```yaml
# 推荐的标签设计
labels:
  # 高基数字段（避免）
  bad_examples:
    - user_id
    - trace_id
    - request_id
    - session_id

  # 低基数字段（推荐）
  good_examples:
    - cluster        # 集群名
    - namespace      # K8s命名空间
    - service        # 服务名
    - pod            # Pod名
    - container      # 容器名
    - level          # 日志级别
    - environment    # 环境
    - version        # 版本
```

## LogQL查询语言

```logql
# 基础查询
{job="kubernetes-pods", namespace="production"}

# 过滤查询
{app="payment-service"} |= "ERROR" |~ "timeout|connection refused"

# 解析JSON日志
{job="app"}
| json
| level = "error"
| line_format "{{.timestamp}} {{.message}}"

# 解析正则
{job="nginx"}
| regexp "^(?P<ip>\S+) (?P<ident>\S+) (?P<user>\S+) \[(?P<timestamp>[\w:/]+\s[+\-]\d{4})\]"

# 聚合查询
sum(rate({job="app"} |= "error" [5m])) by (service)

# 统计错误率
sum(rate({job="app"} |= "error" [5m]))
/
sum(rate({job="app"}[5m]))

# TopK查询
topk(10, sum(rate({job="app"}[1m])) by (pod))

# 范围向量
{job="app"} |= "error"
| unwrap duration [1m]
```

## 告警规则

```yaml
# rules.yaml
groups:
  - name: loki-alerts
    interval: 1m
    rules:
      # 错误日志告警
      - alert: HighErrorRate
        expr: |
          sum(rate({job="app"} |= "ERROR" [5m])) by (service)
          > 0.1
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate in {{ $labels.service }}"
          description: "Error rate: {{ $value }} errors/sec"

      # 特定错误模式告警
      - alert: DatabaseConnectionError
        expr: |
          sum(rate({job="app"} |= "ERROR" |= "connection refused" [5m])) > 0
        for: 2m
        labels:
          severity: critical
          team: database
        annotations:
          summary: "Database connection errors detected"

      # 日志量突增告警
      - alert: LogVolumeSpike
        expr: |
          (
            sum(rate({job="app"}[5m]))
            /
            sum(rate({job="app"}[1h] offset 1h))
          ) > 5
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Unexpected log volume spike"
```

## 与Grafana集成

```yaml
# 数据源配置
datasources:
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    jsonData:
      maxLines: 10000
      # 从日志提取TraceID并链接到追踪
      derivedFields:
        - name: TraceID
          matcherRegex: "trace_id[=:]\\s*(\\w+)"
          url: 'http://jaeger:16686/trace/$${__value.raw}'
        - name: SpanID
          matcherRegex: "span_id[=:]\\s*(\\w+)"
          url: 'http://jaeger:16686/trace/$${__trace.id}/$${__value.raw}'
```

## 性能优化

```yaml
# 优化配置
# 1. 批量写入
client:
  batchwait: 1s
  batchsize: 1048576  # 1MB

# 2. 限制标签基数
limits_config:
  max_label_names_per_series: 30
  max_label_name_length: 1024
  max_label_value_length: 2048

# 3. 压缩配置
chunk_store_config:
  chunk_cache_config:
    embedded_cache:
      enabled: true
      max_size_mb: 512
      ttl: 24h
```

## 最佳实践

1. **标签设计**：只索引静态标签，避免高基数字段
2. **日志采样**：高流量场景启用采样，减少存储压力
3. **查询优化**：使用时间范围和标签过滤缩小查询范围
4. **多级存储**：热数据SSD，冷数据对象存储
5. **限流保护**：配置摄取限流，防止突发流量打垮系统
