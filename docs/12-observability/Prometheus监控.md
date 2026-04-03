# Prometheus监控

## 概述

Prometheus是由SoundCloud开源的监控告警系统，现为CNCF毕业项目。它采用Pull模式采集指标，支持多维数据模型和强大的查询语言PromQL，是云原生时代最受欢迎的监控解决方案。

## 核心架构

```
┌─────────────────────────────────────────────────────────────────┐
│                        Prometheus 架构                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   ┌──────────┐     scrape      ┌──────────────┐                │
│   │  Target  │◄────────────────│  Prometheus  │                │
│   │ (App A)  │   /metrics      │    Server    │                │
│   └──────────┘                 └──────┬───────┘                │
│                                       │                        │
│   ┌──────────┐     scrape            │  TSDB                    │
│   │  Target  │◄───────────────────────┤  Storage               │
│   │ (App B)  │   /metrics            │  (本地存储)              │
│   └──────────┘                       │                        │
│                                       │                        │
│   ┌──────────┐     scrape            │                        │
│   │ Exporter │◄──────────────────────┘                        │
│   │(Node/DB) │                                                │
│   └──────────┘                                                │
│                                                                 │
│   ┌──────────┐    query        ┌──────────────┐                │
│   │ Grafana  │◄───────────────►│    Alert     │                │
│   │(可视化)  │                 │   Manager    │                │
│   └──────────┘                 └──────┬───────┘                │
│                                       │ alerts                 │
│                                       ▼                        │
│                              ┌──────────────┐                │
│                              │  PagerDuty   │                │
│                              │  Slack/Email │                │
│                              └──────────────┘                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. Prometheus Server

负责指标抓取、存储和查询。

```yaml
# prometheus.yml 主配置
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: prod-eu-1
    replica: '{{.ExternalURL}}'

# 存储配置
storage:
  tsdb:
    retention.time: 15d
    retention.size: 50GB
    wal-compression: true

# 抓取配置
scrape_configs:
  # Kubernetes服务发现
  - job_name: 'kubernetes-pods'
    kubernetes_sd_configs:
      - role: pod
        namespaces:
          names:
            - default
            - production
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
        action: replace
        target_label: __metrics_path__
        regex: (.+)
      - source_labels: [__address__, __meta_kubernetes_pod_annotation_prometheus_io_port]
        action: replace
        regex: ([^:]+)(?::\d+)?;(\d+)
        replacement: $1:$2
        target_label: __address__

  # 静态目标
  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node1:9100', 'node2:9100', 'node3:9100']
    scrape_interval: 10s
    metrics_path: /metrics
```

### 2. Alertmanager

告警管理和路由分发。

```yaml
# alertmanager.yml
global:
  smtp_smarthost: 'smtp.example.com:587'
  smtp_from: 'alert@example.com'
  slack_api_url: '<slack_webhook_url>'

# 路由规则
route:
  group_by: ['alertname', 'severity', 'service']
  group_wait: 30s
  group_interval: 5m
  repeat_interval: 12h
  receiver: 'default'
  routes:
    - match:
        severity: critical
      receiver: 'pagerduty-critical'
      group_wait: 0s
      repeat_interval: 5m

    - match:
        severity: warning
      receiver: 'slack-warning'

    - match_re:
        service: (mysql|postgres|redis)
      receiver: 'database-team'

# 接收器配置
receivers:
  - name: 'default'
    email_configs:
      - to: 'ops@example.com'

  - name: 'pagerduty-critical'
    pagerduty_configs:
      - service_key: '<integration_key>'
        severity: critical

  - name: 'slack-warning'
    slack_configs:
      - channel: '#alerts'
        title: '⚠️ {{ .GroupLabels.alertname }}'
        text: '{{ range .Alerts }}{{ .Annotations.summary }}{{ end }}'

  - name: 'database-team'
    email_configs:
      - to: 'dba@example.com'

# 告警抑制
inhibit_rules:
  - source_match:
      severity: 'critical'
    target_match:
      severity: 'warning'
    equal: ['alertname', 'instance']
```

## 常用Exporter配置

### Node Exporter

```yaml
# node-exporter.service
ExecStart=/usr/local/bin/node_exporter \
  --path.procfs=/host/proc \
  --path.rootfs=/host/root \
  --path.sysfs=/host/sys \
  --collector.filesystem.mount-points-exclude='^/(sys|proc|dev|host|etc)($$|/)' \
  --collector.systemd \
  --collector.tcpstat \
  --collector.processes
```

### MySQL Exporter

```yaml
# mysql-exporter.yml
mysql:
  host: mysql-primary
  port: 3306
  user: exporter
  password: ${MYSQL_PASSWORD}

  # 只监控特定数据库
  target_databases:
    - ecommerce
    - payment

  # 自定义查询
  custom_queries:
    - name: mysql_order_count
      query: "SELECT COUNT(*) as count FROM orders WHERE created_at > NOW() - INTERVAL 1 HOUR"
      metrics:
        - count:
            usage: GAUGE
            description: "Orders in last hour"
```

## 告警规则示例

```yaml
# alert-rules.yml
groups:
  - name: node-alerts
    rules:
      # CPU使用率告警
      - alert: HighCPUUsage
        expr: |
          100 - (avg by(instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100) > 80
        for: 5m
        labels:
          severity: warning
          team: infrastructure
        annotations:
          summary: "High CPU usage on {{ $labels.instance }}"
          description: "CPU usage is above 80% (current: {{ $value }}%)"
          runbook_url: "https://wiki/runbooks/high-cpu"

      # 内存告警
      - alert: HighMemoryUsage
        expr: |
          (node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes)
          / node_memory_MemTotal_bytes * 100 > 85
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High memory usage on {{ $labels.instance }}"
          description: "Memory usage is above 85% (current: {{ $value }}%)"

  - name: application-alerts
    rules:
      # 错误率告警
      - alert: HighErrorRate
        expr: |
          sum(rate(http_requests_total{status=~"5.."}[5m]))
          / sum(rate(http_requests_total[5m])) * 100 > 5
        for: 2m
        labels:
          severity: critical
          service: "{{ $labels.service }}"
        annotations:
          summary: "High error rate for {{ $labels.service }}"
          description: "Error rate is {{ $value }}%"

      # P99延迟告警
      - alert: HighLatency
        expr: |
          histogram_quantile(0.99,
            sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
          ) > 0.5
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High P99 latency for {{ $labels.service }}"
          description: "P99 latency is {{ $value }}s"
```

## PromQL查询示例

```promql
# 查询指标
up{job="node-exporter"}

# 计算CPU使用率
100 - (avg by(instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)

# 计算内存使用率
(node_memory_MemTotal_bytes - node_memory_MemAvailable_bytes)
/ node_memory_MemTotal_bytes * 100

# 计算QPS
sum(rate(http_requests_total[5m])) by (service)

# 计算P99延迟
histogram_quantile(0.99,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)

# 错误率计算
sum(rate(http_requests_total{status=~"5.."}[5m]))
/ sum(rate(http_requests_total[5m])) * 100
```

## 高可用部署

```yaml
# Thanos Sidecar模式
thanos:
  sidecar:
    enabled: true
    objstore:
      type: s3
      config:
        bucket: prometheus-data
        endpoint: s3.amazonaws.com
        access_key: ${AWS_ACCESS_KEY}
        secret_key: ${AWS_SECRET_KEY}

  query:
    replicas: 2
    stores:
      - prometheus-0:10901
      - prometheus-1:10901
      - thanos-store:10901

  compact:
    retentionResolutionRaw: 30d
    retentionResolution5m: 120d
    retentionResolution1h: 1y
```

## 最佳实践

1. **标签设计**：避免高基数标签（如user_id、order_id）
2. **命名规范**：使用`domain_unit_suffix`格式，如`http_requests_total`
3. **采集间隔**：核心指标10s，一般指标15-30s
4. **存储规划**：本地SSD存储，保留15天左右历史
5. **告警分级**：critical、warning、info三级，避免告警疲劳
