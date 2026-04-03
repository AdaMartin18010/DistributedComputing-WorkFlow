# Grafana可视化

## 概述

Grafana是开源的数据可视化和监控分析平台，支持多种数据源，提供丰富的可视化组件。作为可观测性体系的展示层，Grafana能够将指标、日志和追踪数据整合为直观的仪表盘，是运维团队日常监控和故障排查的核心工具。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                      Grafana 架构                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    Grafana Server                        │   │
│  │  ┌────────────┐  ┌────────────┐  ┌─────────────────┐   │   │
│  │  │ Dashboard  │  │   Panel    │  │   Alert Rules   │   │   │
│  │  │   Engine   │  │  Renderer  │  │   Scheduler     │   │   │
│  │  └────────────┘  └────────────┘  └─────────────────┘   │   │
│  └────────────┬────────────────────────────────────────────┘   │
│               │                                                 │
│  ┌────────────┼────────────────────────────────────────────┐   │
│  │            │           数据源层                          │   │
│  │  ┌─────────▼─────────┐  ┌──────────────┐  ┌──────────┐  │   │
│  │  │    Prometheus     │  │ Elasticsearch│  │   Loki   │  │   │
│  │  │    (指标)          │  │   (日志)      │  │  (日志)   │  │   │
│  │  └───────────────────┘  └──────────────┘  └──────────┘  │   │
│  │  ┌───────────────────┐  ┌──────────────┐  ┌──────────┐  │   │
│  │  │     InfluxDB      │  │   Tempo      │  │  MySQL   │  │   │
│  │  │                   │  │  (追踪)       │  │          │  │   │
│  │  └───────────────────┘  └──────────────┘  └──────────┘  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                      存储层                              │   │
│  │     SQLite/PostgreSQL/MySQL (元数据)                     │   │
│  │     S3/GCS/Azure Blob (Dashboard导出、图片)              │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## 核心配置

### 服务端配置

```yaml
# grafana.ini
[server]
protocol = http
http_port = 3000
domain = grafana.example.com
root_url = https://grafana.example.com

[database]
type = postgres
host = postgres:5432
name = grafana
user = grafana
password = ${DB_PASSWORD}

[security]
admin_user = admin
admin_password = ${ADMIN_PASSWORD}
secret_key = ${SECRET_KEY}
allow_embedding = true
cookie_secure = true
cookie_samesite = strict

[auth]
disable_login_form = false
disable_signout_menu = false

[auth.generic_oauth]
enabled = true
name = SSO
allow_sign_up = true
client_id = ${OAUTH_CLIENT_ID}
client_secret = ${OAUTH_CLIENT_SECRET}
scopes = openid profile email
token_url = https://auth.example.com/oauth/token
api_url = https://auth.example.com/oauth/userinfo

[alerting]
enabled = true
execute_alerts = true
error_or_timeout = 30s

[unified_alerting]
enabled = true

[rendering]
server_url = http://renderer:8081/render
callback_url = http://grafana:3000/

[panels]
disable_sanitize_html = false

[live]
max_connections = 1000
```

### 数据源配置

```yaml
# datasources/datasources.yml
apiVersion: 1

datasources:
  # Prometheus数据源
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
    editable: false
    jsonData:
      httpMethod: POST
      manageAlerts: true
      prometheusType: Prometheus
      prometheusVersion: 2.40.0
      cacheLevel: 'High'
      incrementalQuerying: true
      incrementalQueryOverlapWindow: 10m
      queryTimeout: 60s

  # Loki日志数据源
  - name: Loki
    type: loki
    access: proxy
    url: http://loki:3100
    editable: false
    jsonData:
      httpHeaderName1: X-Scope-OrgID
      maxLines: 10000
      derivedFields:
        - name: TraceID
          matcherRegex: "trace_id=(\\w+)"
          url: 'http://jaeger.example.com/trace/$${__value.raw}'
          urlDisplayLabel: '查看追踪'
        - name: SpanID
          matcherRegex: "span_id=(\\w+)"
          url: 'http://jaeger.example.com/trace/$${__trace.id}/$${__value.raw}'

  # Tempo追踪数据源
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    editable: false
    jsonData:
      tracesToLogs:
        datasourceUid: 'loki'
        tags: ['pod', 'namespace']
        mappedTags: [{ key: 'service.name', value: 'service' }]
        mapTagNamesEnabled: false
        spanStartTimeShift: '1h'
        spanEndTimeShift: '1h'
        filterByTraceID: false
        filterBySpanID: false
      tracesToMetrics:
        datasourceUid: 'prometheus'
        tags: [{ key: 'service.name', value: 'service' }]
      serviceMap:
        datasourceUid: 'prometheus'

  # Elasticsearch日志数据源
  - name: Elasticsearch
    type: elasticsearch
    access: proxy
    url: http://elasticsearch:9200
    editable: false
    jsonData:
      index: 'logstash-*'
      timeField: '@timestamp'
      esVersion: '8.0.0'
      maxConcurrentShardRequests: 5
      logMessageField: message
      logLevelField: level
```

## 仪表盘设计

### 黄金信号仪表盘

```json
{
  "dashboard": {
    "title": "服务黄金信号",
    "tags": ["sre", "golden-signals"],
    "timezone": "UTC",
    "schemaVersion": 36,
    "refresh": "30s",
    "panels": [
      {
        "id": 1,
        "title": "请求量 (QPS)",
        "type": "stat",
        "targets": [{
          "expr": "sum(rate(http_requests_total[5m]))",
          "legendFormat": "QPS"
        }],
        "fieldConfig": {
          "defaults": {
            "unit": "reqps",
            "thresholds": {
              "steps": [
                {"color": "green", "value": null},
                {"color": "yellow", "value": 1000},
                {"color": "red", "value": 5000}
              ]
            }
          }
        },
        "gridPos": {"h": 4, "w": 6, "x": 0, "y": 0}
      },
      {
        "id": 2,
        "title": "错误率",
        "type": "gauge",
        "targets": [{
          "expr": "sum(rate(http_requests_total{status=~\"5..\"}[5m])) / sum(rate(http_requests_total[5m])) * 100",
          "legendFormat": "Error Rate"
        }],
        "fieldConfig": {
          "defaults": {
            "unit": "percent",
            "min": 0,
            "max": 100,
            "thresholds": {
              "steps": [
                {"color": "green", "value": null},
                {"color": "yellow", "value": 1},
                {"color": "red", "value": 5}
              ]
            }
          }
        },
        "gridPos": {"h": 4, "w": 6, "x": 6, "y": 0}
      },
      {
        "id": 3,
        "title": "P99延迟",
        "type": "stat",
        "targets": [{
          "expr": "histogram_quantile(0.99, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
          "legendFormat": "P99"
        }],
        "fieldConfig": {
          "defaults": {
            "unit": "s",
            "thresholds": {
              "steps": [
                {"color": "green", "value": null},
                {"color": "yellow", "value": 0.5},
                {"color": "red", "value": 1}
              ]
            }
          }
        },
        "gridPos": {"h": 4, "w": 6, "x": 12, "y": 0}
      },
      {
        "id": 4,
        "title": "饱和度 (CPU)",
        "type": "gauge",
        "targets": [{
          "expr": "avg(100 - rate(node_cpu_seconds_total{mode=\"idle\"}[5m]) * 100)",
          "legendFormat": "CPU Usage"
        }],
        "fieldConfig": {
          "defaults": {
            "unit": "percent",
            "min": 0,
            "max": 100
          }
        },
        "gridPos": {"h": 4, "w": 6, "x": 18, "y": 0}
      },
      {
        "id": 5,
        "title": "延迟趋势",
        "type": "timeseries",
        "targets": [
          {
            "expr": "histogram_quantile(0.50, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
            "legendFormat": "P50"
          },
          {
            "expr": "histogram_quantile(0.90, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
            "legendFormat": "P90"
          },
          {
            "expr": "histogram_quantile(0.99, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))",
            "legendFormat": "P99"
          }
        ],
        "fieldConfig": {
          "defaults": {
            "unit": "s",
            "custom": {
              "drawStyle": "line",
              "lineInterpolation": "smooth",
              "fillOpacity": 10
            }
          }
        },
        "gridPos": {"h": 8, "w": 12, "x": 0, "y": 4}
      },
      {
        "id": 6,
        "title": "日志流",
        "type": "logs",
        "datasource": "Loki",
        "targets": [{
          "expr": "{service=\"$service\"} |= \"ERROR\"",
          "refId": "A"
        }],
        "gridPos": {"h": 8, "w": 12, "x": 12, "y": 4}
      }
    ]
  }
}
```

### 仪表盘子文件夹组织

```yaml
# 文件夹结构
folders:
  - name: "基础设施"
    dashboards:
      - node-exporter-full
      - kubernetes-cluster
      - network-monitoring

  - name: "应用监控"
    dashboards:
      - service-golden-signals
      - jvm-metrics
      - database-performance

  - name: "业务监控"
    dashboards:
      - e-commerce-overview
      - payment-success-rate
      - user-activity

  - name: "告警与SLO"
    dashboards:
      - alert-overview
      - slo-compliance
      - error-budget
```

## 告警规则配置

```yaml
# alerting/alert_rules.yml
apiVersion: 1

groups:
  - orgId: 1
    name: 'service_alerts'
    folder: '应用监控'
    interval: 60s
    rules:
      - uid: 'high-error-rate'
        title: '高错误率告警'
        condition: 'B'
        data:
          - refId: 'A'
            relativeTimeRange:
              from: 300
              to: 0
            datasourceUid: 'prometheus'
            model:
              expr: 'sum(rate(http_requests_total{status=~"5.."}[5m])) / sum(rate(http_requests_total[5m])) * 100'
              refId: 'A'
          - refId: 'B'
            relativeTimeRange:
              from: 0
              to: 0
            datasourceUid: '__expr__'
            model:
              type: 'threshold'
              expression: 'A'
              conditions:
                - evaluator:
                    type: 'gt'
                    params: [5]
        noDataState: 'NoData'
        execErrState: 'Error'
        annotations:
          summary: '服务 {{ $labels.service }} 错误率过高'
          description: '错误率: {{ $values.A }}%，已超过阈值5%'
        labels:
          severity: critical
          team: sre
```

## 变量与模板

```yaml
# 常用变量配置
variables:
  # 数据源变量
  - name: datasource
    type: datasource
    query: prometheus
    regex: '/^(?!default)/'

  # 服务选择
  - name: service
    type: query
    datasource: $datasource
    query: 'label_values(http_requests_total, service)'
    multi: true
    includeAll: true

  # 环境选择
  - name: environment
    type: custom
    query: 'prod,staging,dev'

  # Pod选择
  - name: pod
    type: query
    datasource: $datasource
    query: 'label_values(container_memory_usage_bytes{namespace="$namespace"}, pod)'
    refresh: 1

  # 时间范围快捷选择
  - name: interval
    type: interval
    query: '1m,5m,10m,30m,1h,6h,12h,1d,7d'
    current: '5m'
```

## 最佳实践

1. **一致性**：统一颜色编码（绿=正常，黄=警告，红=严重）
2. **分层设计**：概览→详细→原始数据三级结构
3. **交互关联**：日志中嵌入追踪链接，追踪关联指标
4. **性能优化**：限制返回数据点数量，使用Recording Rules
5. **权限管理**：按团队隔离文件夹，敏感数据限制访问
