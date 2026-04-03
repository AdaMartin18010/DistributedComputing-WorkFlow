# Prometheus 指标监控系统专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

Prometheus 是云原生时代最流行的开源监控和告警工具，由 Google 前员工在 SoundCloud 创建，采用拉取（Pull）模式采集指标，支持多维数据模型和强大的 PromQL 查询语言，已成为 Kubernetes 生态的监控标准。

---

## 一、核心概念

### 1.1 定义与原理

Prometheus 是一个开源的系统监控和告警工具包，具有以下核心特征：

- **多维数据模型**：时间序列由指标名称和键值对标签标识
- **灵活的查询语言**：PromQL 支持实时数据聚合和切片
- **去中心化架构**：不依赖分布式存储，单个服务器节点自治
- **HTTP 拉取模型**：通过 HTTP 协议主动拉取（Pull）指标数据
- **服务发现**：支持 Kubernetes、Consul 等服务自动发现

**核心工作原理**：

1. **数据采集**：Prometheus Server 周期性从 Exporter/应用拉取指标
2. **本地存储**：时序数据写入本地 TSDB（Time Series Database）
3. **规则计算**：Recording Rules 预聚合，Alerting Rules 生成告警
4. **告警通知**：Alertmanager 处理告警分组、去重、路由、静默
5. **可视化**：Grafana 通过 PromQL 查询展示监控图表

### 1.2 关键特性

- **多维度数据**：支持任意维度的标签切分和聚合
- **高效存储**：自定义 TSDB，高效压缩，单节点可支撑数百万时间序列
- **服务发现**：自动发现监控目标，适配动态云原生环境
- **强大告警**：丰富的告警规则，支持多级路由和静默
- **生态丰富**：大量 Exporter 覆盖各类中间件和基础设施

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 云原生监控 | ⭐⭐⭐⭐⭐ | Kubernetes、Docker 等容器化环境原生支持 |
| 微服务监控 | ⭐⭐⭐⭐⭐ | 服务发现自动适配动态扩缩容 |
| 基础设施监控 | ⭐⭐⭐⭐⭐ | 丰富的 Exporter 覆盖各类组件 |
| 业务指标监控 | ⭐⭐⭐⭐ | 客户端 SDK 支持自定义业务指标 |
| 日志监控 | ⭐⭐ | 非其强项，需配合 Loki/ELK |
| 分布式追踪 | ⭐ | 需配合 Jaeger/Tempo 等专用工具 |
| 长期历史数据 | ⭐⭐⭐ | 本地存储有限，需配合 Thanos/Cortex |

---

## 二、技术细节

### 2.1 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          Prometheus 架构                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │                    Prometheus Server                          │     │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │     │
│   │  │   Retrieval │  │    TSDB     │  │   PromQL Engine     │  │     │
│   │  │  (Scraper)  │  │  (Storage)  │  │  (Query Processor)  │  │     │
│   │  └──────┬──────┘  └─────────────┘  └─────────────────────┘  │     │
│   │         │                                                    │     │
│   │  ┌─────────────────────────────────────────────────────────┐ │     │
│   │  │               Rules Engine                               │ │     │
│   │  │  ┌─────────────┐    ┌─────────────┐                     │ │     │
│   │  │  │Recording    │    │ Alerting    │                     │ │     │
│   │  │  │Rules        │    │ Rules       │                     │ │     │
│   │  │  └─────────────┘    └──────┬──────┘                     │ │     │
│   │  └────────────────────────────┼─────────────────────────────┘ │     │
│   └───────────────────────────────┼───────────────────────────────┘     │
│                                   │                                     │
│                                   ▼                                     │
│                           ┌─────────────┐                              │
│                           │ Alertmanager │                             │
│                           │  (告警管理)  │                             │
│                           └──────┬──────┘                             │
│                                  │                                     │
│          ┌───────────────────────┼───────────────────────┐            │
│          │                       │                       │            │
│          ▼                       ▼                       ▼            │
│   ┌─────────────┐         ┌─────────────┐         ┌─────────────┐     │
│   │   Email     │         │  DingTalk   │         │   PagerDuty │     │
│   │   Slack     │         │   WeChat    │         │   Webhook   │     │
│   └─────────────┘         └─────────────┘         └─────────────┘     │
│                                                                         │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │                         数据采集层                            │     │
│   │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌────────┐ │     │
│   │  │ Node    │ │ MySQL   │ │ Redis   │ │ Custom  │ │App SDK │ │     │
│   │  │Exporter │ │Exporter │ │Exporter │ │Exporter │ │        │ │     │
│   │  └────┬────┘ └────┬────┘ └────┬────┘ └────┬────┘ └───┬────┘ │     │
│   │       └────────────┴───────────┴───────────┴──────────┘      │     │
│   └──────────────────────────────────────────────────────────────┘     │
│                                                                         │
│   ┌──────────────────────────────────────────────────────────────┐     │
│   │                         可视化层                              │     │
│   │                     ┌─────────────┐                         │     │
│   │                     │   Grafana   │                         │     │
│   │                     │  Dashboard  │                         │     │
│   │                     └─────────────┘                         │     │
│   └──────────────────────────────────────────────────────────────┘     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 指标类型（Metric Types）

#### Counter（计数器）

**特性**：单调递增，只能增加或在重启时归零

**适用场景**：请求总数、错误总数、任务完成数

```
# 示例
http_requests_total{method="GET", endpoint="/api/users"} 1024
http_requests_total{method="POST", endpoint="/api/users"} 256

# PromQL 使用
rate(http_requests_total[5m])  # 计算每秒增长率
increase(http_requests_total[1h])  # 计算1小时内增长量
```

#### Gauge（仪表盘）

**特性**：可增可减，表示瞬时值

**适用场景**：温度、内存使用量、并发连接数、队列长度

```
# 示例
node_memory_used_bytes{instance="server1"} 8589934592
go_goroutines{job="api-service"} 42

# PromQL 使用
node_memory_used_bytes / node_memory_total_bytes * 100  # 内存使用百分比
```

#### Histogram（直方图）

**特性**：采样观测值并分桶计数，包含以下数据：

- `_bucket{le="<bound>"}`：小于等于边界的样本数（累积）
- `_sum`：观测值总和
- `_count`：观测值总数

**适用场景**：请求延迟、响应大小等需要分位统计的数据

```
# 示例
http_request_duration_seconds_bucket{le="0.1"} 100
http_request_duration_seconds_bucket{le="0.5"} 800
http_request_duration_seconds_bucket{le="1.0"} 950
http_request_duration_seconds_bucket{le="+Inf"} 1000
http_request_duration_seconds_sum 520.5
http_request_duration_seconds_count 1000

# PromQL 使用
histogram_quantile(0.95,
  rate(http_request_duration_seconds_bucket[5m])
)  # 计算 95 分位延迟
```

#### Summary（摘要）

**特性**：类似 Histogram，但在客户端计算分位数，提供更精确的分位值

**适用场景**：需要精确分位值且无法服务端聚合的场景

```
# 示例
http_request_duration_seconds{quantile="0.5"} 0.0234
http_request_duration_seconds{quantile="0.9"} 0.1456
http_request_duration_seconds{quantile="0.99"} 0.5678
http_request_duration_seconds_sum 520.5
http_request_duration_seconds_count 1000
```

**Histogram vs Summary 选择建议**：

| 场景 | 推荐 | 原因 |
|------|------|------|
| 需要聚合多个实例数据 | Histogram | Summary 分位值不可聚合 |
| 需要精确分位值 | Summary | 客户端计算更精确 |
| 桶边界需要调整 | Histogram | 可灵活配置 bucket |
| 高基数场景 | Summary | Histogram bucket 会显著增加基数 |

### 2.3 PromQL 查询语言

#### 基础查询

```promql
# 瞬时向量 - 返回最新值
http_requests_total

# 范围向量 - 返回时间范围内的值
http_requests_total[5m]

# 向量选择器 - 标签过滤
http_requests_total{method="GET", status=~"2.."}
http_requests_total{job!="prometheus"}
```

#### 操作符

```promql
# 算术运算
node_memory_total_bytes - node_memory_free_bytes

# 比较运算
up == 0  # 筛选宕机实例

# 聚合操作
sum(rate(http_requests_total[5m])) by (job)
avg(http_request_duration_seconds) by (method)
max_over_time(node_cpu_usage[1h])

# 逻辑运算
http_requests_total{status=~"4.."} or http_requests_total{status=~"5.."}
```

#### 常用函数

| 函数 | 用途 | 示例 |
|------|------|------|
| `rate()` | 计算每秒变化率 | `rate(http_requests_total[5m])` |
| `irate()` | 瞬时变化率（更灵敏）| `irate(cpu_usage[5m])` |
| `increase()` | 计算时间范围内增长量 | `increase(errors_total[1h])` |
| `histogram_quantile()` | 从直方图计算分位数 | `histogram_quantile(0.99, rate(...))` |
| `predict_linear()` | 线性预测 | `predict_linear(disk_free[6h], 3600)` |
| `absent()` | 检查指标是否存在 | `absent(up{job="api"})` |

### 2.4 Alertmanager 告警

#### 告警规则配置

```yaml
# alert_rules.yml
groups:
  - name: api_alerts
    rules:
      # 高错误率告警
      - alert: HighErrorRate
        expr: |
          (
            sum(rate(http_requests_total{status=~"5.."}[5m]))
            /
            sum(rate(http_requests_total[5m]))
          ) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate on {{ $labels.job }}"
          description: "Error rate is {{ $value | humanizePercentage }}"

      # 服务宕机告警
      - alert: ServiceDown
        expr: up == 0
        for: 1m
        labels:
          severity: critical
        annotations:
          summary: "Service {{ $labels.job }} is down"

      # 磁盘空间不足预测
      - alert: DiskWillFillIn4Hours
        expr: predict_linear(node_filesystem_avail_bytes[1h], 4 * 3600) < 0
        for: 5m
        labels:
          severity: warning
```

#### Alertmanager 路由配置

```yaml
# alertmanager.yml
global:
  smtp_smarthost: 'smtp.example.com:587'
  smtp_from: 'alert@example.com'

route:
  receiver: 'default'
  group_by: ['alertname', 'severity']
  group_wait: 30s
  group_interval: 5m
  repeat_interval: 4h

  routes:
    # 严重告警立即通知
    - match:
        severity: critical
      receiver: 'pagerduty-critical'
      continue: true

    # API 团队告警
    - match_re:
        job: 'api-.*'
      receiver: 'api-team-slack'

    # 数据库告警
    - match_re:
        job: 'db-.*'
      receiver: 'dba-team-email'

receivers:
  - name: 'default'
    email_configs:
      - to: 'oncall@example.com'

  - name: 'pagerduty-critical'
    pagerduty_configs:
      - service_key: '<key>'

  - name: 'api-team-slack'
    slack_configs:
      - api_url: '<slack-webhook-url>'
        channel: '#api-alerts'

  - name: 'dba-team-email'
    email_configs:
      - to: 'dba@example.com'
```

### 2.5 Grafana 可视化

#### 常用面板类型

| 类型 | 用途 |
|------|------|
| Time Series | 时序趋势图（折线图）|
| Gauge | 仪表盘，显示当前值 |
| Bar Gauge | 条形图，适合多维度对比 |
| Table | 表格，展示明细数据 |
| Stat | 大数字展示 |
| Heatmap | 热力图，展示分布密度 |
| Pie Chart | 饼图，占比分析 |

#### PromQL 示例（Grafana 面板）

```promql
# 1. 请求 QPS
sum(rate(http_requests_total[5m]))

# 2. 错误率百分比
(
  sum(rate(http_requests_total{status=~"5.."}[5m]))
  /
  sum(rate(http_requests_total[5m]))
) * 100

# 3. 95 分位延迟
histogram_quantile(0.95,
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
)

# 4. Top 10 内存使用 Pod
topk(10,
  container_memory_working_set_bytes{container!=""}
)

# 5. CPU 使用率
(
  1 - avg(irate(node_cpu_seconds_total{mode="idle"}[5m])) by (instance)
) * 100
```

---

## 三、系统对比

### 3.1 Prometheus vs Zabbix vs InfluxDB 对比矩阵

| 维度 | Prometheus | Zabbix | InfluxDB |
|------|------------|--------|----------|
| **架构模式** | Pull（拉取）| Push（推送）| Push（推送）|
| **数据模型** | 多维标签 | 键值对 | 多维标签 |
| **查询语言** | PromQL（强大）| 有限 | Flux/InfluxQL |
| **服务发现** | 原生支持 K8s/Consul | 模板/自动发现 | 需配合 Telegraf |
| **告警能力** | Alertmanager 专业 | 内置告警 | Kapacitor/集成 |
| **水平扩展** | 需 Thanos/Cortex | 有限 | 企业版支持 |
| **存储方式** | 本地 TSDB | 关系型数据库 | 专用时序数据库 |
| **数据保留** | 默认 15 天 | 长期 | 可配置 |
| **云原生适配** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **学习曲线** | 中等 | 较陡 | 中等 |
| **社区生态** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **适用场景** | 云原生/容器 | 传统基础设施 | 物联网/高频写入 |

### 3.2 选型决策树

```
指标监控系统选型
├── 云原生环境（K8s/容器）？
│   ├── 是 → Prometheus（首选）
│   └── 否 → 传统物理机/虚拟机为主？
│       ├── 是 → 已有 Zabbix 基础架构？
│       │   ├── 是 → Zabbix（维护成本低）
│       │   └── 否 → 需要强大的告警能力？
│       │       ├── 是 → Prometheus
│       │       └── 否 → Zabbix（传统监控成熟）
│       └── 否 → 物联网/高频写入场景？
│           ├── 是 → InfluxDB（高吞吐写入）
│           └── 否 → 多维度分析需求强？
│               ├── 是 → Prometheus/PromQL
│               └── 否 → 综合评估存储成本
└── 需要长期历史数据存储？
    ├── 是 → Prometheus + Thanos/Cortex
    └── 否 → 单机 Prometheus 足够
```

### 3.3 性能基准参考

| 指标 | Prometheus | Zabbix | InfluxDB |
|------|------------|--------|----------|
| 单节点写入吞吐 | 100K-800K samples/s | 10K-50K values/s | 500K-1M points/s |
| 查询延迟（简单）| < 10ms | 10-100ms | < 10ms |
| 查询延迟（复杂）| 10-100ms | 100ms-1s | 10-100ms |
| 时间序列容量 | 数百万/节点 | 数十万 | 数百万 |
| 内存占用 | 适中 | 较高 | 较高 |

---

## 四、实践指南

### 4.1 部署配置

**Docker Compose 部署**：

```yaml
version: '3.8'
services:
  prometheus:
    image: prom/prometheus:v2.48.0
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - ./alert_rules.yml:/etc/prometheus/alert_rules.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--storage.tsdb.retention.time=30d'
      - '--web.enable-lifecycle'
    ports:
      - "9090:9090"

  alertmanager:
    image: prom/alertmanager:v0.26.0
    volumes:
      - ./alertmanager.yml:/etc/alertmanager/alertmanager.yml
    ports:
      - "9093:9093"

  grafana:
    image: grafana/grafana:10.2.0
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-dashboards:/etc/grafana/provisioning/dashboards
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin123

  node-exporter:
    image: prom/node-exporter:v1.7.0
    volumes:
      - /proc:/host/proc:ro
      - /sys:/host/sys:ro
      - /:/rootfs:ro
    command:
      - '--path.procfs=/host/proc'
      - '--path.rootfs=/rootfs'
      - '--path.sysfs=/host/sys'
    ports:
      - "9100:9100"

volumes:
  prometheus-data:
  grafana-data:
```

**Prometheus 配置示例**：

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'production'
    replica: '{{.ExternalURL}}'

# 告警规则文件
rule_files:
  - 'alert_rules.yml'

# 告警管理器
alerting:
  alertmanagers:
    - static_configs:
        - targets: ['alertmanager:9093']

# 采集配置
scrape_configs:
  # Prometheus 自身监控
  - job_name: 'prometheus'
    static_configs:
      - targets: ['localhost:9090']

  # 节点监控
  - job_name: 'node-exporter'
    static_configs:
      - targets: ['node-exporter:9100']
    relabel_configs:
      - source_labels: [__address__]
        target_label: instance

  # Kubernetes 服务发现
  - job_name: 'kubernetes-pods'
    kubernetes_sd_configs:
      - role: pod
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true

  # Consul 服务发现
  - job_name: 'consul-services'
    consul_sd_configs:
      - server: 'consul:8500'
        services: ['api', 'worker']
```

### 4.2 最佳实践

1. **指标命名规范**：

   ```
   # 基础格式
   <service>_<metric>_<unit>

   # 示例
   http_requests_total
   http_request_duration_seconds
   node_cpu_seconds_total
   database_connections_active
   ```

2. **标签设计原则**：
   - 控制基数：避免高变动值作为标签（如 user_id、trace_id）
   - 保持一致：同一指标的标签集保持一致
   - 语义清晰：使用 `environment` 而非 `env`

3. **告警设计（SRE 最佳实践）**：
   - **Symptom-based**：基于用户感知的症状（如错误率高）
   - **Page-worthy**：仅严重问题触发 paging
   - **Actionable**：每个告警都应有明确的处理步骤
   - **聚合分组**：使用 `group_by` 减少告警风暴

4. **容量规划**：

   ```
   # 内存估算公式
   内存(MB) =
     活跃时间序列数 × (标签平均长度/2 + 120)
     +
     查询峰值并发数 × 查询内存开销

   # 存储估算
   每日存储(GB) =
     每秒样本数 × 3600 × 24 × 压缩后字节数 / 1024^3
     ≈ 每秒样本数 × 0.0002 GB
   ```

5. **高可用方案**：
   - **联邦集群（Federation）**：分层聚合，边缘采集中心存储
   - **Thanos**：对象存储长期保留、全局查询视图
   - **Cortex/Mimir**：多租户、水平扩展、兼容 PromQL

### 4.3 常见问题

**Q1: Prometheus 内存占用过高怎么办？**
A:

- 减少采集目标或增加 scrape_interval
- 删除不必要的标签，控制指标基数
- 使用 Recording Rules 预聚合高频查询
- 考虑使用 Thanos/Cortex 分担查询压力

**Q2: 如何处理拉取模式无法触达的目标？**
A:

- 使用 Pushgateway 接收短生命周期任务指标
- 配置网络策略允许 Prometheus 访问目标
- 使用 Federation 或 Thanos Sidecar 穿透网络边界

**Q3: 长期存储方案如何选择？**
A:

| 方案 | 适用场景 |
|------|----------|
| Thanos | 需要全局查询视图、对象存储长期保存 |
| Cortex | 多租户 SaaS 场景、水平扩展需求 |
| VictoriaMetrics | 高性能、资源效率优先 |
| Mimir | Grafana Cloud、兼容 Cortex |
| InfluxDB | 已有 Influx 生态、特殊查询需求 |

---

## 五、与其他主题的关联

### 5.1 上游依赖

- [Kubernetes监控](../08-containerization/Kubernetes监控.md) - Prometheus 是 K8s 官方监控方案
- [服务发现](../07-microservices/服务注册与发现.md) - 基于服务发现自动发现监控目标
- [应用埋点](../12-observability/应用埋点规范.md) - 应用暴露 /metrics 端点

### 5.2 下游应用

- [告警通知系统](./告警通知系统.md) - Alertmanager 路由告警
- [容量规划](../11-devops/容量规划.md) - 基于指标数据进行容量预测
- [弹性伸缩](../07-microservices/弹性伸缩设计.md) - HPA 基于 Prometheus 指标

### 5.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| OpenMetrics | 标准规范 | Prometheus 指标格式的开放标准 |
| OTel Collector | 数据采集 | 可替代 Exporter，统一采集层 |
| Thanos/Cortex | 扩展方案 | 解决 Prometheus 扩展性和长期存储 |

---

## 六、参考资源

### 6.1 官方文档

1. [Prometheus 官方文档](https://prometheus.io/docs/introduction/overview/)
2. [PromQL 查询指南](https://prometheus.io/docs/prometheus/latest/querying/basics/)
3. [Alertmanager 配置](https://prometheus.io/docs/alerting/latest/configuration/)
4. [Grafana Prometheus 数据源](https://grafana.com/docs/grafana/latest/datasources/prometheus/)

### 6.2 开源项目

1. [prometheus-operator](https://github.com/prometheus-operator/prometheus-operator) - Kubernetes 部署
2. [kube-prometheus](https://github.com/prometheus-operator/kube-prometheus) - 完整的 K8s 监控栈
3. [awesome-prometheus-alerts](https://github.com/samber/awesome-prometheus-alerts) - 告警规则合集

### 6.3 学习资料

1. [Prometheus 权威指南](https://yunlzheng.gitbook.io/prometheus-book/) - 中文版
2. [Google SRE Book - Monitoring](https://sre.google/sre-book/monitoring-distributed-systems/)
3. [Prometheus Best Practices](https://prometheus.io/docs/practices/)

---

**维护者**：项目团队
**最后更新**：2026年
