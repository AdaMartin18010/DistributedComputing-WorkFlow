# SLO与SLI定义

## 概述

SLO（Service Level Objective，服务等级目标）和SLI（Service Level Indicator，服务等级指标）是站点可靠性工程（SRE）的核心概念。通过量化服务可靠性，SLO帮助团队在可靠性和开发速度之间找到平衡，避免过度追求"五个9"而忽视业务价值。

## 核心概念

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    SRE核心概念关系图                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                          SLA                                     │   │
│  │              (Service Level Agreement)                          │   │
│  │                     服务等级协议                                 │   │
│  │  • 对外承诺的可用性目标                                          │   │
│  │  • 违反时有业务后果(退款/赔偿)                                   │   │
│  │  • 通常比内部SLO更宽松                                           │   │
│  └────────────────────────┬────────────────────────────────────────┘   │
│                           │                                             │
│                           │ 基于                                         │
│                           ▼                                             │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                          SLO                                     │   │
│  │              (Service Level Objective)                          │   │
│  │                     服务等级目标                                 │   │
│  │  • 内部可靠性目标                                                │   │
│  │  • 基于SLI定义                                                   │   │
│  │  • 通常99.9% - 99.99%                                           │   │
│  │  • 错误预算驱动发布决策                                          │   │
│  └────────────────────────┬────────────────────────────────────────┘   │
│                           │                                             │
│                           │ 基于                                         │
│                           ▼                                             │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                          SLI                                     │   │
│  │              (Service Level Indicator)                          │   │
│  │                     服务等级指标                                 │   │
│  │  • 可量化的服务质量指标                                          │   │
│  │  • 如：请求成功率、延迟分布                                      │   │
│  │  • 客观、可测量                                                  │   │
│  └────────────────────────┬────────────────────────────────────────┘   │
│                           │                                             │
│                           │ 消耗                                         │
│                           ▼                                             │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                      Error Budget                                │   │
│  │                        错误预算                                  │   │
│  │  • 1 - SLO = 允许的错误率                                        │   │
│  │  • 用于权衡可靠性与创新速度                                      │   │
│  │  • 预算耗尽时冻结发布                                            │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## SLI定义规范

### 黄金信号SLI

```yaml
# golden-signals-sli.yaml
slis:
  # 1. 可用性 (Availability)
  availability:
    description: "服务成功响应的比例"
    formula: |
      SLI = (good_requests / total_requests) * 100%
      
      good_requests = 状态码为2xx的请求数
      total_requests = 所有请求数
    measurement:
      good: http_requests_total{status=~"2.."}
      total: http_requests_total
    target_slo: 99.9%
    
  # 2. 延迟 (Latency)
  latency:
    description: "请求响应时间分布"
    formula: |
      SLI = P90延迟 < 100ms 的比例
      或
      SLI = P99延迟 < 500ms 的比例
    measurement:
      metric: http_request_duration_seconds
      buckets: [0.01, 0.05, 0.1, 0.5, 1, 2, 5]
    target_slo:
      p90: 100ms
      p99: 500ms
    
  # 3. 质量 (Quality)
  quality:
    description: "返回正确结果的比例"
    formula: |
      SLI = (correct_results / total_results) * 100%
      
      correct_results = 返回正确数据的请求数
      total_results = 所有请求数
    measurement:
      good: results_verified{correct="true"}
      total: results_verified
    target_slo: 99.95%
    
  # 4. 吞吐量 (Throughput)
  throughput:
    description: "每秒处理的请求数"
    formula: |
      SLI = 当前QPS / 目标QPS
    measurement:
      current: rate(http_requests_total[5m])
      target: 10000  # 目标QPS
    target_slo: 100%
    
  # 5. 饱和度 (Saturation)
  saturation:
    description: "资源使用率"
    formula: |
      SLI = 已用资源 / 总资源
      
      常用资源:
      - CPU使用率
      - 内存使用率
      - 磁盘使用率
      - 连接数使用率
    measurement:
      cpu: 1 - rate(node_cpu_seconds_total{mode="idle"}[5m])
      memory: 1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)
      disk: 1 - (node_filesystem_avail_bytes / node_filesystem_size_bytes)
    target_slo: 80%  # 低于80%为健康
```

### 业务SLI定义

```yaml
# business-sli.yaml
slis:
  # 电商系统SLI
  ecommerce:
    - name: checkout_success_rate
      description: "结算成功率"
      formula: successful_checkouts / total_checkout_attempts
      target: 99.5%
      
    - name: payment_completion_time
      description: "支付完成时间"
      formula: 从点击支付到支付完成的P99时间
      target: "< 5s"
      
    - name: search_relevance
      description: "搜索结果相关性"
      formula: 用户点击搜索结果的比例
      target: "> 30%"
      
  # 视频流媒体SLI
  streaming:
    - name: rebuffer_ratio
      description: "重新缓冲率"
      formula: 发生缓冲的次数 / 总播放次数
      target: "< 1%"
      
    - name: video_start_time
      description: "视频启动时间"
      formula: 点击播放到开始播放的P99时间
      target: "< 2s"
      
    - name: playback_error_rate
      description: "播放错误率"
      formula: 播放失败次数 / 总播放尝试次数
      target: "< 0.1%"
```

## SLO配置示例

```yaml
# slo-definitions.yaml
slos:
  # API网关SLO
  api_gateway:
    service: api-gateway
    window: 30d  # 评估窗口
    
    objectives:
      - name: availability
        display_name: "可用性"
        description: "API网关成功响应的比例"
        sli: availability
        target: 0.999  # 99.9%
        burn_rate_alerts:
          fast:
            multiplier: 14.4
            window: 1h
            severity: critical
          slow:
            multiplier: 6
            window: 6h
            severity: warning
            
      - name: latency_p99
        display_name: "P99延迟"
        description: "99%的请求延迟低于500ms"
        sli: latency
        percentile: 0.99
        target: 0.5  # 500ms
        burn_rate_alerts:
          fast:
            multiplier: 14.4
            window: 1h
            
  # 支付服务SLO
  payment_service:
    service: payment-service
    window: 30d
    
    objectives:
      - name: availability
        target: 0.9999  # 四个9，支付服务要求更高
        
      - name: latency_p95
        display_name: "P95延迟"
        percentile: 0.95
        target: 0.2  # 200ms
        
      - name: success_rate
        display_name: "支付成功率"
        target: 0.9995  # 99.95%
        
  # 用户服务SLO
  user_service:
    service: user-service
    window: 30d
    
    objectives:
      - name: availability
        target: 0.99  # 两个9，相对宽松
        
      - name: latency_p90
        display_name: "P90延迟"
        percentile: 0.90
        target: 0.1  # 100ms
```

## 错误预算计算

```yaml
# error-budget.yaml
error_budget:
  # 错误预算计算公式
  formula: |
    错误预算 = 1 - SLO目标
    
    月度允许错误数 = 总请求数 × (1 - SLO)
    
    示例：
    - SLO: 99.9%
    - 月请求数: 1,000,000
    - 错误预算: 0.1%
    - 允许错误数: 1,000次
    
  # 不同SLO的错误预算对比
  comparison:
    - slo: "99% (2个9)"
      error_budget: "1%"
      monthly_downtime: "7.2小时"
      use_case: "内部工具、后台服务"
      
    - slo: "99.9% (3个9)"
      error_budget: "0.1%"
      monthly_downtime: "43分钟"
      use_case: "一般在线服务"
      
    - slo: "99.99% (4个9)"
      error_budget: "0.01%"
      monthly_downtime: "4.3分钟"
      use_case: "关键业务服务"
      
    - slo: "99.999% (5个9)"
      error_budget: "0.001%"
      monthly_downtime: "26秒"
      use_case: "金融交易、医疗系统"
      
  # 错误预算消耗告警
  burn_rate_alerts:
    # 快速消耗：1小时内消耗2%的月度预算
    fast_burn:
      condition: burn_rate > 14.4x
      window: 1h
      action: "立即响应，停止非紧急发布"
      
    # 中速消耗：6小时内消耗5%的月度预算
    medium_burn:
      condition: burn_rate > 6x
      window: 6h
      action: "本周暂停发布"
      
    # 慢速消耗：3天内消耗10%的月度预算
    slow_burn:
      condition: burn_rate > 2x
      window: 3d
      action: "关注趋势，评估发布策略"
```

## SLO实施架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     SLO监控架构                                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                     │
│  │  Prometheus │  │  Data Lake  │  │   APM       │                     │
│  │  (指标)      │  │  (日志)      │  │  (追踪)     │                     │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘                     │
│         │                │                │                             │
│         └────────────────┼────────────────┘                             │
│                          │                                              │
│                          ▼                                              │
│   ┌───────────────────────────────────────────────────────────────┐    │
│   │                    SLI计算引擎                                 │    │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │    │
│   │  │  SLI计算    │  │  SLO评估    │  │  错误预算计算        │   │    │
│   │  │ • 可用性    │  │ • 达成情况  │  │ • 消耗速率          │   │    │
│   │  │ • 延迟      │  │ • 趋势分析  │  │ • 剩余预算          │   │    │
│   │  │ • 错误率    │  │ • 对比历史  │  │ • 预测耗尽时间      │   │    │
│   │  └─────────────┘  └─────────────┘  └─────────────────────┘   │    │
│   └────────────────────────┬────────────────────────────────────┘    │
│                            │                                           │
│                            ▼                                           │
│   ┌───────────────────────────────────────────────────────────────┐   │
│   │                    SLO仪表板                                   │   │
│   │  • 实时SLO达成率                                              │   │
│   │  • 错误预算消耗趋势                                           │   │
│   │  • 告警事件时间线                                             │   │
│   │  • 服务间SLO对比                                              │   │
│   └────────────────────────┬────────────────────────────────────┘   │
│                            │                                           │
│                            ▼                                           │
│   ┌───────────────────────────────────────────────────────────────┐   │
│   │                    决策触发器                                  │   │
│   │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │   │
│   │  │ 发布冻结    │  │ 容量扩容    │  │  事故响应           │   │   │
│   │  │ 决策        │  │ 决策        │  │  升级               │   │   │
│   │  └─────────────┘  └─────────────┘  └─────────────────────┘   │   │
│   └───────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## Prometheus SLO规则

```yaml
# slo-recording-rules.yaml
groups:
  - name: slo_recording_rules
    interval: 5m
    rules:
      # 可用性SLI
      - record: slo:availability:ratio_rate5m
        expr: |
          sum(rate(http_requests_total{status=~"2.."}[5m]))
          /
          sum(rate(http_requests_total[5m]))
          
      - record: slo:availability:ratio_rate1h
        expr: |
          sum(rate(http_requests_total{status=~"2.."}[1h]))
          /
          sum(rate(http_requests_total[1h]))
          
      - record: slo:availability:ratio_rate1d
        expr: |
          sum(rate(http_requests_total{status=~"2.."}[1d]))
          /
          sum(rate(http_requests_total[1d]))
          
      # 延迟SLI (P99)
      - record: slo:latency:p99_5m
        expr: |
          histogram_quantile(0.99,
            sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
          )
          
      # 错误预算消耗
      - record: slo:error_budget:consumed
        expr: |
          1 - slo:availability:ratio_rate1d
          
      # 燃烧率
      - record: slo:burn_rate:1h
        expr: |
          slo:error_budget:consumed
          /
          ignoring(window) slo:error_budget:consumed offset 1h
```

## 最佳实践

1. **SLO要可测量**：SLI必须基于客观可量化的指标
2. **SLO要可达成**：不要过度承诺，留出缓冲空间
3. **从宽松开始**：初期SLO可以宽松，逐步收紧
4. **用户视角定义**：SLI应反映用户体验而非系统内部状态
5. **定期回顾**：每季度回顾SLO达成情况，调整不合理目标
