# SkyWalking APM

## 概述

Apache SkyWalking是由华为开源、捐献给Apache基金会的国产APM（应用性能监控）系统。它提供分布式追踪、服务网格遥测分析、度量聚合和可视化一体化解决方案，专为云原生和容器化架构设计，在Java生态和Service Mesh领域具有显著优势。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     Apache SkyWalking 架构                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌───────────┐          │
│   │Java Agent │  │Go Agent   │  │Node Agent │  │  Mesh     │          │
│   │(自动注入) │  │(自动注入) │  │(自动注入) │  │  Probe    │          │
│   └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └─────┬─────┘          │
│         │              │              │              │                 │
│         └──────────────┼──────────────┼──────────────┘                 │
│                        │              │                                 │
│                        ▼              ▼                                 │
│   ┌─────────────────────────────────────────────────────────────┐     │
│   │                      OAP Server                              │     │
│   │  ┌────────────┐  ┌────────────┐  ┌────────────┐              │     │
│   │  │  Receiver  │  │  Analyzer  │  │   Alarm    │              │     │
│   │  │  (接收器)   │  │  (分析器)   │  │  (告警)    │              │     │
│   │  │• gRPC      │  │• Trace     │  │• Rule      │              │     │
│   │  │• HTTP      │  │• Metrics   │  │• Webhook   │              │     │
│   │  │• Kafka     │  │• Log       │  │• Silence   │              │     │
│   │  └─────┬──────┘  └─────┬──────┘  └────────────┘              │     │
│   │        └───────────────┼──────────────────────────┐          │     │
│   │                        ▼                         │          │     │
│   │              ┌─────────────────┐                 │          │     │
│   │              │  Storage Layer  │◄────────────────┘          │     │
│   │              │  • Elasticsearch│                            │     │
│   │              │  • H2 (测试)     │                            │     │
│   │              │  • MySQL        │                            │     │
│   │              │  • TiDB         │                            │     │
│   │              │  • BanyanDB     │                            │     │
│   │              └─────────────────┘                            │     │
│   └─────────────────────────────────────────────────────────────┘     │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────┐     │
│   │                      UI Server                               │     │
│   │  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌─────────┐  │     │
│   │  │ Dashboard │  │  Topology │  │   Trace   │  │  Log    │  │     │
│   │  │  (仪表盘)  │  │  (拓扑图)  │  │  (追踪)   │  │ (日志)  │  │     │
│   │  └───────────┘  └───────────┘  └───────────┘  └─────────┘  │     │
│   └─────────────────────────────────────────────────────────────┘     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. OAP Server (Observability Analysis Platform)

```yaml
# application.yml
cluster:
  selector: ${SW_CLUSTER:kubernetes}
  kubernetes:
    namespace: ${SW_CLUSTER_K8S_NAMESPACE:skywalking}
    labelSelector: ${SW_CLUSTER_K8S_LABEL:app=skywalking-oap}
    uidEnvName: ${SW_CLUSTER_K8S_UID:SKYWALKING_OAP_UID}

core:
  selector: ${SW_CORE:default}
  default:
    # 数据TTL
    recordDataTTL: ${SW_CORE_RECORD_DATA_TTL:3}  # 天
    metricsDataTTL: ${SW_CORE_METRICS_DATA_TTL:7}  # 天

    # 存储配置
    enableDataKeeperExecutor: ${SW_CORE_ENABLE_DATA_KEEPER_EXECUTOR:true}
    dataKeeperExecutePeriod: ${SW_CORE_DATA_KEEPER_EXECUTE_PERIOD:5}  # 分钟

    # 采样配置
    sampleRate: ${SW_TRACE_SAMPLE_RATE:10000}  # 每10000条采样1条

    # 流处理
    syncThreads: ${SW_CORE_SYNC_THREADS:2}
    dataCarrierBufferSize: ${SW_CORE_DATA_CARRIER_BUFFER_SIZE:10000}

receiver-sharing-server:
  selector: ${SW_RECEIVER_SHARING_SERVER:default}
  default:
    # gRPC接收器
    grpc:
      host: ${SW_RECEIVER_GRPC_HOST:0.0.0.0}
      port: ${SW_RECEIVER_GRPC_PORT:11800}
      maxConcurrentCallsPerConnection: ${SW_RECEIVER_GRPC_MAX_CONCURRENT_CALL:0}
      maxMessageSize: ${SW_RECEIVER_GRPC_MAX_MESSAGE_SIZE:0}

    # HTTP接收器
    rest:
      host: ${SW_RECEIVER_REST_HOST:0.0.0.0}
      port: ${SW_RECEIVER_REST_PORT:12800}
      contextPath: ${SW_RECEIVER_REST_CONTEXT_PATH:/}
      maxThreads: ${SW_RECEIVER_REST_MAX_THREADS:200}
      acceptQueueSize: ${SW_RECEIVER_REST_QUEUE_SIZE:0}

receiver-otel:
  selector: ${SW_OTEL_RECEIVER:default}
  default:
    enabledHandlers: ${SW_OTEL_RECEIVER_ENABLED_HANDLERS:otlp-metrics,otlp-logs}

receiver-zipkin:
  selector: ${SW_RECEIVER_ZIPKIN:default}
  default:
    host: ${SW_RECEIVER_ZIPKIN_HOST:0.0.0.0}
    port: ${SW_RECEIVER_ZIPKIN_PORT:9412}
    contextPath: ${SW_RECEIVER_ZIPKIN_CONTEXT_PATH:/}

storage:
  selector: ${SW_STORAGE:elasticsearch}
  elasticsearch:
    namespace: ${SW_NAMESPACE:""}
    clusterNodes: ${SW_STORAGE_ES_CLUSTER_NODES:elasticsearch:9200}
    protocol: ${SW_STORAGE_ES_HTTP_PROTOCOL:http}
    trustStorePath: ${SW_STORAGE_ES_SSL_JKS_PATH:}
    trustStorePass: ${SW_STORAGE_ES_SSL_JKS_PASS:}
    user: ${SW_ES_USER:}
    password: ${SW_ES_PASSWORD:}

    # 索引配置
    indexShardsNumber: ${SW_STORAGE_ES_INDEX_SHARDS_NUMBER:2}
    indexReplicasNumber: ${SW_STORAGE_ES_INDEX_REPLICAS_NUMBER:0}

    # 批量配置
    bulkActions: ${SW_STORAGE_ES_BULK_ACTIONS:1000}
    bulkSize: ${SW_STORAGE_ES_BULK_SIZE:20}
    flushInterval: ${SW_STORAGE_ES_FLUSH_INTERVAL:10}
    concurrentRequests: ${SW_STORAGE_ES_CONCURRENT_REQUESTS:2}

    # 高级配置
    advanced: ${SW_STORAGE_ES_ADVANCED:""}

alarm:
  selector: ${SW_ALARM:default}
  default:
    # 告警规则文件
    rules:
      service_resp_time_rule:
        metrics-name: service_resp_time
        op: ">"
        threshold: 1000
        period: 10
        count: 3
        silence-period: 5
        message: "服务 {name} 响应时间超过1000ms"

      service_sla_rule:
        metrics-name: service_sla
        op: "<"
        threshold: 8000
        period: 10
        count: 2
        silence-period: 3
        message: "服务 {name} 成功率低于80%"

    # Webhook配置
    webhooks:
      - url: http://alertmanager:9093/webhook
        # 自定义Headers
        headers:
          Authorization: Bearer ${WEBHOOK_TOKEN}
```

### 2. Java Agent

```yaml
# agent.config
# 代理配置
agent.service_name=${SW_AGENT_NAME:Your_ApplicationName}
agent.namespace=${SW_AGENT_NAMESPACE:}

# 后端地址
collector.backend_service=${SW_AGENT_COLLECTOR_BACKEND_SERVICES:127.0.0.1:11800}

# 日志配置
logging.file_name=${SW_LOGGING_FILE_NAME:skywalking-api.log}
logging.level=${SW_LOGGING_LEVEL:INFO}
logging.dir=${SW_LOGGING_DIR:}
logging.max_file_size=${SW_LOGGING_MAX_FILE_SIZE:300102400}
logging.max_history_files=${SW_LOGGING_MAX_HISTORY_FILES:-1}

# 采样配置
agent.sample_n_per_3_secs=${SW_AGENT_SAMPLE:-1}
agent.trace.ignore_path=${SW_AGENT_TRACE_IGNORE_PATH:/api/health,/actuator/**}

# 插件配置
plugin.mount=${SW_MOUNT_FOLDERS:plugins,activations}
plugin.peer_max_length=${SW_PLUGIN_PEER_MAX_LENGTH:200}

# HTTP插件
plugin.httpclient.max_length_of_request_uri=${SW_PLUGIN_HTTPCLIENT_MAX_LENGTH:2048}
plugin.httpclient.collect_http_params=${SW_PLUGIN_HTTPCLIENT_COLLECT_HTTP_PARAMS:false}

# JDBC插件
plugin.jdbc.trace_sql_parameters=${SW_JDBC_TRACE_SQL_PARAMETERS:true}
plugin.jdbc.sql_parameters_max_length=${SW_JDBC_SQL_PARAMETERS_MAX_LENGTH:512}
plugin.jdbc.sql_body_max_length=${SW_JDBC_SQL_BODY_MAX_LENGTH:2048}

# Spring插件
plugin.springtransaction.simplify_transaction_definition_name=${SW_PLUGIN_SPRINGTRANSACTION_SIMPLIFY:true}

# Feign插件
plugin.feign.collect_request_body=${SW_PLUGIN_FEIGN_COLLECT_REQUEST_BODY:false}

# 自定义增强
plugin.custom.enhance_files=${SW_PLUGIN_CUSTOM_ENHANCE_FILES:}
```

### 3. 启动脚本

```bash
#!/bin/bash
# skywalking-agent.sh

# JVM参数配置
export SW_AGENT_NAME="order-service"
export SW_AGENT_NAMESPACE="production"
export SW_AGENT_COLLECTOR_BACKEND_SERVICES="skywalking-oap:11800"
export SW_AGENT_SAMPLE="10"  # 每10秒采样1条

# Java启动参数
JAVA_OPTS="
  -javaagent:/opt/skywalking-agent/skywalking-agent.jar
  -Dskywalking.agent.service_name=${SW_AGENT_NAME}
  -Dskywalking.agent.namespace=${SW_AGENT_NAMESPACE}
  -Dskywalking.collector.backend_service=${SW_AGENT_COLLECTOR_BACKEND_SERVICES}
  -Dskywalking.agent.sample_n_per_3_secs=${SW_AGENT_SAMPLE}
  -Dskywalking.plugin.jdbc.trace_sql_parameters=true
  -Dskywalking.plugin.httpclient.collect_http_params=true
"

java ${JAVA_OPTS} -jar app.jar
```

## UI配置

```yaml
# webapp.yml
server:
  port: 8080
  servlet:
    context-path: /

spring:
  cloud:
    gateway:
      routes:
        - id: oap-route
          uri: lb://oap
          predicates:
            - Path=/graphql/**
      discovery:
        locator:
          enabled: true

    # OAP服务发现
    discovery:
      kubernetes:
        enabled: true
        namespace: skywalking
        service-labels:
          app: skywalking-oap

skywalking:
  ui:
    # 默认时间范围
    default:
      duration:
        start: now-15m
        end: now
        step: MINUTE

    # 仪表盘配置
    dashboards:
      - name: "Service Dashboard"
        path: /dashboard/service
      - name: "Topology"
        path: /topology
      - name: "Trace"
        path: /trace
      - name: "Log"
        path: /log

    # 告警配置
    alarm:
      enabled: true
      webhook: http://alertmanager:9093/webhook
```

## 告警规则配置

```yaml
# alarm-settings.yml
rules:
  # 服务响应时间告警
  service_resp_time_rule:
    metrics-name: service_resp_time
    op: ">"
    threshold: 1000
    period: 10
    count: 3
    silence-period: 5
    message: "服务 {name} 响应时间超过1000ms，当前值: {current}ms"

  # 服务成功率告警
  service_sla_rule:
    metrics-name: service_sla
    op: "<"
    threshold: 8000
    period: 10
    count: 2
    silence-period: 3
    message: "服务 {name} 成功率低于80%，当前值: {current}%"

  # 服务实例告警
  service_instance_resp_time_rule:
    metrics-name: service_instance_resp_time
    op: ">"
    threshold: 1000
    period: 10
    count: 2
    silence-period: 5
    message: "实例 {name} 响应时间超过1000ms"

  # 数据库访问告警
  database_access_resp_time_rule:
    metrics-name: database_access_resp_time
    op: ">"
    threshold: 500
    period: 10
    count: 3
    silence-period: 5
    message: "数据库 {name} 访问响应时间超过500ms"

  # Endpoint告警
  endpoint_resp_time_rule:
    metrics-name: endpoint_resp_time
    op: ">"
    threshold: 1000
    period: 10
    count: 5
    silence-period: 5
    message: "端点 {name} 响应时间超过1000ms"

# Webhook模板
webhooks:
  - url: http://alertmanager:9093/webhook
    # 自定义Headers
    headers:
      Content-Type: application/json
      X-Custom-Header: skywalking
    # 超时配置
    timeout: 10s
```

## Kubernetes集成

```yaml
# skywalking-kubernetes.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: skywalking-oap
  namespace: skywalking
spec:
  replicas: 3
  selector:
    matchLabels:
      app: skywalking-oap
  template:
    metadata:
      labels:
        app: skywalking-oap
    spec:
      containers:
        - name: oap
          image: apache/skywalking-oap-server:latest
          ports:
            - containerPort: 11800
              name: grpc
            - containerPort: 12800
              name: rest
          env:
            - name: SW_CLUSTER
              value: kubernetes
            - name: SW_CLUSTER_K8S_NAMESPACE
              value: skywalking
            - name: SW_STORAGE
              value: elasticsearch
            - name: SW_STORAGE_ES_CLUSTER_NODES
              value: elasticsearch:9200
            - name: SW_CORE_RECORD_DATA_TTL
              value: "3"
            - name: SW_CORE_METRICS_DATA_TTL
              value: "7"
          resources:
            requests:
              memory: "2Gi"
              cpu: "1000m"
            limits:
              memory: "4Gi"
              cpu: "2000m"
          livenessProbe:
            tcpSocket:
              port: 12800
            initialDelaySeconds: 30
            periodSeconds: 10
          readinessProbe:
            httpGet:
              path: /healthcheck
              port: 12800
            initialDelaySeconds: 10
            periodSeconds: 5
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: skywalking-ui
  namespace: skywalking
spec:
  replicas: 1
  selector:
    matchLabels:
      app: skywalking-ui
  template:
    metadata:
      labels:
        app: skywalking-ui
    spec:
      containers:
        - name: ui
          image: apache/skywalking-ui:latest
          ports:
            - containerPort: 8080
          env:
            - name: SW_OAP_ADDRESS
              value: http://skywalking-oap:12800
```

## 最佳实践

1. **采样策略**：生产环境设置sample_n_per_3_secs，避免数据爆炸
2. **数据TTL**：合理设置recordDataTTL和metricsDataTTL，控制存储成本
3. **告警规则**：基于服务SLA和响应时间配置告警，避免误报
4. **Agent部署**：使用Init Container自动注入Agent到应用Pod
5. **标签规范**：统一agent.service_name命名规范，便于聚合分析
