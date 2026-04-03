# Knative 架构

## 一、概述

Knative 是一个基于 Kubernetes 的开源 Serverless 平台，它为在 Kubernetes 上运行无服务器工作负载提供了一整套组件。Knative 由 Google 主导开发，结合了 Kubernetes 的强大能力和 Serverless 的便捷性，使开发者能够在任何支持 Kubernetes 的基础设施上运行无服务器应用。

## 二、Knative 架构

### 2.1 整体架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Knative 架构                                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                       Client Layer                               │    │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ │    │
│  │  │   kn CLI    │  │   kubectl   │  │  CloudEvents SDK        │ │    │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘ │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                    │                                     │
│                                    ▼                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Knative Serving                               │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │   Service                                               │    │    │
│  │  │   └── Configuration ──► Revision 1 (v1)                │    │    │
│  │  │                    └──► Revision 2 (v2) ◄── Route     │    │    │
│  │  │                                             (100% /    │    │    │
│  │  │                                              50/50)    │    │    │
│  │  └─────────────────────────────────────────────────────────┘    │    │
│  │                                                                  │    │
│  │  功能:                                                           │    │
│  │  • 自动扩缩容 (0 ↔ N)                                             │    │
│  │  • 流量分割和金丝雀发布                                            │    │
│  │  • 版本管理                                                       │    │
│  │  • 自动网络端点                                                    │    │
│  └────────────────────────┬────────────────────────────────────────┘    │
│                           │                                              │
│  ┌────────────────────────┴────────────────────────────────────────┐    │
│  │                    Knative Eventing                              │    │
│  │  ┌───────────┐    ┌───────────┐    ┌───────────────────────┐   │    │
│  │  │  Sources  │───►│  Broker   │───►│      Triggers         │   │    │
│  │  │ (事件源)   │    │ (事件总线) │    │  ┌──────┐ ┌──────┐  │   │    │
│  │  │           │    │           │    │  │filter│ │sink  │  │   │    │
│  │  │ • GitHub  │    │           │    │  └──────┘ └──────┘  │   │    │
│  │  │ • Kafka   │    │           │    └───────────────────────┘   │    │
│  │  │ • S3      │    │           │                                │    │
│  │  │ • CronJob │    │           │                                │    │
│  │  └───────────┘    └───────────┘                                │    │
│  │                                                                  │    │
│  │  功能:                                                           │    │
│  │  • 事件驱动的无服务器架构                                          │    │
│  │  • 解耦事件生产者和消费者                                           │    │
│  │  • 多种事件源支持                                                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Knative Functions                             │    │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐           │    │
│  │  │    Go    │ │  Python  │ │  Node.js │ │   Java   │           │    │
│  │  │  func()  │ │  func()  │ │  func()  │ │  func()  │           │    │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘           │    │
│  │                                                                  │    │
│  │  功能:                                                           │    │
│  │  • 简化函数开发 (func CLI)                                        │    │
│  │  • 多语言运行时支持                                               │    │
│  │  • 本地开发到云端部署一键完成                                      │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Kubernetes Core                               │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐        │    │
│  │  │   Pod    │  │  Service │  │ Ingress  │  │   HPA    │        │    │
│  │  │          │  │          │  │ Controller│  │          │        │    │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘        │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Knative Serving 核心概念

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Knative Serving 资源关系                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                        Service                                   │    │
│  │  (顶层资源，管理整个应用生命周期)                                   │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │ apiVersion: serving.knative.dev/v1                      │    │    │
│  │  │ kind: Service                                           │    │    │
│  │  │ metadata:                                               │    │    │
│  │  │   name: hello                                           │    │    │
│  │  └───────────────────────┬─────────────────────────────────┘    │    │
│  │                          │                                        │    │
│  │                          │ manages                                │    │
│  │                          ▼                                        │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │                    Configuration                         │    │    │
│  │  │  (期望状态，定义 Pod 模板)                                │    │    │
│  │  └───────────────────────┬─────────────────────────────────┘    │    │
│  │                          │                                        │    │
│  │                          │ creates                                │    │
│  │                          ▼                                        │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │  Revision 1 (v1)        Revision 2 (v2)                 │    │    │
│  │  │  ┌───────────────┐     ┌───────────────┐                │    │    │
│  │  │  │   Deployment  │     │   Deployment  │                │    │    │
│  │  │  │   ReplicaSet  │     │   ReplicaSet  │                │    │    │
│  │  │  │   Pod         │     │   Pod         │                │    │    │
│  │  │  └───────────────┘     └───────────────┘                │    │    │
│  │  │         ▲                    ▲                          │    │    │
│  │  └─────────┼────────────────────┼──────────────────────────┘    │    │
│  │            │                    │                               │    │
│  │            └────────────────────┘                               │    │
│  │                      routes to                                  │    │
│  │            ┌─────────────────────────────────────────┐          │    │
│  │            │              Route                       │          │    │
│  │            │  hello.default.example.com              │          │    │
│  │            │  • v1: 90%                              │          │    │
│  │            │  • v2: 10% (金丝雀)                      │          │    │
│  │            └─────────────────────────────────────────┘          │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## 三、Knative Serving 配置

### 3.1 基础 Service

```yaml
# hello-service.yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: hello
  namespace: default
spec:
  template:
    metadata:
      name: hello-revision-1
      annotations:
        # 自动扩缩容配置
        autoscaling.knative.dev/minScale: "0"      # 最小 0 实例（缩容到零）
        autoscaling.knative.dev/maxScale: "10"     # 最大 10 实例
        autoscaling.knative.dev/targetConcurrency: "100"  # 每 Pod 100 并发
        # 稳定性窗口
        autoscaling.knative.dev/window: "60s"
        # 响应时间目标
        autoscaling.knative.dev/metric: "concurrency"
        autoscaling.knative.dev/targetUtilizationPercentage: "70"
    spec:
      containerConcurrency: 1000  # 单容器最大并发
      timeoutSeconds: 300         # 请求超时时间
      responseStartTimeoutSeconds: 60
      idleTimeoutSeconds: 300     # 空闲超时
      # Pod 配置
      serviceAccountName: hello-sa
      containers:
      - image: gcr.io/knative-samples/helloworld-go
        ports:
        - containerPort: 8080
        env:
        - name: TARGET
          value: "World"
        resources:
          requests:
            cpu: "100m"
            memory: "128Mi"
          limits:
            cpu: "500m"
            memory: "256Mi"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 0
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 0
          periodSeconds: 5
      # 节点亲和性
      affinity:
        nodeAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            preference:
              matchExpressions:
              - key: knative.dev/capacity
                operator: In
                values:
                - free
```

### 3.2 流量管理

```yaml
# traffic-split.yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: hello
  namespace: default
spec:
  template:
    metadata:
      name: hello-v2  # 新版本
    spec:
      containers:
      - image: gcr.io/knative-samples/helloworld-go:v2
        env:
        - name: TARGET
          value: "World v2"
  # 流量分配
  traffic:
  - tag: current
    revisionName: hello-v1
    percent: 90
  - tag: candidate
    revisionName: hello-v2
    percent: 10
  - tag: latest
    latestRevision: true
    percent: 0  # 不直接接收流量，仅用于测试

# 生成的 URL:
# current-hello.default.example.com    → v1 (90%)
# candidate-hello.default.example.com  → v2 (10%)
# latest-hello.default.example.com     → v2 (测试用)
# hello.default.example.com            → 按比例分流
```

### 3.3 私有服务

```yaml
# private-service.yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: internal-api
  namespace: backend
  labels:
    networking.knative.dev/visibility: cluster-local  # 仅集群内访问
spec:
  template:
    spec:
      containers:
      - image: internal-api:latest

# 访问地址变为:
# internal-api.backend.svc.cluster.local
```

## 四、Knative Eventing

### 4.1 事件源示例

```yaml
# cronjob-source.yaml
apiVersion: sources.knative.dev/v1
kind: PingSource
metadata:
  name: hourly-job
spec:
  schedule: "0 * * * *"  # 每小时执行
  data: '{"message": "Hello from Cron!"}'
  sink:
    ref:
      apiVersion: serving.knative.dev/v1
      kind: Service
      name: event-processor

---
# github-source.yaml
apiVersion: sources.knative.dev/v1
kind: GitHubSource
metadata:
  name: github-webhook
spec:
  eventTypes:
    - push
    - pull_request
  ownerAndRepository: myorg/myrepo
  accessToken:
    secretKeyRef:
      name: github-secret
      key: accessToken
  secretToken:
    secretKeyRef:
      name: github-secret
      key: secretToken
  sink:
    ref:
      apiVersion: serving.knative.dev/v1
      kind: Service
      name: github-handler

---
# kafka-source.yaml
apiVersion: sources.knative.dev/v1beta1
kind: KafkaSource
metadata:
  name: kafka-consumer
spec:
  consumerGroup: knative-group
  bootstrapServers:
    - my-cluster-kafka-bootstrap:9092
  topics:
    - my-topic
  sink:
    ref:
      apiVersion: serving.knative.dev/v1
      kind: Service
      name: kafka-processor
```

### 4.2 Broker 和 Trigger

```yaml
# broker.yaml
apiVersion: eventing.knative.dev/v1
kind: Broker
metadata:
  name: default
  namespace: default
  annotations:
    eventing.knative.dev/broker.class: MTChannelBasedBroker
spec:
  config:
    apiVersion: v1
    kind: ConfigMap
    name: config-br-default-channel
    namespace: knative-eventing

---
# trigger.yaml
apiVersion: eventing.knative.dev/v1
kind: Trigger
metadata:
  name: order-trigger
  namespace: default
spec:
  broker: default
  filter:
    attributes:
      type: com.example.order.created
      source: order-service
  subscriber:
    ref:
      apiVersion: serving.knative.dev/v1
      kind: Service
      name: order-processor

---
# 多 trigger 示例
apiVersion: eventing.knative.dev/v1
kind: Trigger
metadata:
  name: notification-trigger
spec:
  broker: default
  filter:
    attributes:
      type: com.example.order.created
  subscriber:
    ref:
      apiVersion: serving.knative.dev/v1
      kind: Service
      name: notification-service
```

## 五、Knative Functions

### 5.1 创建函数

```bash
# 安装 func CLI
brew install func

# 创建 Go 函数
func create -l go hello-function
cd hello-function

# 项目结构
# hello-function/
# ├── func.yaml          # 函数配置
# ├── go.mod
# ├── go.sum
# ├── handle.go          # 处理函数
# ├── handle_test.go
# └── README.md
```

### 5.2 函数代码示例

```go
// handle.go
package function

import (
	"context"
	"fmt"
	"net/http"

	"github.com/cloudevents/sdk-go/v2/event"
)

// Handle HTTP 请求
func Handle(ctx context.Context, res http.ResponseWriter, req *http.Request) {
	name := req.URL.Query().Get("name")
	if name == "" {
		name = "World"
	}
	fmt.Fprintf(res, "Hello, %s!\n", name)
}

// HandleCloudEvent 处理 CloudEvent
func HandleCloudEvent(ctx context.Context, e event.Event) (*event.Event, error) {
	// 处理事件
	fmt.Printf("Received event: %s\n", e.Type())
	
	// 返回响应事件
	response := event.New()
	response.SetSource("hello-function")
	response.SetType("com.example.response")
	response.SetData(e.DataContentType(), map[string]string{
		"status": "processed",
	})
	
	return &response, nil
}
```

### 5.3 函数配置

```yaml
# func.yaml
specVersion: 0.35.0
name: hello-function
runtime: go
registry: docker.io/username
image: docker.io/username/hello-function:latest
created: 2024-01-15T10:00:00.000000+00:00
build:
  buildpacks: {}
  builder: pack
  buildEnvs: []
run:
  volumes: []
  envs: []
deploy:
  namespace: default
  annotations:
    autoscaling.knative.dev/minScale: "0"
    autoscaling.knative.dev/maxScale: "5"
  options: {}
  labels: []
  healthEndpoints:
    liveness: /health/liveness
    readiness: /health/readiness
```

### 5.4 部署函数

```bash
# 本地运行
func run

# 构建镜像
func build --registry docker.io/username

# 部署到 Knative
func deploy

# 查看函数
func list

# 调用函数
func invoke --data '{"name": "Knative"}'

# 或者使用 curl
curl $(kn service describe hello-function -o url)
```

## 六、常用命令

```bash
# ========== Knative CLI (kn) ==========
# 安装 kn
brew install kn

# 查看服务
kn service list
kn service list -A

# 创建服务
kn service create hello \
  --image gcr.io/knative-samples/helloworld-go \
  --env TARGET=World

# 更新服务
kn service update hello --env TARGET=Knative

# 删除服务
kn service delete hello

# 查看服务详情
kn service describe hello

# 查看修订版本
kn revision list

# 流量管理
kn service update hello \
  --traffic hello-v1=90 \
  --traffic hello-v2=10

# ========== Knative Functions (func) ==========
# 创建函数
func create -l python myfunc

# 本地运行
func run

# 构建
func build

# 部署
func deploy

# 调用
func invoke

# 删除
func delete

# ========== 自动扩缩容配置 ==========
# 配置 min/max 规模
kn service update hello \
  --annotation autoscaling.knative.dev/minScale=0 \
  --annotation autoscaling.knative.dev/maxScale=10

# 配置并发
kn service update hello \
  --annotation autoscaling.knative.dev/targetConcurrency=50

# ========== 调试 ==========
# 查看 Pod
kubectl get pods -n default

# 查看 Knative 控制器
kubectl get pods -n knative-serving

# 查看自动扩缩容器
kubectl get pods -n knative-serving -l app=autoscaler

# 查看事件
kubectl get events -n default --sort-by='.lastTimestamp'
```

## 七、总结

Knative 提供了完整的 Serverless 解决方案：

1. **Knative Serving**：无服务器容器部署，自动扩缩容到零
2. **Knative Eventing**：事件驱动的架构，支持多种事件源
3. **Knative Functions**：简化的函数开发体验

优势：
- 开源、云厂商无关
- 基于 Kubernetes，易于集成
- 自动扩缩容到零，节省成本
- 流量管理和版本控制
- 丰富的生态系统

适用场景：
- 事件驱动的应用
- 可变工作负载
- 微服务架构
- 需要快速扩缩容的场景
- 希望避免供应商锁定的 Serverless 需求
