# Kubernetes 调度器详解

## 1. 架构概述

Kubernetes 调度器（kube-scheduler）负责将新创建的 Pod 分配到合适的节点上运行。它根据资源需求、亲和性/反亲和性规则、数据本地性等多种约束条件做出调度决策。

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Kubernetes 调度架构                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    kube-scheduler                              │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │   Informer  │  │  Scheduling │  │      Binding        │   │ │
│  │  │   (监听)     │  │    Queue    │  │      (绑定)         │   │ │
│  │  │             │  │  (调度队列)  │  │                     │   │ │
│  │  │ 监听未调度  │  │             │  │ 将 Pod 绑定到 Node  │   │ │
│  │  │ Pod 事件    │  │ 优先级队列   │  │                     │   │ │
│  │  └──────┬──────┘  └──────┬──────┘  └─────────────────────┘   │ │
│  │         │                │                                     │ │
│  │         └────────────────┼────────────────┐                   │ │
│  │                          ▼                │                   │ │
│  │  ┌─────────────────────────────────────┐  │                   │ │
│  │  │           Scheduling Cycle           │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  1. PreFilter (过滤)                 │  │                   │ │
│  │  │     - 检查必要条件                    │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  2. Filter (筛选节点)                │  │                   │ │
│  │  │     - 资源充足性                      │  │                   │ │
│  │  │     - 亲和性规则                      │  │                   │ │
│  │  │     - 污点容忍                        │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  3. PostFilter (过滤后处理)          │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  4. Score (打分排序)                 │  │                   │ │
│  │  │     - 资源利用率                      │  │                   │ │
│  │  │     - 数据本地性                      │  │                   │ │
│  │  │     - 负载均衡                        │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  5. Reserve (预留资源)               │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  6. Permit (批准)                    │  │                   │ │
│  │  │                                      │  │                   │ │
│  │  │  7. Bind (绑定) ◀────────────────────┘                   │ │
│  │  │                                      │                     │ │
│  │  └──────────────────────────────────────┘                     │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. 调度流程详解

```
┌─────────────────────────────────────────────────────────────────────┐
│                  调度流程扩展点                                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Scheduling Framework 扩展点：                                      │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Queue Sort        ──▶ 对 Pod 进行排序                       │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  PreFilter         ──▶ 预过滤，检查必要条件                   │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  Filter            ──▶ 过滤不符合条件的节点                   │   │
│  │       │              (NodeResourcesFit, NodeAffinity,         │   │
│  │       │               PodAffinity, TaintsTolerations)         │   │
│  │       ▼                                                      │   │
│  │  PostFilter        ──▶ 过滤后处理，如抢占                     │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  PreScore          ──▶ 预打分准备                             │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  Score             ──▶ 对节点打分                             │   │
│  │       │              (NodeResourcesBalancedAllocation,        │   │
│  │       │               ImageLocality, InterPodAffinity)        │   │
│  │       ▼                                                      │   │
│  │  Reserve           ──▶ 预留资源                               │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  Permit            ──▶ 批准或等待                             │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  PreBind           ──▶ 绑定前准备                             │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  Bind              ──▶ 绑定 Pod 到节点                        │   │
│  │       │                                                      │   │
│  │       ▼                                                      │   │
│  │  PostBind          ──▶ 绑定后处理                             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Pod 调度配置

### 3.1 资源请求与限制

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: resource-demo
spec:
  containers:
  - name: app
    image: nginx
    resources:
      requests:
        memory: "64Mi"
        cpu: "250m"
      limits:
        memory: "128Mi"
        cpu: "500m"
```

### 3.2 节点亲和性

```yaml
# 硬亲和性（必须满足）
apiVersion: v1
kind: Pod
metadata:
  name: node-affinity-required
spec:
  affinity:
    nodeAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
        nodeSelectorTerms:
        - matchExpressions:
          - key: kubernetes.io/e2e-az-name
            operator: In
            values:
            - e2e-az1
            - e2e-az2
          - key: node-type
            operator: In
            values:
            - high-memory
  containers:
  - name: app
    image: nginx

---

# 软亲和性（偏好满足）
apiVersion: v1
kind: Pod
metadata:
  name: node-affinity-preferred
spec:
  affinity:
    nodeAffinity:
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 1
        preference:
          matchExpressions:
          - key: disktype
            operator: In
            values:
            - ssd
      - weight: 50
        preference:
          matchExpressions:
          - key: zone
            operator: In
            values:
            - zone1
  containers:
  - name: app
    image: nginx
```

### 3.3 Pod 亲和性与反亲和性

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: pod-affinity-demo
spec:
  affinity:
    # Pod 亲和性：与特定 Pod 运行在同一节点
    podAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
      - labelSelector:
          matchExpressions:
          - key: app
            operator: In
            values:
            - cache
        topologyKey: kubernetes.io/hostname

    # Pod 反亲和性：不与特定 Pod 运行在同一节点
    podAntiAffinity:
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 100
        podAffinityTerm:
          labelSelector:
            matchExpressions:
            - key: app
              operator: In
              values:
              - web
          topologyKey: kubernetes.io/hostname
  containers:
  - name: app
    image: nginx
```

### 3.4 污点与容忍

```yaml
# 给节点添加污点
# kubectl taint nodes node1 dedicated=special-user:NoSchedule

# Pod 容忍污点
apiVersion: v1
kind: Pod
metadata:
  name: toleration-demo
spec:
  tolerations:
  # 完全匹配污点
  - key: "dedicated"
    operator: "Equal"
    value: "special-user"
    effect: "NoSchedule"

  # 存在性匹配（不关心值）
  - key: "gpu"
    operator: "Exists"
    effect: "NoSchedule"

  # 容忍所有污点
  - operator: "Exists"

  containers:
  - name: app
    image: nginx
```

## 4. 调度策略

### 4.1 默认调度策略

```yaml
# kube-scheduler 配置文件
apiVersion: kubescheduler.config.k8s.io/v1beta3
kind: KubeSchedulerConfiguration
profiles:
  - schedulerName: default-scheduler
    plugins:
      score:
        disabled:
        - name: NodeResourcesLeastAllocated
        enabled:
        - name: NodeResourcesMostAllocated
          weight: 100
```

### 4.2 自定义调度器

```yaml
# 多调度器配置
apiVersion: kubescheduler.config.k8s.io/v1beta3
kind: KubeSchedulerConfiguration
profiles:
  - schedulerName: default-scheduler
    plugins:
      score:
        enabled:
        - name: NodeResourcesBalancedAllocation
          weight: 100

  - schedulerName: gpu-scheduler
    plugins:
      filter:
        enabled:
        - name: NodeResourcesFit
      score:
        enabled:
        - name: ImageLocality
          weight: 50
```

```yaml
# 使用自定义调度器
apiVersion: v1
kind: Pod
metadata:
  name: gpu-pod
spec:
  schedulerName: gpu-scheduler
  containers:
  - name: gpu-app
    image: gpu-app:latest
    resources:
      limits:
        nvidia.com/gpu: 1
```

## 5. 高级调度特性

### 5.1 Pod 拓扑分布约束

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-deployment
spec:
  replicas: 6
  selector:
    matchLabels:
      app: web
  template:
    metadata:
      labels:
        app: web
    spec:
      topologySpreadConstraints:
      # 跨 Zone 均匀分布
      - maxSkew: 1
        topologyKey: topology.kubernetes.io/zone
        whenUnsatisfiable: DoNotSchedule
        labelSelector:
          matchLabels:
            app: web

      # 跨 Node 均匀分布
      - maxSkew: 2
        topologyKey: kubernetes.io/hostname
        whenUnsatisfiable: ScheduleAnyway
        labelSelector:
          matchLabels:
            app: web

      containers:
      - name: web
        image: nginx
```

### 5.2 Pod 抢占与优先级

```yaml
# 定义 PriorityClass
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: high-priority
value: 1000000
globalDefault: false
description: "High priority class for critical workloads"

---
apiVersion: scheduling.k8s.io/v1
kind: PriorityClass
metadata:
  name: low-priority
value: 1000
globalDefault: false
description: "Low priority class for batch jobs"

---
# 使用 PriorityClass
apiVersion: v1
kind: Pod
metadata:
  name: critical-pod
spec:
  priorityClassName: high-priority
  containers:
  - name: app
    image: critical-app
```

### 5.3 调度门控（Scheduling Gates）

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: gated-pod
  schedulingGates:
  - name: example.com/custom-gate-1
  - name: example.com/custom-gate-2
spec:
  containers:
  - name: app
    image: nginx
```

```bash
# 移除调度门控，允许调度
kubectl patch pod gated-pod --type=merge \
  --patch='{"schedulingGates": [{"name": "example.com/custom-gate-2"}]}'
```

## 6. 调度器性能调优

```yaml
# kube-scheduler 启动参数
apiVersion: v1
kind: Pod
metadata:
  name: kube-scheduler
spec:
  containers:
  - name: kube-scheduler
    image: k8s.gcr.io/kube-scheduler:v1.28.0
    command:
    - kube-scheduler
    - --bind-address=0.0.0.0
    - --leader-elect=true
    - --leader-elect-lease-duration=15s
    - --leader-elect-renew-deadline=10s
    - --leader-elect-retry-period=2s
    - --profiling=false
    - --v=2
    - --config=/etc/kubernetes/scheduler-config.yaml
```

### 6.1 关键性能指标

```bash
# 调度延迟
kubectl get --raw /metrics | grep scheduler_e2e_scheduling_duration_seconds

# 调度速率
kubectl get --raw /metrics | grep scheduler_pod_scheduling_attempts

# 队列长度
kubectl get --raw /metrics | grep scheduler_pending_pods

# 调度失败次数
kubectl get --raw /metrics | grep scheduler_schedule_attempts_total
```

## 7. 与 YARN 对比

| 特性 | Kubernetes | YARN |
|------|------------|------|
| **调度粒度** | Pod | Container |
| **调度策略** | 丰富（亲和性、污点、拓扑分布） | 队列为主 |
| **扩展性** | Scheduler Framework 插件 | 有限 |
| **资源类型** | CPU、内存、GPU、存储等 | 主要是 CPU、内存 |
| **适用场景** | 云原生应用、微服务 | 大数据批处理 |
| **调度延迟** | 低（毫秒级） | 较高（秒级） |
| **多租户** | Namespace + RBAC | 队列 + ACL |

## 8. 最佳实践

1. **合理设置资源请求**：避免过度分配或分配不足
2. **使用亲和性规则**：优化性能和可用性
3. **设置 PodDisruptionBudget**：保证服务可用性
4. **使用拓扑分布约束**：实现高可用和故障隔离
5. **配置优先级和抢占**：保证关键工作负载
6. **监控调度指标**：及时发现和解决问题

## 9. 总结

Kubernetes 调度器的优势：

- **灵活性**：丰富的调度策略和扩展点
- **可扩展性**：Scheduler Framework 支持自定义插件
- **云原生**：深度集成 Kubernetes 生态
- **高性能**：高效的调度算法和低延迟

适用场景：

- 云原生应用部署
- 微服务架构
- AI/ML 工作负载
- 混合云/多云部署


---

## 相关主题

- [YARN资源管理](./YARN资源管理.md)
- [K8s调度策略](../../07-architecture/Kubernetes生态/K8s调度策略.md)
- [资源隔离技术](./资源隔离技术.md)

## 参考资源

- [K8s调度文档](https://kubernetes.io/docs/concepts/scheduling-eviction/)
