# K8s 调度策略

## 一、概述

Kubernetes 调度器（kube-scheduler）负责将 Pod 分配到最合适的节点上运行。调度决策基于多种因素，包括资源需求、硬件/软件约束、亲和性/反亲和性规则、数据局部性等。理解调度策略对于优化集群资源利用率、提升应用性能和确保高可用性至关重要。

## 二、调度流程

### 2.1 调度器架构

```
┌─────────────────────────────────────────────────────────────┐
│                  Kubernetes 调度器架构                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  1. 调度队列 (Scheduling Queue)                        │  │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────────┐  │  │
│  │  │Active Queue │ │Backoff Queue│ │Unschedulable    │  │  │
│  │  │  (待调度)   │ │  (失败重试)  │ │     Queue       │  │  │
│  │  └─────────────┘ └─────────────┘ └─────────────────┘  │  │
│  │       │                │                │             │  │
│  │       └────────────────┴────────────────┘             │  │
│  │                          │                            │  │
│  │                          ▼                            │  │
│  │  ┌─────────────────────────────────────────────────┐  │  │
│  │  │         Pop (取出待调度 Pod)                      │  │  │
│  │  └─────────────────────────────────────────────────┘  │  │
│  └──────────────────────────┬────────────────────────────┘  │
│                             │                                │
│                             ▼                                │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  2. 预选阶段 (Filtering/Predicates)                    │  │
│  │  ┌─────────────────────────────────────────────────┐  │  │
│  │  │ • PodFitsResources    - 资源是否充足              │  │  │
│  │  │ • PodFitsHost         - 主机名匹配                │  │  │
│  │  │ • PodFitsHostPorts    - 端口是否冲突              │  │  │
│  │  │ • MatchNodeSelector   - 节点选择器匹配            │  │  │
│  │  │ • MatchInterPodAffinity - Pod间亲和性            │  │  │
│  │  │ • NoDiskConflict      - 存储冲突检查              │  │  │
│  │  │ • PodToleratesNodeTaints - 污点容忍              │  │  │
│  │  │ • CheckNodeCondition  - 节点状态检查              │  │  │
│  │  └─────────────────────────────────────────────────┘  │  │
│  │  输出: 可用节点列表                                      │  │
│  └──────────────────────────┬────────────────────────────┘  │
│                             │                                │
│                             ▼                                │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  3. 优选阶段 (Scoring/Priorities)                      │  │
│  │  ┌─────────────────────────────────────────────────┐  │  │
│  │  │ • LeastAllocatedPriority   - 资源闲置率          │  │  │
│  │  │ • BalancedAllocation       - 资源平衡度          │  │  │
│  │  │ • ImageLocalityPriority    - 镜像本地性          │  │  │
│  │  │ • NodeAffinityPriority     - 节点亲和性          │  │  │
│  │  │ • TaintTolerationPriority  - 污点容忍度          │  │  │
│  │  │ • InterPodAffinityPriority - Pod间亲和性         │  │  │
│  │  │ • NodeLabelsPriority       - 节点标签匹配        │  │  │
│  │  └─────────────────────────────────────────────────┘  │  │
│  │  输出: 节点评分排序                                      │  │
│  └──────────────────────────┬────────────────────────────┘  │
│                             │                                │
│                             ▼                                │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  4. 绑定阶段 (Binding)                                 │  │
│  │     将 Pod 与选定的节点绑定                              │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 调度队列详解

```yaml
# 调度队列配置
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
profiles:
- schedulerName: default-scheduler
  queueSort:
    enabled:
    - name: PrioritySort  # 按优先级排序
  preEnqueue:
    enabled:
    - name: SchedulingGates
    - name: ClusterEventBackoff
  plugins:
    # 入队限制插件
    permit:
      enabled:
      - name: NodeResourcesFit
  # 调度队列参数
  podInitialBackoffSeconds: 1      # 初始退避时间
  podMaxBackoffSeconds: 10         # 最大退避时间
```

## 三、节点选择器

### 3.1 nodeSelector

```yaml
# 基本节点选择器
apiVersion: v1
kind: Pod
metadata:
  name: nginx-gpu
spec:
  containers:
  - name: nginx
    image: nginx:alpine
  nodeSelector:
    accelerator: nvidia-tesla-v100
    environment: production

---
# 给节点添加标签
kubectl label nodes node-1 accelerator=nvidia-tesla-v100
kubectl label nodes node-1 environment=production
kubectl label nodes node-1 disktype=ssd

# 查看节点标签
kubectl get nodes --show-labels
```

### 3.2 节点亲和性（Node Affinity）

```yaml
# 软亲和性（preferred）- 尽量满足
apiVersion: v1
kind: Pod
metadata:
  name: nginx-preferred
spec:
  containers:
  - name: nginx
    image: nginx:alpine
  affinity:
    nodeAffinity:
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 100
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
            - zone-a

---
# 硬亲和性（required）- 必须满足
apiVersion: v1
kind: Pod
metadata:
  name: nginx-required
spec:
  containers:
  - name: nginx
    image: nginx:alpine
  affinity:
    nodeAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
        nodeSelectorTerms:
        - matchExpressions:
          - key: kubernetes.io/os
            operator: In
            values:
            - linux
          - key: kubernetes.io/arch
            operator: In
            values:
            - amd64
        - matchExpressions:
          - key: custom-label
            operator: Exists

---
# 复杂示例：数据库 Pod 调度到特定硬件
apiVersion: v1
kind: Pod
metadata:
  name: postgres-ha
spec:
  containers:
  - name: postgres
    image: postgres:15
    resources:
      requests:
        memory: "8Gi"
        cpu: "4"
  affinity:
    nodeAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
        nodeSelectorTerms:
        - matchExpressions:
          - key: node-type
            operator: In
            values:
            - database
          - key: storage-type
            operator: In
            values:
            - nvme-ssd
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 100
        preference:
          matchExpressions:
          - key: rack
            operator: In
            values:
            - rack-1
```

## 四、Pod 亲和性与反亲和性

### 4.1 Pod 亲和性（Pod Affinity）

```yaml
# 将 Pod 调度到同一拓扑域
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-cache
spec:
  replicas: 3
  selector:
    matchLabels:
      app: web
  template:
    metadata:
      labels:
        app: web
    spec:
      containers:
      - name: nginx
        image: nginx:alpine
      affinity:
        podAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
          - labelSelector:
              matchExpressions:
              - key: app
                operator: In
                values:
                - cache
            topologyKey: kubernetes.io/hostname  # 同一节点

---
# 将 Pod 调度到同一可用区
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-tier
spec:
  replicas: 5
  selector:
    matchLabels:
      tier: frontend
  template:
    metadata:
      labels:
        tier: frontend
    spec:
      containers:
      - name: app
        image: myapp:v1
      affinity:
        podAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: tier
                  operator: In
                  values:
                  - backend
              topologyKey: topology.kubernetes.io/zone
```

### 4.2 Pod 反亲和性（Pod Anti-Affinity）

```yaml
# 分散 Pod 到不同节点（高可用）
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-ha
spec:
  replicas: 3
  selector:
    matchLabels:
      app: web
  template:
    metadata:
      labels:
        app: web
    spec:
      containers:
      - name: nginx
        image: nginx:alpine
      affinity:
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
          - labelSelector:
              matchExpressions:
              - key: app
                operator: In
                values:
                - web
            topologyKey: kubernetes.io/hostname

---
# StatefulSet 反亲和性（Pod 级别）
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: redis-cluster
spec:
  serviceName: redis
  replicas: 6
  selector:
    matchLabels:
      app: redis
  template:
    metadata:
      labels:
        app: redis
    spec:
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - redis
              topologyKey: kubernetes.io/hostname
          - weight: 50
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - redis
              topologyKey: topology.kubernetes.io/zone
      containers:
      - name: redis
        image: redis:7-alpine

---
# 复杂反亲和性示例
apiVersion: apps/v1
kind: Deployment
metadata:
  name: multi-tier-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: web
      tier: frontend
  template:
    metadata:
      labels:
        app: web
        tier: frontend
    spec:
      affinity:
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
          # 避免与前端 Pod 同节点
          - labelSelector:
              matchExpressions:
              - key: tier
                operator: In
                values:
                - frontend
            topologyKey: kubernetes.io/hostname
          preferredDuringSchedulingIgnoredDuringExecution:
          # 尽量避免与数据库同可用区
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - database
              topologyKey: topology.kubernetes.io/zone
      containers:
      - name: nginx
        image: nginx:alpine
```

## 五、污点与容忍

### 5.1 污点（Taints）

```bash
# 给节点添加污点
kubectl taint nodes node-1 dedicated=production:NoSchedule
kubectl taint nodes node-1 gpu=true:NoSchedule
kubectl taint nodes node-1 maintenance=true:NoExecute

# 查看节点污点
kubectl describe node node-1 | grep Taints

# 移除污点
kubectl taint nodes node-1 dedicated=production:NoSchedule-
kubectl taint nodes node-1 gpu-
```

### 5.2 污点效果类型

| 效果 | 说明 |
|------|------|
| `NoSchedule` | 不允许调度新 Pod，但已运行 Pod 不受影响 |
| `PreferNoSchedule` | 尽量避免调度，但不是强制要求 |
| `NoExecute` | 不允许调度，且会驱逐已运行的 Pod（除非容忍） |

### 5.3 容忍（Tolerations）

```yaml
# 容忍特定污点
apiVersion: v1
kind: Pod
metadata:
  name: gpu-workload
spec:
  containers:
  - name: cuda
    image: nvidia/cuda:11.0-base
    resources:
      limits:
        nvidia.com/gpu: 1
  tolerations:
  - key: "gpu"
    operator: "Equal"
    value: "true"
    effect: "NoSchedule"

---
# 容忍所有效果的污点
apiVersion: v1
kind: Pod
metadata:
  name: critical-pod
spec:
  containers:
  - name: app
    image: critical-app:latest
  tolerations:
  - key: "dedicated"
    operator: "Equal"
    value: "production"
    effect: "NoSchedule"
  - key: "maintenance"
    operator: "Exists"
    effect: "NoExecute"
    tolerationSeconds: 3600  # 容忍 1 小时后驱逐

---
# 容忍任何值的污点
apiVersion: v1
kind: Pod
metadata:
  name: maintenance-worker
spec:
  containers:
  - name: worker
    image: worker:latest
  tolerations:
  - key: "maintenance"
    operator: "Exists"  # 不指定 value，匹配任何值
    effect: "NoExecute"

---
# 容忍所有污点（谨慎使用）
apiVersion: v1
kind: Pod
metadata:
  name: privileged-pod
spec:
  containers:
  - name: app
    image: app:latest
  tolerations:
  - operator: "Exists"  # 匹配所有污点
```

### 5.4 专用节点配置

```yaml
# 创建专用 GPU 节点池
# 1. 给节点添加污点和标签
kubectl taint nodes gpu-node-1 gpu=true:NoSchedule
kubectl taint nodes gpu-node-2 gpu=true:NoSchedule
kubectl label nodes gpu-node-1 node-type=gpu
kubectl label nodes gpu-node-2 node-type=gpu

---
# 2. GPU 工作负载配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ml-training
spec:
  replicas: 2
  selector:
    matchLabels:
      app: ml-training
  template:
    metadata:
      labels:
        app: ml-training
    spec:
      nodeSelector:
        node-type: gpu
      tolerations:
      - key: "gpu"
        operator: "Equal"
        value: "true"
        effect: "NoSchedule"
      containers:
      - name: training
        image: tensorflow/tensorflow:latest-gpu
        resources:
          limits:
            nvidia.com/gpu: 2
```

## 六、Pod 拓扑分布约束

### 6.1 Topology Spread Constraints

```yaml
# 均匀分布 Pod 到不同可用区
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-distributed
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
      - maxSkew: 1                    # 最大不均匀度
        topologyKey: topology.kubernetes.io/zone
        whenUnsatisfiable: DoNotSchedule
        labelSelector:
          matchLabels:
            app: web
        minDomains: 3                 # 最少需要 3 个可用区
      containers:
      - name: nginx
        image: nginx:alpine

---
# 多层拓扑分布
apiVersion: apps/v1
kind: Deployment
metadata:
  name: app-ha
spec:
  replicas: 12
  selector:
    matchLabels:
      app: ha-app
  template:
    metadata:
      labels:
        app: ha-app
    spec:
      topologySpreadConstraints:
      # 第一层：跨区域分布
      - maxSkew: 1
        topologyKey: topology.kubernetes.io/zone
        whenUnsatisfiable: ScheduleAnyway
        labelSelector:
          matchLabels:
            app: ha-app
        minDomains: 2
      # 第二层：区域内跨节点分布
      - maxSkew: 2
        topologyKey: kubernetes.io/hostname
        whenUnsatisfiable: ScheduleAnyway
        labelSelector:
          matchLabels:
            app: ha-app
      containers:
      - name: app
        image: myapp:v1
```

### 6.2 与 PodAntiAffinity 对比

| 特性 | PodAntiAffinity | TopologySpreadConstraints |
|------|-----------------|---------------------------|
| 目的 | 避免 Pod 聚集 | 均匀分布 Pod |
| 强制性 | 强（可以 required） | 可配置（DoNotSchedule/ScheduleAnyway）|
| 灵活性 | 低 | 高（支持 maxSkew） |
| 性能 | 大规模时较慢 | 优化的大规模支持 |
| 推荐场景 | 简单反亲和需求 | 复杂的分布需求 |

## 七、自定义调度器

### 7.1 调度器配置文件

```yaml
# /etc/kubernetes/scheduler-config.yaml
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
profiles:
# 默认调度器配置
- schedulerName: default-scheduler
  plugins:
    # 预选插件
    filter:
      enabled:
      - name: NodeResourcesFit
        args:
          scoringStrategy:
            type: LeastAllocated  # 优先选择资源闲置多的节点
      - name: NodePorts
      - name: NodeAffinity
      disabled:
      - name: NodeName  # 禁用某些插件

    # 优选插件
    score:
      enabled:
      - name: NodeResourcesBalancedAllocation
        weight: 1
      - name: ImageLocality
        weight: 1
      - name: InterPodAffinity
        weight: 2
      - name: NodeAffinity
        weight: 1
      - name: PodTopologySpread
        weight: 2

# GPU 调度器配置
- schedulerName: gpu-scheduler
  plugins:
    filter:
      enabled:
      - name: NodeResourcesFit
      - name: NodeAffinity
    score:
      enabled:
      - name: ImageLocality
        weight: 1
      - name: NodeAffinity
        weight: 10  # 更高的节点亲和性权重
```

### 7.2 使用自定义调度器

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: gpu-job
spec:
  schedulerName: gpu-scheduler  # 指定调度器
  containers:
  - name: training
    image: nvidia/cuda:latest
    resources:
      limits:
        nvidia.com/gpu: 1
```

## 八、调度故障排查

### 8.1 查看调度事件

```bash
# 查看 Pod 调度事件
kubectl describe pod <pod-name> | grep -A 10 Events

# 查看 Pending Pod
kubectl get pods --all-namespaces --field-selector status.phase=Pending

# 查看调度器日志
kubectl logs -n kube-system -l component=kube-scheduler

# 查看节点资源
kubectl describe node <node-name> | grep -A 5 "Allocated resources"

# 查看调度评分
kubectl get events --field-selector reason=Scheduled
```

### 8.2 常见调度问题

```bash
# 问题 1: 资源不足
# 错误: 0/3 nodes are available: 3 Insufficient cpu, 2 Insufficient memory.
# 解决: 扩展集群或调整资源请求

# 问题 2: 节点选择器不匹配
# 错误: 0/3 nodes are available: 3 node(s) didn't match Pod's node affinity.
# 解决: 检查节点标签或调整 nodeSelector

# 问题 3: 污点不匹配
# 错误: 0/3 nodes are available: 1 node(s) had taint {node-role.kubernetes.io/master: },
#       that the pod didn't tolerate.
# 解决: 添加 tolerations 或选择其他节点

# 问题 4: 端口冲突
# 错误: 0/3 nodes are available: 1 node(s) didn't have free ports for
#       the requested pod ports.
# 解决: 更改主机端口或使用动态分配

# 模拟调度（不实际创建 Pod）
kubectl apply --dry-run=server -f pod.yaml
```

## 九、最佳实践

### 9.1 生产环境调度策略

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: production-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: prod-app
  template:
    metadata:
      labels:
        app: prod-app
    spec:
      # 1. 资源请求和限制
      containers:
      - name: app
        image: myapp:v1
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "1Gi"
            cpu: "1000m"

      # 2. 拓扑分布 - 高可用
      topologySpreadConstraints:
      - maxSkew: 1
        topologyKey: topology.kubernetes.io/zone
        whenUnsatisfiable: DoNotSchedule
        labelSelector:
          matchLabels:
            app: prod-app

      # 3. 反亲和性 - 避免同节点
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - prod-app
              topologyKey: kubernetes.io/hostname

        # 4. 节点亲和性 - 优选特定节点
        nodeAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            preference:
              matchExpressions:
              - key: node-type
                operator: In
                values:
                - production

      # 5. 容忍 - 允许调度到专用节点
      tolerations:
      - key: "dedicated"
        operator: "Equal"
        value: "production"
        effect: "NoSchedule"

      # 6. 优雅终止
      terminationGracePeriodSeconds: 60
```

## 十、总结

Kubernetes 调度策略提供了强大的控制能力：

1. **nodeSelector**：简单的节点标签匹配
2. **节点亲和性**：更灵活的节点选择（硬/软约束）
3. **Pod 亲和性/反亲和性**：控制 Pod 之间的分布关系
4. **污点与容忍**：实现专用节点和节点维护
5. **拓扑分布约束**：实现 Pod 的均匀分布
6. **自定义调度器**：针对特殊需求的调度策略

在生产环境中，建议：

- 结合使用多种调度策略实现高可用
- 合理设置资源请求，避免调度失败
- 使用拓扑分布约束实现跨可用区部署
- 定期审查调度配置，优化资源利用率
