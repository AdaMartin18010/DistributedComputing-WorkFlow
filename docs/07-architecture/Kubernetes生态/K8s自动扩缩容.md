# K8s 自动扩缩容

## 一、概述

Kubernetes 自动扩缩容机制可以根据负载动态调整应用程序的资源分配，确保应用在面对流量波动时保持高性能和高可用性，同时优化资源利用率。Kubernetes 提供了三种主要的自动扩缩容方式：HPA（水平 Pod 自动扩缩容）、VPA（垂直 Pod 自动扩缩容）和 Cluster Autoscaler（集群节点自动扩缩容）。

## 二、自动扩缩容架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  Kubernetes 自动扩缩容架构                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                     HPA (Horizontal)                             │    │
│  │  ┌──────────┐     ┌──────────┐     ┌──────────────────────┐    │    │
│  │  │  Metrics │────►│   HPA    │────►│  Scale Deployment    │    │    │
│  │  │  Server  │     │ Controller│    │  Replicas: 3 → 10    │    │    │
│  │  └──────────┘     └──────────┘     └──────────────────────┘    │    │
│  │       ▲                               │                        │    │
│  │       │                               ▼                        │    │
│  │  ┌──────────┐                    ┌──────────┐                  │    │
│  │  │  Custom  │                    │   Pods   │                  │    │
│  │  │  Metrics │                    │  ◄──►    │                  │    │
│  │  └──────────┘                    └──────────┘                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                     VPA (Vertical)                               │    │
│  │  ┌──────────┐     ┌──────────┐     ┌──────────────────────┐    │    │
│  │  │   VPA    │────►│Recommender│────►│  Update Resources    │    │    │
│  │  │  Object  │     │   Model  │     │  CPU: 100m → 500m    │    │    │
│  │  └──────────┘     └──────────┘     │  Memory: 256Mi → 1Gi │    │    │
│  │                                     └──────────────────────┘    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                Cluster Autoscaler                                │    │
│  │  ┌──────────┐     ┌──────────┐     ┌──────────────────────┐    │    │
│  │  │ Pending  │────►│  Cluster │────►│  Add/Remove Nodes    │    │    │
│  │  │   Pods   │     │Autoscaler│     │  Nodes: 3 → 5        │    │    │
│  │  └──────────┘     └──────────┘     └──────────────────────┘    │    │
│  │         ▲                                                        │    │
│  │         │ Unschedulable                                          │    │
│  │  ┌──────────┐                                                    │    │
│  │  │  Node    │                                                    │    │
│  │  │  Groups  │                                                    │    │
│  │  └──────────┘                                                    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## 三、HPA（Horizontal Pod Autoscaler）

### 3.1 HPA 工作原理

```
┌─────────────────────────────────────────────────────────────┐
│                   HPA 工作流程                               │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────┐                                              │
│  │   Pod    │                                              │
│  │ Metrics  │  1. 采集指标                                  │
│  └────┬─────┘                                              │
│       │                                                      │
│       ▼                                                      │
│  ┌──────────┐     ┌──────────┐     ┌──────────┐            │
│  │  Metrics │     │  Custom  │     │ External │            │
│  │  Server  │     │  Metrics │     │  Metrics │            │
│  │ (CPU/Mem)│     │  (Prom)  │     │  (Cloud) │            │
│  └────┬─────┘     └────┬─────┘     └────┬─────┘            │
│       │                │                │                   │
│       └────────────────┴────────────────┘                   │
│                        │                                     │
│                        ▼                                     │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  2. HPA Controller 计算期望副本数                     │   │
│  │                                                     │   │
│  │  desiredReplicas = ceil[currentReplicas ×           │   │
│  │                    (currentMetricValue /             │   │
│  │                     desiredMetricValue)]            │   │
│  │                                                     │   │
│  │  考虑因素:                                          │   │
│  │  - minReplicas / maxReplicas 限制                   │   │
│  │  - 缩放冷却时间 (scaleDownDelay)                     │   │
│  │  - 行为策略 (behavior policies)                      │   │
│  └─────────────────────────┬───────────────────────────┘   │
│                            │                                 │
│                            ▼                                 │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  3. 调用 Scale API 调整副本数                         │   │
│  │                                                     │   │
│  │  Deployment/ReplicaSet/StatefulSet.replicas = N     │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 基于 CPU/Memory 的 HPA

```yaml
# 基本 HPA 配置
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: app-hpa
  namespace: production
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  minReplicas: 2
  maxReplicas: 20
  metrics:
  # CPU 利用率目标
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  # 内存利用率目标
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  # 也可以设置绝对值
  - type: Resource
    resource:
      name: cpu
      target:
        type: AverageValue
        averageValue: "500m"

---
# 带行为的 HPA
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: app-hpa-advanced
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: api-server
  minReplicas: 3
  maxReplicas: 100
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 60
  behavior:
    # 扩容行为
    scaleUp:
      stabilizationWindowSeconds: 60  # 稳定窗口
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15  # 15秒内最多扩容100%
      - type: Pods
        value: 4
        periodSeconds: 15  # 15秒内最多扩容4个Pod
      selectPolicy: Max  # 选择最大的策略
    # 缩容行为
    scaleDown:
      stabilizationWindowSeconds: 300  # 5分钟后才考虑缩容
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60  # 每分钟最多缩容10%
      - type: Pods
        value: 2
        periodSeconds: 60  # 每分钟最多缩容2个Pod
      selectPolicy: Min  # 选择最保守的策略
```

### 3.3 基于自定义指标的 HPA

```yaml
# 基于 Prometheus 自定义指标
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: custom-metrics-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  minReplicas: 2
  maxReplicas: 50
  metrics:
  # HTTP 请求延迟 P99
  - type: Pods
    pods:
      metric:
        name: http_request_duration_seconds_p99
      target:
        type: AverageValue
        averageValue: "0.5"  # 500ms

  # 每秒请求数
  - type: Pods
    pods:
      metric:
        name: http_requests_per_second
      target:
        type: AverageValue
        averageValue: "1000"

  # 消息队列积压
  - type: External
    external:
      metric:
        name: kafka_consumer_lag
        selector:
          matchLabels:
            topic: orders
      target:
        type: AverageValue
        averageValue: "100"

  # 外部指标（云厂商）
  - type: External
    external:
      metric:
        name: sqs_queue_length
        selector:
          matchLabels:
            queue: worker-queue
      target:
        type: Value
        value: "30"
```

### 3.4 HPA 配套 Deployment 配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-app
spec:
  replicas: 3  # HPA 会覆盖此值
  selector:
    matchLabels:
      app: web-app
  template:
    metadata:
      labels:
        app: web-app
    spec:
      containers:
      - name: app
        image: myapp:v1
        ports:
        - containerPort: 8080
        resources:
          # 必须设置资源请求，HPA 才能计算利用率
          requests:
            cpu: "200m"
            memory: "256Mi"
          limits:
            cpu: "1000m"
            memory: "512Mi"
        # 应用指标端点
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
---
# Service 配合
apiVersion: v1
kind: Service
metadata:
  name: web-app
  annotations:
    # Prometheus 监控
    prometheus.io/scrape: "true"
    prometheus.io/port: "8080"
spec:
  selector:
    app: web-app
  ports:
  - port: 80
    targetPort: 8080
```

## 四、VPA（Vertical Pod Autoscaler）

### 4.1 VPA 工作原理

```
┌─────────────────────────────────────────────────────────────┐
│                   VPA 工作流程                               │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌─────────────┐   ┌─────────────┐   ┌─────────────────┐   │
│  │   Metrics   │   │   History   │   │   Live          │   │
│  │   Server    │   │   Storage   │   │   Metrics       │   │
│  └──────┬──────┘   └──────┬──────┘   └────────┬────────┘   │
│         │                 │                    │            │
│         └─────────────────┴────────────────────┘            │
│                           │                                 │
│                           ▼                                 │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              Recommender                            │   │
│  │                                                     │   │
│  │  1. 收集历史资源使用数据                             │   │
│  │  2. 分析资源使用模式                                 │   │
│  │  3. 计算推荐资源配置                                 │   │
│  │                                                     │   │
│  │  推荐类型:                                          │   │
│  │  - Target:    最可能满足需求的配置                   │   │
│  │  - LowerBound: 最小可靠配置                          │   │
│  │  - UpperBound: 最大推荐配置                          │   │
│  │  - UncappedTarget: 无限制目标                        │   │
│  └─────────────────────────┬───────────────────────────┘   │
│                            │                                 │
│                            ▼                                 │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              VPA Modes                              │   │
│  │                                                     │   │
│  │  "Off":      仅推荐，不修改资源                     │   │
│  │  "Initial":  仅在创建 Pod 时设置资源                │   │
│  │  "Recreate": 更新资源时重建 Pod                     │   │
│  │  "Auto":     自动在需要时重建 Pod                   │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 VPA 配置

```yaml
# VPA 配置
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: app-vpa
  namespace: production
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  updatePolicy:
    updateMode: "Auto"  # Off, Initial, Recreate, Auto
    minReplicas: 2      # 最小保留副本数
  resourcePolicy:
    containerPolicies:
    - containerName: '*'  # 应用到所有容器
      minAllowed:
        cpu: 50m
        memory: 100Mi
      maxAllowed:
        cpu: 2000m
        memory: 2Gi
      controlledResources:
        - cpu
        - memory
      controlledValues: RequestsAndLimits  # 或 RequestsOnly

    # 特定容器配置
    - containerName: sidecar
      mode: "Off"  # 不管理此容器

---
# 仅初始模式（不重建运行中的 Pod）
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: app-vpa-initial
spec:
  targetRef:
    apiVersion: apps/v1
    kind: StatefulSet
    name: database
  updatePolicy:
    updateMode: "Initial"  # 只在创建时设置
  resourcePolicy:
    containerPolicies:
    - containerName: postgres
      minAllowed:
        memory: "512Mi"
      maxAllowed:
        memory: "8Gi"
```

### 4.3 VPA 与 HPA 配合使用

```yaml
# VPA 调整资源请求，HPA 调整副本数
# 注意：不要同时对同一指标使用两者

apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: app-vpa
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  updatePolicy:
    updateMode: "Auto"
  resourcePolicy:
    containerPolicies:
    - containerName: app
      controlledResources: ["memory"]  # VPA 只管理内存

---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: app-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  minReplicas: 2
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu  # HPA 只基于 CPU
      target:
        type: Utilization
        averageUtilization: 70
```

## 五、Cluster Autoscaler

### 5.1 Cluster Autoscaler 架构

```
┌─────────────────────────────────────────────────────────────┐
│               Cluster Autoscaler 架构                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │           Cluster Autoscaler Pod                       │  │
│  │                                                      │  │
│  │  ┌─────────────┐   ┌─────────────┐   ┌────────────┐ │  │
│  │  │   Pod       │   │   Node      │   │   Cloud    │ │  │
│  │  │   Monitor   │   │   Monitor   │   │   Provider │ │  │
│  │  └──────┬──────┘   └──────┬──────┘   └─────┬──────┘ │  │
│  │         │                 │                 │        │  │
│  │         └─────────────────┴─────────────────┘        │  │
│  │                           │                          │  │
│  │                           ▼                          │  │
│  │  ┌───────────────────────────────────────────────┐  │  │
│  │  │          Scale Up Decision                     │  │  │
│  │  │  - 检测不可调度 Pod                            │  │  │
│  │  │  - 检查节点组模板                              │  │  │
│  │  │  - 计算需要节点数                              │  │  │
│  │  │  - 调用云 API 创建节点                         │  │  │
│  │  └───────────────────────────────────────────────┘  │  │
│  │                           │                          │  │
│  │                           ▼                          │  │
│  │  ┌───────────────────────────────────────────────┐  │  │
│  │  │          Scale Down Decision                   │  │  │
│  │  │  - 检测低利用率节点                            │  │  │
│  │  │  - 检查 Pod 驱逐条件                           │  │  │
│  │  │  - 标记节点为待删除                            │  │  │
│  │  │  - 驱逐 Pod 后删除节点                         │  │  │
│  │  └───────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 Cluster Autoscaler 配置

```yaml
# Cluster Autoscaler Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: cluster-autoscaler
  namespace: kube-system
  labels:
    app: cluster-autoscaler
spec:
  replicas: 1
  selector:
    matchLabels:
      app: cluster-autoscaler
  template:
    metadata:
      labels:
        app: cluster-autoscaler
    spec:
      serviceAccountName: cluster-autoscaler
      containers:
      - name: cluster-autoscaler
        image: registry.k8s.io/autoscaling/cluster-autoscaler:v1.28.0
        command:
        - ./cluster-autoscaler
        - --v=4
        - --stderrthreshold=info
        - --cloud-provider=aws
        - --skip-nodes-with-local-storage=false
        - --skip-nodes-with-system-pods=false
        - --expander=least-waste  # 扩展策略
        - --balance-similar-node-groups=true
        - --scale-down-enabled=true
        - --scale-down-delay-after-add=10m
        - --scale-down-delay-after-delete=5m
        - --scale-down-delay-after-failure=3m
        - --scale-down-unneeded-time=10m
        - --scale-down-utilization-threshold=0.5
        - --node-group-auto-discovery=asg:tag=k8s.io/cluster-autoscaler/enabled,k8s.io/cluster-autoscaler/my-cluster
        env:
        - name: AWS_REGION
          value: us-west-2
        volumeMounts:
        - name: ssl-certs
          mountPath: /etc/ssl/certs/ca-certificates.crt
          readOnly: true
      volumes:
      - name: ssl-certs
        hostPath:
          path: /etc/ssl/certs/ca-bundle.crt
```

### 5.3 AWS Auto Scaling Group 配置

```yaml
# 节点组配置
apiVersion: karpenter.sh/v1beta1
kind: NodePool
metadata:
  name: default
spec:
  template:
    spec:
      requirements:
      - key: kubernetes.io/arch
        operator: In
        values: ["amd64", "arm64"]
      - key: kubernetes.io/os
        operator: In
        values: ["linux"]
      - key: karpenter.sh/capacity-type
        operator: In
        values: ["spot", "on-demand"]
      - key: node.kubernetes.io/instance-type
        operator: In
        values: ["m5.large", "m5.xlarge", "m5.2xlarge"]
      nodeClassRef:
        name: default
  limits:
    cpu: 1000
    memory: 1000Gi
  disruption:
    consolidationPolicy: WhenUnderutilized
    expireAfter: 720h

---
# EC2NodeClass
apiVersion: karpenter.k8s.aws/v1beta1
kind: EC2NodeClass
metadata:
  name: default
spec:
  amiFamily: AL2
  role: KarpenterNodeRole
  subnetSelectorTerms:
  - tags:
      karpenter.sh/discovery: "true"
  securityGroupSelectorTerms:
  - tags:
      karpenter.sh/discovery: "true"
  amiSelectorTerms:
  - alias: al2@latest
  blockDeviceMappings:
  - deviceName: /dev/xvda
    ebs:
      volumeSize: 100Gi
      volumeType: gp3
      encrypted: true
```

## 六、KEDA（Kubernetes Event-driven Autoscaling）

### 6.1 KEDA 架构

```
┌─────────────────────────────────────────────────────────────┐
│                   KEDA 架构                                  │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              Event Sources                             │  │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────────┐ │  │
│  │  │ Kafka   │ │ RabbitMQ│ │ SQS     │ │ Prometheus  │ │  │
│  │  │ Azure   │ │ GCP Pub │ │ NATS    │ │ MySQL       │ │  │
│  │  │ Service │ │ /Sub    │ │ Redis   │ │ MongoDB     │ │  │
│  │  │ Bus     │ │         │ │         │ │ ...         │ │  │
│  │  └────┬────┘ └────┬────┘ └────┬────┘ └──────┬──────┘ │  │
│  │       └─────────────┴─────────────┴───────────┘       │  │
│  │                         │                             │  │
│  └─────────────────────────┼─────────────────────────────┘  │
│                            │                                 │
│                            ▼                                 │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              KEDA Operator                             │  │
│  │                                                      │  │
│  │  ┌─────────────┐    ┌─────────────┐    ┌──────────┐ │  │
│  │  │   Scaled    │    │   Metrics   │    │  HPA     │ │  │
│  │  │   Object    │───►│   Adapter   │───►│ Controller│ │  │
│  │  │   Controller│    │             │    │          │ │  │
│  │  └─────────────┘    └─────────────┘    └──────────┘ │  │
│  │                                                      │  │
│  └───────────────────────────────────────────────────────┘  │
│                            │                                 │
│                            ▼                                 │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              ScaledObject                              │  │
│  │  (定义缩放目标和触发器)                                 │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 KEDA ScaledObject 配置

```yaml
# Kafka 消息驱动扩缩容
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: kafka-scaled-object
  namespace: default
spec:
  scaleTargetRef:
    name: kafka-consumer
    kind: Deployment
    apiVersion: apps/v1
  pollingInterval: 30
  cooldownPeriod: 300
  minReplicaCount: 0      # 可以缩容到 0
  maxReplicaCount: 100
  advanced:
    restoreToOriginalReplicaCount: true
    horizontalPodAutoscalerConfig:
      behavior:
        scaleDown:
          stabilizationWindowSeconds: 300
          policies:
          - type: Percent
            value: 50
            periodSeconds: 60
  triggers:
  - type: kafka
    metadata:
      bootstrapServers: kafka-cluster-kafka-bootstrap:9092
      consumerGroup: my-group
      topic: test-topic
      lagThreshold: "100"      # 每条消息延迟阈值
      activationLagThreshold: "10"
      offsetResetPolicy: latest

---
# RabbitMQ 队列深度驱动
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: rabbitmq-scaled-object
spec:
  scaleTargetRef:
    name: order-processor
  minReplicaCount: 1
  maxReplicaCount: 50
  triggers:
  - type: rabbitmq
    metadata:
      protocol: amqp
      queueName: order_queue
      mode: QueueLength
      value: "100"             # 队列长度超过 100 时扩容
    authenticationRef:
      name: rabbitmq-trigger-auth

---
# Prometheus 指标驱动
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: prometheus-scaled-object
spec:
  scaleTargetRef:
    name: api-server
  minReplicaCount: 2
  maxReplicaCount: 20
  triggers:
  - type: prometheus
    metadata:
      serverAddress: http://prometheus:9090
      metricName: http_requests_per_second
      threshold: "100"
      query: |
        sum(rate(http_requests_total{service="api-server"}[2m]))

---
# 多触发器组合
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: multi-trigger-scaled-object
spec:
  scaleTargetRef:
    name: worker
  minReplicaCount: 2
  maxReplicaCount: 50
  triggers:
  # CPU 触发器
  - type: cpu
    metricType: Utilization
    metadata:
      value: "70"
  # 内存触发器
  - type: memory
    metricType: Utilization
    metadata:
      value: "80"
  # 自定义业务指标
  - type: metrics-api
    metadata:
      targetValue: "100"
      url: "http://metrics-service/metrics"
      valueLocation: "data.queue_length"
```

## 七、扩缩容最佳实践

### 7.1 综合扩缩容方案

```yaml
# 生产环境完整扩缩容配置

# 1. 应用部署（设置资源请求）
apiVersion: apps/v1
kind: Deployment
metadata:
  name: production-app
  labels:
    app: production-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: production-app
  template:
    metadata:
      labels:
        app: production-app
    spec:
      containers:
      - name: app
        image: myapp:v1
        ports:
        - containerPort: 8080
        resources:
          requests:
            cpu: "500m"
            memory: "512Mi"
          limits:
            cpu: "2000m"
            memory: "2Gi"
        # 优雅关闭，配合缩容
        lifecycle:
          preStop:
            exec:
              command: ["/bin/sh", "-c", "sleep 10"]
      terminationGracePeriodSeconds: 60

---
# 2. HPA 配置（水平扩容）
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: production-app-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: production-app
  minReplicas: 3
  maxReplicas: 50
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Pods
        value: 4
        periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60

---
# 3. VPA 配置（垂直优化）
apiVersion: autoscaling.k8s.io/v1
kind: VerticalPodAutoscaler
metadata:
  name: production-app-vpa
spec:
  targetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: production-app
  updatePolicy:
    updateMode: "Off"  # 初始关闭，观察推荐值后再开启
  resourcePolicy:
    containerPolicies:
    - containerName: app
      minAllowed:
        cpu: 100m
        memory: 128Mi
      maxAllowed:
        cpu: 4000m
        memory: 4Gi
      controlledResources: ["cpu", "memory"]

---
# 4. KEDA 配置（事件驱动）
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: production-app-keda
spec:
  scaleTargetRef:
    name: production-app
  minReplicaCount: 3
  maxReplicaCount: 100
  triggers:
  # 基于队列长度
  - type: aws-sqs-queue
    authenticationRef:
      name: keda-aws-credentials
    metadata:
      queueURL: https://sqs.us-west-2.amazonaws.com/123456789/my-queue
      queueLength: "5"
      awsRegion: "us-west-2"
```

### 7.2 扩缩容监控告警

```yaml
# PrometheusRule 告警
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: autoscaling-alerts
  namespace: monitoring
spec:
  groups:
  - name: autoscaling
    rules:
    # HPA 达到最大副本数
    - alert: HPAMaxReplicasReached
      expr: |
        kube_horizontalpodautoscaler_status_current_replicas
        /
        kube_horizontalpodautoscaler_spec_max_replicas == 1
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "HPA {{ $labels.horizontalpodautoscaler }} 已达到最大副本数"
        description: "HPA {{ $labels.horizontalpodautoscaler }} 在 namespace {{ $labels.namespace }} 已达到最大副本数 {{ $labels.max_replicas }}"

    # 扩容失败
    - alert: HPAScaleUpFailed
      expr: |
        increase(kube_horizontalpodautoscaler_status_condition{condition="ScalingActive",status="false"}[5m]) > 0
      for: 0m
      labels:
        severity: critical
      annotations:
        summary: "HPA 扩容失败"
        description: "HPA {{ $labels.horizontalpodautoscaler }} 扩容失败"

    # Pod 长时间 Pending（可能需要扩容节点）
    - alert: PodsStuckPending
      expr: |
        count by (namespace) (
          kube_pod_status_phase{phase="Pending"} == 1
        ) > 10
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "大量 Pod 处于 Pending 状态"
        description: "Namespace {{ $labels.namespace }} 有超过 10 个 Pod 处于 Pending 状态，可能需要扩容节点"
```

## 八、总结

Kubernetes 自动扩缩容提供了多层级的弹性能力：

| 类型 | 作用对象 | 触发条件 | 适用场景 |
|------|----------|----------|----------|
| **HPA** | Pod 副本数 | CPU/内存/自定义指标 | 无状态应用、API 服务 |
| **VPA** | Pod 资源请求 | 历史资源使用模式 | 资源优化、成本节省 |
| **Cluster Autoscaler** | 集群节点数 | Pod 调度需求 | 基础设施弹性 |
| **KEDA** | Pod 副本数 | 事件源（消息队列等）| 事件驱动应用 |

最佳实践：

1. **HPA + Cluster Autoscaler**：最常用的组合，实现应用和基础设施弹性
2. **VPA 初始模式**：用于确定合理的资源请求值
3. **KEDA**：用于事件驱动的批处理任务
4. **避免 HPA 和 VPA 冲突**：不要同时基于同一指标进行水平和垂直扩容
5. **设置合理的缩容延迟**：避免频繁的扩缩容震荡
6. **监控扩缩容事件**：及时发现和解决扩缩容问题
