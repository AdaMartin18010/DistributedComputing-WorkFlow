# K8s 控制平面详解

## 一、概述

Kubernetes 控制平面（Control Plane）是集群的大脑，负责管理集群的状态和协调各个组件的工作。理解控制平面的工作原理对于部署、运维和调优 Kubernetes 集群至关重要。

## 二、控制平面架构

### 2.1 整体架构图

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      Kubernetes Control Plane                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         API Server                               │    │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │    │
│  │  │   REST API   │  │   etcd       │  │   Authentication     │  │    │
│  │  │   接口层      │  │   Client     │  │   Authorization      │  │    │
│  │  │   Validation │  │              │  │   Admission Control  │  │    │
│  │  └──────────────┘  └──────────────┘  └──────────────────────┘  │    │
│  │  Port: 6443 (HTTPS)                                              │    │
│  └────────────────────────┬────────────────────────────────────────┘    │
│                           │                                              │
│         ┌─────────────────┼─────────────────┐                           │
│         │                 │                 │                           │
│         ▼                 ▼                 ▼                           │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐          │
│  │  Scheduler   │  │  Controller  │  │  etcd                │          │
│  │              │  │  Manager     │  │                      │          │
│  │ Pod 调度     │  │              │  │  键值存储             │          │
│  │ 节点选择     │  │ 节点控制器    │  │  集群状态             │          │
│  │ 资源匹配     │  │ 副本控制器    │  │  配置数据             │          │
│  │              │  │ 端点控制器    │  │                      │          │
│  │              │  │ 服务控制器    │  │  Port: 2379          │          │
│  └──────────────┘  └──────────────┘  └──────────────────────┘          │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                        Worker Nodes                                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                      │
│  │  kubelet    │  │ kube-proxy  │  │ Container  │                      │
│  │             │  │             │  │ Runtime    │                      │
│  │ Pod 管理    │  │ 服务代理    │  │ (containerd│                      │
│  │ 健康检查    │  │ 负载均衡    │  │  /CRI-O)   │                      │
│  │ 资源报告    │  │ 网络规则    │  │            │                      │
│  └─────────────┘  └─────────────┘  └─────────────┘                      │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 控制平面组件职责

| 组件 | 主要职责 | 高可用要求 |
|------|----------|-----------|
| **kube-apiserver** | 暴露 Kubernetes API，处理所有 REST 请求 | 多实例 + 负载均衡 |
| **etcd** | 分布式键值存储，保存集群所有数据 | 奇数节点集群（3/5/7） |
| **kube-scheduler** | 监视新 Pod，选择最佳节点运行 | 多实例（leader 选举） |
| **kube-controller-manager** | 运行各种控制器，维护期望状态 | 多实例（leader 选举） |
| **cloud-controller-manager** | 云厂商特定控制逻辑 | 可选，多实例 |

## 三、API Server 详解

### 3.1 API Server 架构

```
┌─────────────────────────────────────────────────────────────┐
│                    API Server 处理流程                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Client Request                                               │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  1. HTTP/HTTPS 接收层 (6443端口)                     │    │
│  │     - TLS 终止                                       │    │
│  │     - 请求解析                                       │    │
│  └─────────────────────────────────────────────────────┘    │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  2. 认证 (Authentication)                            │    │
│  │     - X509 客户端证书                                │    │
│  │     - Bearer Token (ServiceAccount/JWT)              │    │
│  │     - Webhook Token (OIDC/LDAP)                      │    │
│  └─────────────────────────────────────────────────────┘    │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  3. 授权 (Authorization)                             │    │
│  │     - RBAC (Role-Based Access Control)               │    │
│  │     - ABAC (Attribute-Based Access Control)          │    │
│  │     - Node 授权                                      │    │
│  │     - Webhook 授权                                   │    │
│  └─────────────────────────────────────────────────────┘    │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  4. 准入控制 (Admission Control)                      │    │
│  │     ┌─────────────────────────────────────────┐      │    │
│  │     │ Mutating Webhooks (修改请求)            │      │    │
│  │     │ - Pod Preset, Istio Injection           │      │    │
│  │     └─────────────────────────────────────────┘      │    │
│  │     ┌─────────────────────────────────────────┐      │    │
│  │     │ Validating Webhooks (验证请求)          │      │    │
│  │     │ - 资源限制检查, 安全策略                 │      │    │
│  │     └─────────────────────────────────────────┘      │    │
│  └─────────────────────────────────────────────────────┘    │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │  5. 处理请求                                         │    │
│  │     - 读取: 从 etcd 缓存获取                          │    │
│  │     - 写入: 更新 etcd，触发 Watch 事件                │    │
│  └─────────────────────────────────────────────────────┘    │
│       │                                                      │
│       ▼                                                      │
│  Response to Client                                          │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 API Server 配置

```yaml
# /etc/kubernetes/manifests/kube-apiserver.yaml
apiVersion: v1
kind: Pod
metadata:
  name: kube-apiserver
  namespace: kube-system
spec:
  containers:
  - name: kube-apiserver
    image: registry.k8s.io/kube-apiserver:v1.28.0
    command:
    - kube-apiserver
    # 基本配置
    - --advertise-address=192.168.1.10
    - --bind-address=0.0.0.0
    - --secure-port=6443

    # etcd 连接
    - --etcd-servers=https://192.168.1.10:2379,https://192.168.1.11:2379,https://192.168.1.12:2379
    - --etcd-cafile=/etc/kubernetes/pki/etcd/ca.crt
    - --etcd-certfile=/etc/kubernetes/pki/apiserver-etcd-client.crt
    - --etcd-keyfile=/etc/kubernetes/pki/apiserver-etcd-client.key

    # TLS 配置
    - --tls-cert-file=/etc/kubernetes/pki/apiserver.crt
    - --tls-private-key-file=/etc/kubernetes/pki/apiserver.key
    - --client-ca-file=/etc/kubernetes/pki/ca.crt

    # 认证与授权
    - --authorization-mode=Node,RBAC
    - --enable-admission-plugins=NodeRestriction,NamespaceLifecycle,LimitRanger,ServiceAccount,ResourceQuota
    - --service-account-key-file=/etc/kubernetes/pki/sa.pub
    - --service-account-signing-key-file=/etc/kubernetes/pki/sa.key
    - --service-account-issuer=https://kubernetes.default.svc.cluster.local

    # API 启用/禁用
    - --runtime-config=api/all=true
    - --feature-gates=HPAScaleToZero=true

    # 审计日志
    - --audit-log-path=/var/log/kubernetes/audit.log
    - --audit-log-maxage=30
    - --audit-log-maxbackup=10
    - --audit-log-maxsize=100
    - --audit-policy-file=/etc/kubernetes/audit-policy.yaml

    # 请求限制
    - --max-requests-inflight=400
    - --max-mutating-requests-inflight=200
    - --default-watch-cache-size=100

    # 聚合层配置
    - --proxy-client-cert-file=/etc/kubernetes/pki/front-proxy-client.crt
    - --proxy-client-key-file=/etc/kubernetes/pki/front-proxy-client.key
    - --requestheader-client-ca-file=/etc/kubernetes/pki/front-proxy-ca.crt

    volumeMounts:
    - mountPath: /etc/kubernetes/pki
      name: k8s-certs
      readOnly: true
    - mountPath: /etc/kubernetes/audit-policy.yaml
      name: audit-policy
      readOnly: true
    - mountPath: /var/log/kubernetes
      name: audit-logs
  volumes:
  - name: k8s-certs
    hostPath:
      path: /etc/kubernetes/pki
  - name: audit-policy
    hostPath:
      path: /etc/kubernetes/audit-policy.yaml
  - name: audit-logs
    hostPath:
      path: /var/log/kubernetes
```

### 3.3 常用 API Server 操作

```bash
# 查看 API Server 状态
kubectl get componentstatuses

# 查看 API 资源
kubectl api-resources
kubectl api-resources --namespaced=false
kubectl api-versions

# 查看 API Server 日志
kubectl logs -n kube-system kube-apiserver-master

# 直接与 API Server 交互
kubectl get --raw /api/v1/namespaces/default/pods
kubectl get --raw /apis/metrics.k8s.io/v1beta1/nodes

# 检查 API Server 证书
openssl x509 -in /etc/kubernetes/pki/apiserver.crt -text -noout
```

## 四、etcd 详解

### 4.1 etcd 架构与原理

```
┌─────────────────────────────────────────────────────────────┐
│                      etcd 集群架构                            │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐  │
│  │   etcd-0     │◄──►│   etcd-1     │◄──►│   etcd-2     │  │
│  │  (Leader)    │    │  (Follower)  │    │  (Follower)  │  │
│  │              │    │              │    │              │  │
│  │  Client      │    │              │    │              │  │
│  │  Requests    │    │              │    │              │  │
│  │     │        │    │              │    │              │  │
│  │     ▼        │    │              │    │              │  │
│  │  ┌────────┐  │    │              │    │              │  │
│  │  │  Raft  │  │    │              │    │              │  │
│  │  │  Log   │──┼────┼──────────────┼────┼──────────────┤  │
│  │  └────────┘  │    │              │    │              │  │
│  │     │        │    │              │    │              │  │
│  │     ▼        │    │              │    │              │  │
│  │  ┌────────┐  │    │              │    │              │  │
│  │  │ BoltDB │  │    │              │    │              │  │
│  │  │ (存储)  │  │    │              │    │              │  │
│  │  └────────┘  │    │              │    │              │  │
│  └──────────────┘    └──────────────┘    └──────────────┘  │
│                                                              │
│  推荐配置: 3/5/7 个节点 (奇数，保证选举效率)                     │
│  写入: 需要多数派确认 (N/2 + 1)                               │
│  读取: 可以从任意节点读取                                      │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 etcd 数据存储结构

```
/registry/
├── pods/
│   ├── default/
│   │   ├── nginx-deployment-5c4c8c8b7f-abc12
│   │   └── my-app-7d4f8c9b2e-xyz34
│   └── kube-system/
│       ├── coredns-5c4c8c8b7f-abc12
│       └── kube-proxy-xyz34
├── deployments/
│   └── default/
│       └── nginx-deployment
├── services/
│   └── default/
│       ├── kubernetes
│       └── nginx-service
├── configmaps/
├── secrets/
├── nodes/
├── namespaces/
├── replicasets/
├── daemonsets/
├── statefulsets/
├── ingresses/
├── roles/
├── rolebindings/
└── clusterroles/
```

### 4.3 etcd 运维操作

```bash
# 查看 etcd 成员
etcdctl member list -w table

# 检查 etcd 集群健康
etcdctl endpoint health --cluster

# 查看 etcd 状态
etcdctl endpoint status --cluster -w table

# 备份 etcd
etcdctl snapshot save /backup/etcd-$(date +%Y%m%d-%H%M%S).db

# 恢复 etcd
etcdctl snapshot restore snapshot.db \
  --data-dir=/var/lib/etcd-new \
  --name=etcd-0 \
  --initial-cluster=etcd-0=https://192.168.1.10:2380,etcd-1=https://192.168.1.11:2380 \
  --initial-cluster-token=etcd-cluster-token \
  --initial-advertise-peer-urls=https://192.168.1.10:2380

# 查看特定键的值
etcdctl get /registry/namespaces/default --prefix --keys-only

# 监视键变化
etcdctl watch /registry/pods/default/ --prefix

# 压缩历史版本
etcdctl compaction $(etcdctl endpoint status --write-out=json | jq '.[0].Status.header.revision')
etcdctl defrag

# 检查数据一致性
etcdctl check datascale
```

### 4.4 etcd 配置示例

```yaml
# etcd.yaml
apiVersion: v1
kind: Pod
metadata:
  name: etcd
  namespace: kube-system
spec:
  containers:
  - name: etcd
    image: registry.k8s.io/etcd:3.5.9-0
    command:
    - etcd
    - --name=etcd-0
    - --advertise-client-urls=https://192.168.1.10:2379
    - --listen-client-urls=https://0.0.0.0:2379
    - --listen-peer-urls=https://0.0.0.0:2380
    - --initial-advertise-peer-urls=https://192.168.1.10:2380
    - --initial-cluster=etcd-0=https://192.168.1.10:2380,etcd-1=https://192.168.1.11:2380,etcd-2=https://192.168.1.12:2380
    - --initial-cluster-token=etcd-cluster-token
    - --initial-cluster-state=new
    - --data-dir=/var/lib/etcd
    - --snapshot-count=10000
    - --heartbeat-interval=100
    - --election-timeout=1000
    - --quota-backend-bytes=8589934592  # 8GB
    - --auto-compaction-mode=periodic
    - --auto-compaction-retention=1h
    # TLS 配置
    - --cert-file=/etc/kubernetes/pki/etcd/server.crt
    - --key-file=/etc/kubernetes/pki/etcd/server.key
    - --trusted-ca-file=/etc/kubernetes/pki/etcd/ca.crt
    - --peer-cert-file=/etc/kubernetes/pki/etcd/peer.crt
    - --peer-key-file=/etc/kubernetes/pki/etcd/peer.key
    - --peer-trusted-ca-file=/etc/kubernetes/pki/etcd/ca.crt
    - --peer-client-cert-auth=true
    - --client-cert-auth=true
```

## 五、Scheduler 详解

### 5.1 调度流程

```
┌─────────────────────────────────────────────────────────────┐
│                    Pod 调度流程                              │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. Pod 创建                                                 │
│     │                                                        │
│     ▼                                                        │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  2. 进入调度队列                                         │  │
│  │     - Active Queue (待调度)                             │  │
│  │     - Backoff Queue (失败重试)                          │  │
│  │     - Unschedulable Queue (无法调度)                    │  │
│  └───────────────────────────────────────────────────────┘  │
│     │                                                        │
│     ▼                                                        │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  3. 预选阶段 (Predicates)                                │  │
│  │     ┌─────────────────────────────────────────────┐    │  │
│  │     │ • PodFitsResources    (资源是否足够)         │    │  │
│  │     │ • PodFitsHost         (主机名匹配)           │    │  │
│  │     │ • PodFitsHostPorts    (端口是否冲突)         │    │  │
│  │     │ • PodMatchNodeSelector (标签匹配)            │    │  │
│  │     │ • NoDiskConflict      (存储冲突检查)         │    │  │
│  │     │ • CheckNodeMemoryPressure (内存压力)         │    │  │
│  │     │ • CheckNodeDiskPressure   (磁盘压力)         │    │  │
│  │     │ • PodToleratesNodeTaints  (污点容忍)         │    │  │
│  │     └─────────────────────────────────────────────┘    │  │
│  │     结果: 筛选出可用节点列表                              │  │
│  └───────────────────────────────────────────────────────┘  │
│     │                                                        │
│     ▼                                                        │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  4. 优选阶段 (Priorities)                                │  │
│  │     ┌─────────────────────────────────────────────┐    │  │
│  │     │ • LeastRequestedPriority       (资源闲置)   │    │  │
│  │     │ • BalancedResourceAllocation   (资源平衡)   │    │  │
│  │     │ • NodeAffinityPriority         (节点亲和)   │    │  │
│  │     │ • ImageLocalityPriority        (镜像本地)   │    │  │
│  │     │ • TaintTolerationPriority      (污点容忍)   │    │  │
│  │     │ • InterPodAffinityPriority     (Pod间亲和)  │    │  │
│  │     └─────────────────────────────────────────────┘    │  │
│  │     结果: 为每个节点打分，选择最高分节点                    │  │
│  └───────────────────────────────────────────────────────┘  │
│     │                                                        │
│     ▼                                                        │
│  5. 绑定 Pod 到选定节点                                       │
│     │                                                        │
│     ▼                                                        │
│  6. kubelet 创建 Pod                                         │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 Scheduler 配置

```yaml
# scheduler-config.yaml
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
profiles:
- schedulerName: default-scheduler
  plugins:
    # 预选插件
    filter:
      enabled:
      - name: NodeResourcesFit
        args:
          scoringStrategy:
            type: LeastAllocated
            resources:
            - name: cpu
              weight: 1
            - name: memory
              weight: 1
      disabled:
      - name: NodeName

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

    # 绑定插件
    bind:
      enabled:
      - name: DefaultBind

  # 插件参数
  pluginConfig:
  - name: InterPodAffinity
    args:
      hardPodAffinityWeight: 100

# 启动时指定配置
# kube-scheduler --config=/etc/kubernetes/scheduler-config.yaml
```

## 六、Controller Manager 详解

### 6.1 控制器类型

```
┌─────────────────────────────────────────────────────────────┐
│                 Controller Manager 控制器                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  工作负载控制器                                         │  │
│  │  ├── Deployment Controller    (无状态应用部署)          │  │
│  │  ├── ReplicaSet Controller    (副本数量控制)            │  │
│  │  ├── StatefulSet Controller   (有状态应用部署)          │  │
│  │  ├── DaemonSet Controller     (守护进程部署)            │  │
│  │  └── Job/CronJob Controller   (批处理任务)              │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  节点和网络控制器                                       │  │
│  │  ├── Node Controller          (节点生命周期)            │  │
│  │  ├── Endpoint Controller      (服务端点管理)            │  │
│  │  ├── EndpointSlice Controller (端点切片)                │  │
│  │  └── Service Account Controller (服务账户)              │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  资源配额和自动扩缩容                                     │  │
│  │  ├── ResourceQuota Controller (资源配额)                │  │
│  │  ├── LimitRange Controller    (资源限制)                │  │
│  │  ├── HorizontalPodAutoscaler (HPA 控制器)               │  │
│  │  └── VerticalPodAutoscaler   (VPA 控制器)               │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  存储控制器                                             │  │
│  │  ├── PV Controller            (持久卷)                  │  │
│  │  ├── PVC Controller           (持久卷声明)              │  │
│  │  └── StorageClass Controller  (存储类)                  │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 控制器工作原理

```go
// 控制循环（Control Loop）伪代码
for {
    // 1. 获取期望状态 (Desired State)
    desired := getDesiredState()

    // 2. 获取当前状态 (Current State)
    current := getCurrentState()

    // 3. 计算差异
    diff := compare(desired, current)

    // 4. 执行调和动作
    if diff.needsCreate {
        createResource(diff.toCreate)
    }
    if diff.needsUpdate {
        updateResource(diff.toUpdate)
    }
    if diff.needsDelete {
        deleteResource(diff.toDelete)
    }

    // 5. 等待或监听变化
    waitForNextEvent()
}
```

### 6.3 控制器配置

```yaml
# controller-manager.yaml
apiVersion: v1
kind: Pod
metadata:
  name: kube-controller-manager
  namespace: kube-system
spec:
  containers:
  - name: kube-controller-manager
    image: registry.k8s.io/kube-controller-manager:v1.28.0
    command:
    - kube-controller-manager
    # 基础配置
    - --bind-address=0.0.0.0
    - --secure-port=10257
    - --cluster-name=kubernetes

    # API Server 连接
    - --kubeconfig=/etc/kubernetes/controller-manager.conf
    - --authentication-kubeconfig=/etc/kubernetes/controller-manager.conf
    - --authorization-kubeconfig=/etc/kubernetes/controller-manager.conf

    # 控制器配置
    - --concurrent-deployment-syncs=5
    - --concurrent-endpoint-syncs=5
    - --concurrent-gc-syncs=20
    - --concurrent-namespace-syncs=10
    - --concurrent-rc-syncs=5
    - --concurrent-replicaset-syncs=5
    - --concurrent-resource-quota-syncs=5
    - --concurrent-service-syncs=1
    - --concurrent-serviceaccount-token-syncs=5

    # 节点控制器配置
    - --node-monitor-grace-period=40s
    - --node-monitor-period=5s
    - --node-startup-grace-period=60s
    - --pod-eviction-timeout=5m0s

    # 水平扩缩容配置
    - --horizontal-pod-autoscaler-sync-period=15s
    - --horizontal-pod-autoscaler-tolerance=0.1
    - --horizontal-pod-autoscaler-cpu-initialization-period=90s
    - --horizontal-pod-autoscaler-initial-readiness-delay=30s

    # 服务配置
    - --service-cluster-ip-range=10.96.0.0/12
    - --cluster-cidr=10.244.0.0/16
    - --allocate-node-cidrs=true

    # TLS 配置
    - --root-ca-file=/etc/kubernetes/pki/ca.crt
    - --service-account-private-key-file=/etc/kubernetes/pki/sa.key

    # _leader 选举
    - --leader-elect=true
    - --leader-elect-lease-duration=15s
    - --leader-elect-renew-deadline=10s
    - --leader-elect-retry-period=2s
```

## 七、控制平面高可用

### 7.1 高可用架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      高可用控制平面架构                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│                              ┌─────────────┐                            │
│                              │   Load      │                            │
│                              │  Balancer   │                            │
│                              │  (VIP:6443) │                            │
│                              └──────┬──────┘                            │
│                                     │                                    │
│           ┌─────────────────────────┼─────────────────────────┐          │
│           │                         │                         │          │
│           ▼                         ▼                         ▼          │
│  ┌─────────────────┐      ┌─────────────────┐      ┌─────────────────┐  │
│  │  Control Plane  │      │  Control Plane  │      │  Control Plane  │  │
│  │     Node 1      │      │     Node 2      │      │     Node 3      │  │
│  │  ┌───────────┐  │      │  ┌───────────┐  │      │  ┌───────────┐  │  │
│  │  │API Server │  │◄────►│  │API Server │  │◄────►│  │API Server │  │  │
│  │  └───────────┘  │      │  └───────────┘  │      │  └───────────┘  │  │
│  │  ┌───────────┐  │      │  ┌───────────┐  │      │  ┌───────────┐  │  │
│  │  │ Scheduler │  │◄────►│  │ Scheduler │  │◄────►│  │ Scheduler │  │  │
│  │  └───────────┘  │      │  └───────────┘  │      │  └───────────┘  │  │
│  │  ┌───────────┐  │      │  ┌───────────┐  │      │  ┌───────────┐  │  │
│  │  │Controller │  │◄────►│  │Controller │  │◄────►│  │Controller │  │  │
│  │  │ Manager   │  │      │  │ Manager   │  │      │  │ Manager   │  │  │
│  │  └───────────┘  │      │  └───────────┘  │      │  └───────────┘  │  │
│  │  ┌───────────┐  │      │  ┌───────────┐  │      │  ┌───────────┐  │  │
│  │  │   etcd    │  │◄────►│  │   etcd    │  │◄────►│  │   etcd    │  │  │
│  │  │ (Member)  │  │      │  │ (Member)  │  │      │  │ (Member)  │  │  │
│  │  └───────────┘  │      │  └───────────┘  │      │  └───────────┘  │  │
│  └─────────────────┘      └─────────────────┘      └─────────────────┘  │
│                                                                          │
│  负载均衡器: HAProxy/Nginx/Keepalived/云LB                               │
│  存储: etcd 集群 (Raft 协议保证一致性)                                    │
│  Leader 选举: Scheduler 和 Controller Manager 自动选举                    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 7.2 控制平面故障排查

```bash
# 检查控制平面 Pod 状态
kubectl get pods -n kube-system

# 检查节点状态
kubectl get nodes
kubectl describe node <node-name>

# 检查 API Server 健康
curl -k https://localhost:6443/healthz
curl -k https://localhost:6443/livez
curl -k https://localhost:6443/readyz

# 检查 etcd 健康
ETCDCTL_API=3 etcdctl --endpoints=https://127.0.0.1:2379 \
  --cacert=/etc/kubernetes/pki/etcd/ca.crt \
  --cert=/etc/kubernetes/pki/etcd/healthcheck-client.crt \
  --key=/etc/kubernetes/pki/etcd/healthcheck-client.key \
  endpoint health

# 检查证书过期
kubeadm certs check-expiration

# 查看控制平面日志
journalctl -u kube-apiserver -f
journalctl -u kube-scheduler -f
journalctl -u kube-controller-manager -f
journalctl -u etcd -f

# 检查资源使用情况
top
kubectl top nodes
kubectl top pods -n kube-system
```

## 八、总结

Kubernetes 控制平面是集群的大脑，各组件协同工作维护集群的期望状态：

1. **API Server** 是所有组件通信的中心枢纽，处理认证、授权和准入控制
2. **etcd** 是可靠的分布式存储，保存集群的所有配置和状态
3. **Scheduler** 负责智能调度，将 Pod 分配到合适的节点
4. **Controller Manager** 运行各种控制器，持续调和实际状态与期望状态

在生产环境中：

- 必须部署高可用控制平面（至少 3 个节点）
- 定期备份 etcd 数据
- 监控控制平面组件健康状况
- 及时更新证书
- 合理配置资源限制和调度策略
