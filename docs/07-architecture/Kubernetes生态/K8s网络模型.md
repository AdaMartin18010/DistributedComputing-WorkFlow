# K8s 网络模型

## 一、概述

Kubernetes 网络模型定义了集群中 Pod、Service 和外部实体之间通信的规则。与 Docker 的默认网络不同，Kubernetes 采用了一种独特的扁平网络设计，为容器编排提供了强大的网络能力。

## 二、Kubernetes 网络核心原则

### 2.1 网络模型要求

```
┌─────────────────────────────────────────────────────────────┐
│              Kubernetes 网络模型核心原则                      │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. 每个 Pod 拥有独立的 IP 地址                               │
│     ┌─────────────┐      ┌─────────────┐                    │
│     │   Pod A     │      │   Pod B     │                    │
│     │  10.244.1.2 │      │  10.244.2.3 │                    │
│     └─────────────┘      └─────────────┘                    │
│                                                              │
│  2. 所有 Pod 可以在没有 NAT 的情况下互相通信                    │
│     Pod A ────────────────────────────────► Pod B           │
│     Source IP: 10.244.1.2  ───────────────► Dest IP: 10.244.2.3│
│     (IP 保持不变)                                             │
│                                                              │
│  3. 所有节点可以与所有 Pod 通信                                │
│     Node 1 ───────────────────────────────► Pod B           │
│     192.168.1.10 ────────────────────────► 10.244.2.3       │
│                                                              │
│  4. Pod 可以看到自己的 IP（与其他 Pod 看到的一致）               │
│     Pod A 内部看到的 IP = 其他 Pod 看到的 Pod A IP            │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 与传统 Docker 网络对比

| 特性 | Docker 默认 | Kubernetes |
|------|-------------|------------|
| Pod IP | 动态分配，变化频繁 | 集群内唯一，相对固定 |
| 跨主机通信 | 需要端口映射 | 直接 Pod IP 通信 |
| NAT | 广泛使用 | 尽量避免 |
| 服务发现 | 手动配置/外部方案 | 内置 Service/DNS |
| 网络隔离 | 有限 | NetworkPolicy |

## 三、CNI（容器网络接口）

### 3.1 CNI 架构

```
┌─────────────────────────────────────────────────────────────┐
│                     CNI 架构                                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Kubernetes                                                 │
│       │                                                     │
│       ▼ kubelet calls CNI                                   │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                 CNI Plugin (二进制)                  │   │
│  │              (bridge/calico/cilium等)                │   │
│  └─────────────────────────────────────────────────────┘   │
│       │                                                     │
│       │ Add/Del/Check                                       │
│       ▼                                                     │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                 Network Namespace                    │   │
│  │              (veth pair / 网络设备)                   │   │
│  └─────────────────────────────────────────────────────┘   │
│       │                                                     │
│       ▼                                                     │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                 底层网络基础设施                       │   │
│  │         (Linux Bridge/OVS/VXLAN/BGP等)               │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 CNI 配置

```json
// /etc/cni/net.d/10-calico.conflist
{
  "name": "k8s-pod-network",
  "cniVersion": "0.3.1",
  "plugins": [
    {
      "type": "calico",
      "log_level": "info",
      "datastore_type": "kubernetes",
      "nodename": "node-1",
      "mtu": 1440,
      "ipam": {
        "type": "calico-ipam",
        "assign_ipv4": "true",
        "ipv4_pools": ["10.244.0.0/16"]
      },
      "policy": {
        "type": "k8s"
      },
      "kubernetes": {
        "kubeconfig": "/etc/cni/net.d/calico-kubeconfig"
      }
    },
    {
      "type": "portmap",
      "snat": true,
      "capabilities": {"portMappings": true}
    }
  ]
}
```

### 3.3 主流 CNI 插件对比

| CNI 插件 | 数据平面 | 网络模式 | 特点 | 适用场景 |
|----------|----------|----------|------|----------|
| **Flannel** | VXLAN/UDP | Overlay | 简单轻量 | 中小规模集群 |
| **Calico** | eBPF/BGP | Overlay/Underlay | 功能丰富，性能高 | 大规模生产环境 |
| **Cilium** | eBPF | Overlay | 安全可视，服务网格 | 云原生安全 |
| **Weave Net** | VXLAN | Overlay | 自动发现，易用 | 快速部署 |
| **OVN-Kubernetes** | OVS | Overlay | 企业级功能 | OpenStack 环境 |
| **Antrea** | OVS | Overlay | VMware 支持 | Tanzu 环境 |

## 四、Pod 网络详解

### 4.1 Pod 网络创建流程

```
┌─────────────────────────────────────────────────────────────┐
│              Pod 网络创建流程 (以 Calico 为例)                │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. kubelet 创建 Pod                                        │
│       │                                                     │
│       ▼                                                     │
│  2. 创建 Pause 容器 (infra container)                        │
│     - 创建 Network Namespace                                │
│     - 设置 loopback 接口                                    │
│       │                                                     │
│       ▼                                                     │
│  3. 调用 CNI Add 操作                                       │
│     /opt/cni/bin/calico \\                                   │
│       --command=ADD \\                                       │
│       --netns=/proc/<pid>/ns/net \\                          │
│       --ifname=eth0                                         │
│       │                                                     │
│       ▼                                                     │
│  4. CNI 插件分配 IP                                          │
│     - 从 IPAM 获取可用 IP                                    │
│     - 创建 veth pair                                        │
│       │                                                     │
│       ▼                                                     │
│  5. 配置网络接口                                             │
│     ┌─────────────────┐         ┌──────────────────────┐   │
│     │  Pod Namespace  │         │    Host Network      │   │
│     │  ┌───────────┐  │         │  ┌────────────────┐  │   │
│     │  │   eth0    │◄─┼──veth───┼─►│ calixxxxx      │  │   │
│     │  │ 10.244.1.2│  │  pair   │  │ (veth 另一端)   │  │   │
│     │  └───────────┘  │         │  └────────────────┘  │   │
│     │       │         │         │         │            │   │
│     │  ┌────┴────┐    │         │    ┌────┴────┐       │   │
│     │  │  lo     │    │         │    │ 路由表   │       │   │
│     │  │127.0.0.1│    │         │    │         │       │   │
│     │  └─────────┘    │         │    └─────────┘       │   │
│     └─────────────────┘         └──────────────────────┘   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 Pod 网络诊断

```bash
# 查看 Pod IP
kubectl get pod <pod-name> -o wide

# 进入 Pod 查看网络配置
kubectl exec -it <pod-name> -- /bin/sh
ip addr
ip route
netstat -tlnp

# 查看节点上的 Pod 网络接口
ip addr | grep cali
ip link show type veth

# 查看路由表
ip route show
route -n

# 查看 iptables 规则
iptables -t nat -L -n -v
iptables -t filter -L -n -v

# 测试 Pod 连通性
kubectl run -it --rm debug --image=nicolaka/netshoot --restart=Never -- ping <pod-ip>

# 抓包分析
kubectl debug -it <pod-name> --image=nicolaka/netshoot --target=<container> -- tcpdump -i eth0 -w /tmp/capture.pcap
```

## 五、Service 网络

### 5.1 Service 类型

```
┌─────────────────────────────────────────────────────────────┐
│                  Kubernetes Service 类型                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. ClusterIP (默认)                                         │
│  ┌───────────────────────────────────────────────────────┐  │
│  │     Pod A          Pod B          Pod C              │  │
│  │    10.244.1.2    10.244.1.3    10.244.2.4           │  │
│  │        │              │              │               │  │
│  │        └──────────────┼──────────────┘               │  │
│  │                       │                             │  │
│  │              ┌────────▼────────┐                     │  │
│  │              │  Service:web    │                     │  │
│  │              │  10.96.123.45   │                     │  │
│  │              │  ClusterIP      │                     │  │
│  │              └─────────────────┘                     │  │
│  │  仅集群内部可访问                                       │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  2. NodePort                                                │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  External Client                                       │  │
│  │       │                                               │  │
│  │       ▼                                               │  │
│  │  Node IP:30080 ──────┬──────────────────────┐        │  │
│  │                      │                      │        │  │
│  │              ┌───────┴───────┐      ┌───────┴───────┐│  │
│  │              │   Node 1      │      │   Node 2      ││  │
│  │              │  192.168.1.10 │      │  192.168.1.11 ││  │
│  │              │  Port 30080   │      │  Port 30080   ││  │
│  │              └───────┬───────┘      └───────┬───────┘│  │
│  │                      │                      │        │  │
│  │              ┌───────┴───────┐      ┌───────┴───────┐│  │
│  │              │   Pod A       │      │   Pod B       ││  │
│  │              └───────────────┘      └───────────────┘│  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  3. LoadBalancer                                            │
│  ┌───────────────────────────────────────────────────────┐  │
│  │         Cloud Load Balancer (AWS ELB/GCP LB/Azure LB) │  │
│  │                        │                              │  │
│  │                        ▼                              │  │
│  │              ┌─────────────────────┐                  │  │
│  │              │   Service:web       │                  │  │
│  │              │   Type:LoadBalancer │                  │  │
│  │              │   External-IP: x.x.x│                  │  │
│  │              └──────────┬──────────┘                  │  │
│  │                         │                             │  │
│  │              ┌──────────┴──────────┐                  │  │
│  │              │      Pod Pool       │                  │  │
│  │              └─────────────────────┘                  │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  4. ExternalName                                            │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Service:database                                     │  │
│  │  Type:ExternalName                                    │  │
│  │  ExternalName:db.example.com                          │  │
│  │                                                       │  │
│  │  Pod ──► database.default.svc.cluster.local           │  │
│  │              │                                        │  │
│  │              ▼ CNAME                                  │  │
│  │         db.example.com                                │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 kube-proxy 工作原理

```
┌─────────────────────────────────────────────────────────────┐
│                kube-proxy 模式对比                           │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  1. iptables 模式 (默认)                                     │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Service: 10.96.0.1:443                               │  │
│  │       │                                               │  │
│  │       ▼ KUBE-SVC-XXX 链                                │  │
│  │  ┌─────────────────────────────────────────────┐      │  │
│  │  │ KUBE-SVC-XXX                                │      │  │
│  │  │   ├─ KUBE-SEP-AAA ──► 10.244.1.2:8443 (33%) │      │  │
│  │  │   ├─ KUBE-SEP-BBB ──► 10.244.1.3:8443 (33%) │      │  │
│  │  │   └─ KUBE-SEP-CCC ──► 10.244.2.4:8443 (34%) │      │  │
│  │  └─────────────────────────────────────────────┘      │  │
│  │  特点: 内核态处理，性能好，但大量规则时更新慢               │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  2. IPVS 模式                                                │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Service: 10.96.0.1:443                               │  │
│  │       │                                               │  │
│  │       ▼ IP Virtual Server                              │  │
│  │  ┌─────────────────────────────────────────────┐      │  │
│  │  │ TCP  10.96.0.1:443 rr                       │      │  │
│  │  │   ├─ 10.244.1.2:8443   Masq    1    0       │      │  │
│  │  │   ├─ 10.244.1.3:8443   Masq    1    0       │      │  │
│  │  │   └─ 10.244.2.4:8443   Masq    1    0       │      │  │
│  │  └─────────────────────────────────────────────┘      │  │
│  │  特点: 内核态哈希表，支持多种负载均衡算法，性能最佳          │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
│  3. userspace 模式 (已废弃)                                  │  │
│  4. nftables 模式 (实验性)                                   │  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 5.3 Service 配置示例

```yaml
# ClusterIP Service
apiVersion: v1
kind: Service
metadata:
  name: web-service
  namespace: default
spec:
  type: ClusterIP
  selector:
    app: web
  ports:
  - port: 80
    targetPort: 8080
    protocol: TCP
    name: http
  sessionAffinity: ClientIP  # 会话保持
  sessionAffinityConfig:
    clientIP:
      timeoutSeconds: 10800

---
# NodePort Service
apiVersion: v1
kind: Service
metadata:
  name: web-nodeport
spec:
  type: NodePort
  selector:
    app: web
  ports:
  - port: 80
    targetPort: 8080
    nodePort: 30080  # 30000-32767

---
# LoadBalancer Service
apiVersion: v1
kind: Service
metadata:
  name: web-lb
  annotations:
    service.beta.kubernetes.io/aws-load-balancer-type: "nlb"
    service.beta.kubernetes.io/aws-load-balancer-backend-protocol: "tcp"
spec:
  type: LoadBalancer
  selector:
    app: web
  ports:
  - port: 443
    targetPort: 8443
  externalTrafficPolicy: Local  # 保留客户端源 IP

---
# ExternalName Service
apiVersion: v1
kind: Service
metadata:
  name: external-db
spec:
  type: ExternalName
  externalName: db.production.example.com
```

## 六、Ingress 与网关

### 6.1 Ingress 架构

```
┌─────────────────────────────────────────────────────────────┐
│                    Ingress 架构                              │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  External Traffic                                            │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │            Ingress Controller                        │    │
│  │  ┌─────────────────────────────────────────────┐    │    │
│  │  │  Nginx/Traefik/HAProxy/Envoy                │    │    │
│  │  │                                             │    │    │
│  │  │  Routing Rules:                             │    │    │
│  │  │  ┌─────────────────────────────────────┐    │    │    │
│  │  │  │ api.example.com  ──► api-service   │    │    │    │
│  │  │  │ www.example.com  ──► web-service   │    │    │    │
│  │  │  │ /api/v1          ──► api-v1        │    │    │    │
│  │  │  │ /static/*        ──► static-assets │    │    │    │
│  │  │  └─────────────────────────────────────┘    │    │    │
│  │  └─────────────────────────────────────────────┘    │    │
│  └──────────────────────────┬──────────────────────────┘    │
│                             │                                │
│              ┌──────────────┼──────────────┐                 │
│              │              │              │                 │
│              ▼              ▼              ▼                 │
│        ┌─────────┐    ┌─────────┐    ┌─────────┐            │
│        │ api-svc │    │ web-svc │    │static-svc│            │
│        │  Cluster│    │ Cluster │    │ Cluster │            │
│        │    IP   │    │    IP   │    │    IP   │            │
│        └────┬────┘    └────┬────┘    └────┬────┘            │
│             │              │              │                  │
│             ▼              ▼              ▼                  │
│        ┌─────────┐    ┌─────────┐    ┌─────────┐            │
│        │ Pod A   │    │ Pod B   │    │ Pod C   │            │
│        │ Pod A2  │    │ Pod B2  │    │ Pod C2  │            │
│        └─────────┘    └─────────┘    └─────────┘            │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 Ingress 配置示例

```yaml
# Nginx Ingress Controller
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: app-ingress
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/rate-limit: "100"
    nginx.ingress.kubernetes.io/rate-limit-window: "1m"
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
spec:
  ingressClassName: nginx
  tls:
  - hosts:
    - api.example.com
    - www.example.com
    secretName: example-tls
  rules:
  - host: api.example.com
    http:
      paths:
      - path: /v1
        pathType: Prefix
        backend:
          service:
            name: api-v1
            port:
              number: 80
      - path: /v2
        pathType: Prefix
        backend:
          service:
            name: api-v2
            port:
              number: 80
  - host: www.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: web-service
            port:
              number: 80

---
# 基于路径的路由
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: path-based-ingress
  annotations:
    nginx.ingress.kubernetes.io/use-regex: "true"
spec:
  ingressClassName: nginx
  rules:
  - host: app.example.com
    http:
      paths:
      - path: /api(/|$)(.*)
        pathType: ImplementationSpecific
        backend:
          service:
            name: api-service
            port:
              number: 8080
      - path: /static/(.*)
        pathType: ImplementationSpecific
        backend:
          service:
            name: static-service
            port:
              number: 80
```

### 6.3 Gateway API (下一代 Ingress)

```yaml
# Gateway API 示例
apiVersion: gateway.networking.k8s.io/v1
kind: Gateway
metadata:
  name: example-gateway
spec:
  gatewayClassName: nginx
  listeners:
  - name: http
    protocol: HTTP
    port: 80
  - name: https
    protocol: HTTPS
    port: 443
    tls:
      certificateRefs:
      - name: example-tls

---
apiVersion: gateway.networking.k8s.io/v1
kind: HTTPRoute
metadata:
  name: example-route
spec:
  parentRefs:
  - name: example-gateway
  hostnames:
  - "api.example.com"
  rules:
  - matches:
    - path:
        type: PathPrefix
        value: /v1
    backendRefs:
    - name: api-v1
      port: 80
  - matches:
    - path:
        type: PathPrefix
        value: /v2
    backendRefs:
    - name: api-v2
      port: 80
```

## 七、网络策略（NetworkPolicy）

### 7.1 默认网络策略

```yaml
# 默认拒绝所有入站流量
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: default-deny-ingress
  namespace: production
spec:
  podSelector: {}
  policyTypes:
  - Ingress

---
# 默认拒绝所有出站流量
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: default-deny-egress
  namespace: production
spec:
  podSelector: {}
  policyTypes:
  - Egress

---
# 默认拒绝所有流量
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: default-deny-all
  namespace: production
spec:
  podSelector: {}
  policyTypes:
  - Ingress
  - Egress
```

### 7.2 应用层网络策略

```yaml
# 允许前端访问后端
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: backend-allow-frontend
  namespace: production
spec:
  podSelector:
    matchLabels:
      app: backend
      tier: api
  policyTypes:
  - Ingress
  ingress:
  - from:
    - podSelector:
        matchLabels:
          app: frontend
          tier: web
    ports:
    - protocol: TCP
      port: 8080

---
# 允许后端访问数据库
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: db-allow-backend
  namespace: production
spec:
  podSelector:
    matchLabels:
      app: postgres
      tier: database
  policyTypes:
  - Ingress
  ingress:
  - from:
    - podSelector:
        matchLabels:
          app: backend
          tier: api
    ports:
    - protocol: TCP
      port: 5432

---
# 允许出站到特定 CIDR
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: allow-external-api
  namespace: production
spec:
  podSelector:
    matchLabels:
      app: backend
  policyTypes:
  - Egress
  egress:
  - to:
    - ipBlock:
        cidr: 203.0.113.0/24
    ports:
    - protocol: TCP
      port: 443
  # 允许 DNS 查询
  - to:
    - namespaceSelector: {}
    ports:
    - protocol: UDP
      port: 53
    - protocol: TCP
      port: 53
```

## 八、CoreDNS

### 8.1 DNS 解析流程

```
┌─────────────────────────────────────────────────────────────┐
│                  Kubernetes DNS 解析流程                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Pod DNS 配置                                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  /etc/resolv.conf                                    │   │
│  │  nameserver 10.96.0.10  (Cluster DNS IP)             │   │
│  │  search default.svc.cluster.local svc.cluster.local  │   │
│  │  options ndots:5                                     │   │
│  └─────────────────────────────────────────────────────┘   │
│                              │                               │
│                              ▼                               │
│  ┌─────────────────────────────────────────────────────┐   │
│  │              CoreDNS (kube-system)                   │   │
│  │  ┌─────────────────────────────────────────────┐    │   │
│  │  │  Corefile                                    │    │   │
│  │  │    kubernetes cluster.local in-addr.arpa {  │    │   │
│  │  │      pods insecure                          │    │   │
│  │  │      fallthrough in-addr.arpa ip6.arpa      │    │   │
│  │  │    }                                        │    │   │
│  │  │    forward . /etc/resolv.conf {             │    │   │
│  │  │      policy sequential                      │    │   │
│  │  │    }                                        │    │   │
│  │  └─────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────┘   │
│                              │                               │
│              ┌───────────────┴───────────────┐               │
│              │                               │               │
│              ▼                               ▼               │
│  ┌─────────────────────┐      ┌─────────────────────┐       │
│  │ 集群内部 Service     │      │ 外部 DNS 服务器      │       │
│  │ web.default.svc.    │      │ 8.8.8.8             │       │
│  │ cluster.local       │      │ 上游 DNS            │       │
│  └─────────────────────┘      └─────────────────────┘       │
│                                                              │
│  DNS 命名规范:                                               │
│  - Service: <service>.<namespace>.svc.cluster.local         │
│  - Pod IP: <ip-with-dashes>.<namespace>.pod.cluster.local   │
│  - Headless: <pod-name>.<service>.<namespace>.svc...        │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 8.2 CoreDNS 配置

```yaml
# CoreDNS ConfigMap
apiVersion: v1
kind: ConfigMap
metadata:
  name: coredns
  namespace: kube-system
data:
  Corefile: |
    .:53 {
        errors
        health {
           lameduck 5s
        }
        ready
        kubernetes cluster.local in-addr.arpa ip6.arpa {
           pods insecure
           fallthrough in-addr.arpa ip6.arpa
           ttl 30
        }
        prometheus :9153
        forward . /etc/resolv.conf {
           max_concurrent 1000
        }
        cache 30
        loop
        reload
        loadbalance
    }
    # 自定义域名
    example.com:53 {
        errors
        cache 30
        forward . 10.0.0.10
    }
```

## 九、网络故障排查

### 9.1 常用排查命令

```bash
# 检查 Pod 网络
kubectl get pods -o wide
kubectl get svc -o wide
kubectl get endpoints

# 检查 CNI 状态
kubectl get pods -n kube-system -l k8s-app=calico-node
kubectl logs -n kube-system -l k8s-app=calico-node

# 检查 kube-proxy
kubectl get pods -n kube-system -l k8s-app=kube-proxy
kubectl logs -n kube-system -l k8s-app=kube-proxy

# 检查 CoreDNS
kubectl get pods -n kube-system -l k8s-app=kube-dns
kubectl logs -n kube-system -l k8s-app=kube-dns

# 网络诊断工具 Pod
kubectl run -it --rm debug --image=nicolaka/netshoot --restart=Never

# 在诊断 Pod 中执行
# DNS 测试
dig kubernetes.default.svc.cluster.local
nslookup web-service.default.svc.cluster.local

# 连通性测试
ping <pod-ip>
curl -v http://web-service.default.svc.cluster.local

# 路由追踪
traceroute <pod-ip>

# 抓包
tcpdump -i eth0 -w /tmp/capture.pcap
```

### 9.2 常见网络问题

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| Pod 无法访问 Service | kube-proxy 故障/iptables 规则错误 | 检查 kube-proxy，重启或切换模式 |
| DNS 解析失败 | CoreDNS 异常/网络策略阻断 | 检查 CoreDNS Pod，检查 NetworkPolicy |
| 跨节点 Pod 不通 | CNI 配置错误/Overlay 网络故障 | 检查 CNI 插件状态，检查隧道 |
| 外部无法访问 | LoadBalancer 未分配/安全组 | 检查云厂商 LB 配置，检查安全组 |
| 高延迟 | kube-proxy iptables 模式 | 切换到 IPVS 或 eBPF 模式 |

## 十、总结

Kubernetes 网络是一个复杂的主题，涉及多个层次：

1. **Pod 网络**：CNI 插件提供 Pod IP 和跨节点通信能力
2. **Service 网络**：kube-proxy 实现服务发现和负载均衡
3. **Ingress/Gateway**：集群入口流量管理
4. **NetworkPolicy**：网络隔离和访问控制
5. **DNS**：服务发现和域名解析

选择合适的 CNI 插件和网络架构对于集群性能和安全性至关重要。在生产环境中，建议：

- 使用 Calico 或 Cilium 等功能丰富的 CNI
- 启用 NetworkPolicy 进行网络隔离
- 配置合适的 Service 类型和 Ingress
- 定期监控网络性能和连通性


---

## 相关主题

- [Kubernetes架构深度分析](../cloud-computing/Kubernetes架构深度分析.md)
- [K8s存储](./K8s存储.md)
- [CNI规范](https://www.cni.dev/)

## 参考资源

- [K8s网络文档](https://kubernetes.io/docs/concepts/cluster-administration/networking/)
