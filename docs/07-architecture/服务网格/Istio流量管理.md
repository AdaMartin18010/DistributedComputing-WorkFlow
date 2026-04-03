# Istio 流量管理

## 一、概述

Istio 是一个开源的服务网格平台，提供了流量管理、安全、可观测性等核心功能，无需对应用代码进行任何修改。流量管理是 Istio 最强大的特性之一，它允许运维人员控制服务之间的流量流动和 API 调用，实现 A/B 测试、金丝雀发布、负载均衡等功能。

## 二、Istio 流量管理架构

### 2.1 数据平面架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Istio 数据平面流量管理                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         Pod A                                    │    │
│  │  ┌─────────────┐     ┌─────────────┐     ┌────────────────────┐ │    │
│  │  │ Application │────►│    Envoy    │────►│   Other Services   │ │    │
│  │  │  (容器)      │     │   Sidecar   │     │                    │ │    │
│  │  └─────────────┘     │   (代理)     │     └────────────────────┘ │    │
│  │                      │             │                            │    │
│  │                      │ ┌─────────┐ │                            │    │
│  │                      │ │Listener │ │ 拦截入站流量                │    │
│  │                      │ │  :8080  │ │                            │    │
│  │                      │ ├─────────┤ │                            │    │
│  │                      │ │  Route  │ │ 路由规则                    │    │
│  │                      │ │  Table  │ │                            │    │
│  │                      │ ├─────────┤ │                            │    │
│  │                      │ │ Cluster │ │ 上游集群                    │    │
│  │                      │ │ Manager │ │                            │    │
│  │                      │ ├─────────┤ │                            │    │
│  │                      │ │ Endpoint│ │ 端点发现                    │    │
│  │                      │ │Discovery│ │                            │    │
│  │                      │ └─────────┘ │                            │    │
│  │                      └─────────────┘                            │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  Envoy 配置来源:                                                          │
│  ┌─────────────────┐     xDS API      ┌─────────────────┐               │
│  │   istiod        │◄────────────────►│   Envoy Sidecar │               │
│  │  (控制平面)      │  (LDS/RDS/CDS/   │   (数据平面)     │               │
│  │                 │   EDS/SDS)       │                 │               │
│  └─────────────────┘                  └─────────────────┘               │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 流量管理资源

```
┌─────────────────────────────────────────────────────────────────────────┐
│                 Istio 流量管理资源关系                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────┐                                                     │
│  │  Gateway        │  定义入口/出口流量入口                               │
│  │  (网关)         │  - 端口、协议、TLS                                   │
│  └────────┬────────┘                                                     │
│           │                                                              │
│           ▼                                                              │
│  ┌─────────────────┐                                                     │
│  │ VirtualService  │  定义路由规则                                        │
│  │ (虚拟服务)       │  - 匹配条件 (URI/Header)                            │
│  └────────┬────────┘  - 目标服务                                          │
│           │          - 流量权重                                           │
│           ▼                                                              │
│  ┌─────────────────┐                                                     │
│  │ DestinationRule │  定义服务策略                                        │
│  │ (目标规则)       │  - 负载均衡算法                                      │
│  └─────────────────┘  - 连接池设置                                         │
│                       - 熔断/异常检测                                     │
│                                                                          │
│  辅助资源:                                                                │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐          │
│  │ ServiceEntry    │  │  Sidecar        │  │ EnvoyFilter     │          │
│  │ (外部服务)       │  │ (Sidecar配置)   │  │ (Envoy扩展)     │          │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘          │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## 三、Gateway 配置

### 3.1 入口网关（Ingress Gateway）

```yaml
# gateway.yaml
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: public-gateway
  namespace: istio-system
spec:
  selector:
    istio: ingressgateway  # 选择 Ingress Gateway Pod
  servers:
  # HTTP 端口
  - port:
      number: 80
      name: http
      protocol: HTTP
    hosts:
    - "*.example.com"
    - "api.example.com"
    # HTTP 重定向到 HTTPS
    tls:
      httpsRedirect: true

  # HTTPS 端口
  - port:
      number: 443
      name: https
      protocol: HTTPS
    tls:
      mode: SIMPLE
      credentialName: example-tls-secret  # 引用 TLS Secret
      minProtocolVersion: TLSV1_2
      cipherSuites:
      - ECDHE-RSA-AES256-GCM-SHA384
      - ECDHE-RSA-AES128-GCM-SHA256
    hosts:
    - "api.example.com"
    - "app.example.com"

  # TCP 端口
  - port:
      number: 3306
      name: mysql
      protocol: TCP
    hosts:
    - "db.example.com"

---
# 使用 cert-manager 自动管理证书
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: auto-tls-gateway
  namespace: istio-system
  annotations:
    cert-manager.io/cluster-issuer: letsencrypt-prod
spec:
  selector:
    istio: ingressgateway
  servers:
  - port:
      number: 443
      name: https
      protocol: HTTPS
    tls:
      mode: SIMPLE
      credentialName: auto-tls-cert  # cert-manager 自动创建
    hosts:
    - "api.example.com"
```

### 3.2 出口网关（Egress Gateway）

```yaml
# egress-gateway.yaml
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: egress-gateway
  namespace: istio-system
spec:
  selector:
    istio: egressgateway
  servers:
  - port:
      number: 443
      name: https
      protocol: HTTPS
    hosts:
    - "external-api.com"
    tls:
      mode: ISTIO_MUTUAL

---
# 外部服务访问策略
apiVersion: networking.istio.io/v1beta1
kind: ServiceEntry
metadata:
  name: external-api
spec:
  hosts:
  - external-api.com
  ports:
  - number: 443
    name: https
    protocol: HTTPS
  resolution: DNS
  location: MESH_EXTERNAL

---
# 通过 Egress Gateway 路由外部流量
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: external-api-route
spec:
  hosts:
  - external-api.com
  gateways:
  - mesh  # 内部网格流量
  - egress-gateway
  tls:
  - match:
    - gateways:
      - mesh
      port: 443
      sniHosts:
      - external-api.com
    route:
    - destination:
        host: istio-egressgateway.istio-system.svc.cluster.local
        port:
          number: 443
      weight: 100
  - match:
    - gateways:
      - egress-gateway
      port: 443
      sniHosts:
      - external-api.com
    route:
    - destination:
        host: external-api.com
        port:
          number: 443
      weight: 100
```

## 四、VirtualService 路由

### 4.1 基础路由配置

```yaml
# virtualservice-basic.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: api-route
  namespace: production
spec:
  hosts:
  - api.example.com
  gateways:
  - istio-system/public-gateway
  http:
  # 路由规则按顺序匹配
  # 规则 1: API v2 路由
  - match:
    - uri:
        prefix: /api/v2/
    route:
    - destination:
        host: api-v2
        port:
          number: 8080
    # 重写路径
    rewrite:
      uri: /
    # 请求超时
    timeout: 10s
    # 重试策略
    retries:
      attempts: 3
      perTryTimeout: 2s
      retryOn: 5xx,connect-failure

  # 规则 2: API v1 路由（带 Header 匹配）
  - match:
    - uri:
        prefix: /api/v1/
      headers:
        x-api-version:
          exact: "1.0"
    route:
    - destination:
        host: api-v1
        port:
          number: 8080
    fault:
      delay:
        percentage:
          value: 0.1  # 0.1% 延迟注入
        fixedDelay: 5s

  # 规则 3: 默认路由
  - route:
    - destination:
        host: api-v1
        port:
          number: 8080
      weight: 90
    - destination:
        host: api-v2
        port:
          number: 8080
      weight: 10
    # 请求镜像（流量复制用于测试）
    mirror:
      host: api-v2-canary
      port:
        number: 8080
    mirrorPercentage:
      value: 10.0
```

### 4.2 金丝雀发布

```yaml
# canary-deployment.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: app-canary
spec:
  hosts:
  - app.example.com
  gateways:
  - istio-system/public-gateway
  http:
  - match:
    # 内部测试用户路由到新版本
    - headers:
        x-canary:
          exact: "true"
    route:
    - destination:
        host: app
        subset: v2
        port:
          number: 80

  - match:
    # 特定用户群体路由到新版本
    - headers:
        cookie:
          regex: "^(.*?;)?(user-group=beta)(;.*)?$"
    route:
    - destination:
        host: app
        subset: v2
        port:
          number: 80

  - route:
    # 按比例分流
    - destination:
        host: app
        subset: v1
        port:
          number: 80
      weight: 90
    - destination:
        host: app
        subset: v2
        port:
          number: 80
      weight: 10

---
# DestinationRule 定义子集
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: app-subsets
spec:
  host: app
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        maxRequestsPerConnection: 10
    loadBalancer:
      simple: LEAST_REQUEST
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
  subsets:
  - name: v1
    labels:
      version: v1
  - name: v2
    labels:
      version: v2
```

### 4.3 A/B 测试

```yaml
# ab-testing.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: ab-test
spec:
  hosts:
  - shop.example.com
  http:
  # 移动端用户 -> 版本 A
  - match:
    - headers:
        user-agent:
          regex: ".*Mobile.*"
    route:
    - destination:
        host: shop
        subset: version-a

  # 桌面端 + 注册用户 -> 版本 B
  - match:
    - headers:
        cookie:
          regex: "^(.*?;)?(logged_in=true)(;.*)?$"
    route:
    - destination:
        host: shop
        subset: version-b

  # 其他流量 -> 版本 A（控制组）
  - route:
    - destination:
        host: shop
        subset: version-a
```

### 4.4 高级匹配规则

```yaml
# advanced-matching.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: advanced-routing
spec:
  hosts:
  - api.example.com
  http:
  # 复杂匹配条件
  - match:
    # URI 前缀匹配
    - uri:
        prefix: /api/users
    # URI 正则匹配
    - uri:
        regex: "/api/v[0-9]+/orders"
    # 精确匹配
    - uri:
        exact: /api/health
    # Header 匹配
    headers:
      # 精确匹配
      x-request-id:
        exact: "abc-123"
      # 前缀匹配
      x-api-key:
        prefix: "prod-"
      # 正则匹配
      x-forwarded-for:
        regex: "^10\\..*"
      # 存在性检查
      x-custom-header:
        present: true
    # Query 参数匹配
    queryParams:
      version:
        exact: "2.0"
    # 端口匹配
    port: 8080
    # 来源标签匹配
    sourceLabels:
      app: frontend
      version: v1
    # 方法匹配
    method:
      exact: GET

    route:
    - destination:
        host: api-service
        port:
          number: 8080
```

## 五、DestinationRule 策略

### 5.1 负载均衡配置

```yaml
# loadbalancer.yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: api-lb-policy
spec:
  host: api-service
  trafficPolicy:
    loadBalancer:
      # 简单负载均衡策略
      # simple: ROUND_ROBIN | LEAST_CONN | RANDOM | PASSTHROUGH

      # 一致性哈希（会话保持）
      consistentHash:
        httpHeaderName: x-user-id
        # httpCookie:
        #   name: session
        #   ttl: 0s
        # useSourceIp: true
        # httpQueryParameterName: user
        minimumRingSize: 1024

      # 地域感知负载均衡
      localityLbSetting:
        enabled: true
        distribute:
        - from: us-west/*
          to:
            "us-west": 80
            "us-east": 20
        failover:
        - from: us-west
          to: us-east
```

### 5.2 连接池和熔断

```yaml
# circuit-breaker.yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: circuit-breaker
spec:
  host: api-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
        connectTimeout: 30ms
        tcpKeepalive:
          time: 300s
          interval: 75s
      http:
        http1MaxPendingRequests: 100
        http2MaxRequests: 1000
        maxRequestsPerConnection: 100
        maxRetries: 3

    loadBalancer:
      simple: LEAST_REQUEST

    # 熔断配置
    outlierDetection:
      # 连续错误次数触发熔断
      consecutiveErrors: 5
      # 错误率阈值
      consecutiveGatewayErrors: 5
      consecutive5xxErrors: 5
      # 检测间隔
      interval: 10s
      # 基础驱逐时间
      baseEjectionTime: 30s
      # 最大驱逐百分比
      maxEjectionPercent: 50
      # 最小健康比例
      minHealthPercent: 40
      # 成功标准（恢复条件）
      successRate:
        minimumHosts: 3
        requestVolume: 100
        standardDeviationFactor: 1.4
```

### 5.3 TLS 配置

```yaml
# tls-policy.yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: mtls-policy
spec:
  host: api-service
  trafficPolicy:
    tls:
      # 客户端证书模式
      mode: ISTIO_MUTUAL
      # mode: DISABLE
      # mode: SIMPLE
      # mode: MUTUAL

      # 客户端证书（非 Istio 自动 mTLS）
      # clientCertificate: /etc/certs/client.pem
      # privateKey: /etc/certs/key.pem
      # caCertificates: /etc/certs/ca.pem

      # SNI
      # sni: api-service

      # 证书验证
      subjectAltNames:
      - api-service.default.svc.cluster.local
```

## 六、流量镜像和故障注入

### 6.1 流量镜像

```yaml
# traffic-mirroring.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: traffic-mirror
spec:
  hosts:
  - api-service
  http:
  - route:
    - destination:
        host: api-service
        subset: production
      weight: 100
    # 流量镜像到测试环境
    mirror:
      host: api-service
      subset: testing
    mirrorPercentage:
      value: 10.0  # 镜像 10% 的流量
```

### 6.2 故障注入

```yaml
# fault-injection.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: fault-injection
spec:
  hosts:
  - api-service
  http:
  # 延迟注入
  - fault:
      delay:
        percentage:
          value: 10.0  # 10% 的请求
        fixedDelay: 5s
        # exponentialDelay:
        #   base: 100ms
        #   growthRate: 2
        #   maxDelay: 10s
    route:
    - destination:
        host: api-service

  # 错误注入
  - fault:
      abort:
        percentage:
          value: 5.0  # 5% 的请求
        httpStatus: 503
        # grpcStatus: "14"
    route:
    - destination:
        host: api-service
```

## 七、常用命令

```bash
# ========== Gateway 管理 ==========
# 查看 Gateway
kubectl get gateway -A
kubectl describe gateway public-gateway -n istio-system

# 查看 Gateway 状态
istioctl proxy-config listener deploy/istio-ingressgateway -n istio-system

# ========== VirtualService 管理 ==========
# 应用 VirtualService
kubectl apply -f virtualservice.yaml

# 查看路由配置
istioctl proxy-config route deploy/productpage-v1

# 测试路由
istioctl dashboard envoy deploy/productpage-v1

# ========== DestinationRule 管理 ==========
# 查看 DestinationRule
kubectl get destinationrule -A

# 查看集群配置
istioctl proxy-config cluster deploy/productpage-v1

# 查看端点
istioctl proxy-config endpoint deploy/productpage-v1

# ========== 流量分析 ==========
# 查看流量指标
istioctl dashboard prometheus

# 查看 Kiali 服务图
istioctl dashboard kiali

# 查看 Jaeger 追踪
istioctl dashboard jaeger

# ========== 调试命令 ==========
# 检查配置
istioctl analyze

# 检查特定命名空间
istioctl analyze -n production

# 验证代理配置
istioctl proxy-status

# 查看代理差异
istioctl proxy-status deploy/productpage-v1
```

## 八、总结

Istio 流量管理提供了丰富的流量控制能力：

1. **Gateway**：定义流量入口，支持多协议和 TLS
2. **VirtualService**：灵活的路由规则，支持金丝雀、A/B 测试
3. **DestinationRule**：服务策略，包括负载均衡、熔断、TLS
4. **高级功能**：流量镜像、故障注入、重试、超时

在生产环境中使用 Istio 流量管理时：

- 从小规模开始，逐步扩大使用范围
- 充分测试路由规则，避免流量异常
- 监控服务网格指标，及时发现异常
- 制定故障恢复预案
