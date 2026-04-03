# Kustomize 配置管理

## 一、概述

Kustomize 是 Kubernetes 原生的配置管理工具，自 Kubernetes 1.14 版本起被集成到 kubectl 中。与 Helm 的模板化方式不同，Kustomize 采用"配置即数据"的理念，通过 overlay 和 patch 机制来管理不同环境的配置差异，保持原始 YAML 文件的完整性和可读性。

## 二、Kustomize vs Helm

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  Kustomize vs Helm 对比                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                          Helm                                    │    │
│  │                                                                  │    │
│  │  ┌──────────┐      ┌──────────┐      ┌──────────────────────┐   │    │
│  │  │  Template│  +   │  Values  │  →   │  Rendered YAML       │   │    │
│  │  │  {{ . }} │      │  .yaml   │      │  (运行时渲染)         │   │    │
│  │  └──────────┘      └──────────┘      └──────────────────────┘   │    │
│  │                                                                  │    │
│  │  特点:                                                           │    │
│  │  - 基于 Go Template                                              │    │
│  │  - 运行时渲染                                                    │    │
│  │  - 支持复杂逻辑 (if/else, range, etc.)                           │    │
│  │  - 适合可复用的应用包                                            │    │
│  │                                                                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                        Kustomize                                 │    │
│  │                                                                  │    │
│  │  ┌──────────┐      ┌──────────┐      ┌──────────────────────┐   │    │
│  │  │   Base   │  +   │ Overlay  │  →   │  Modified YAML       │   │    │
│  │  │  (基础)  │      │ (补丁)   │      │  (纯 YAML，无模板)    │   │    │
│  │  └──────────┘      └──────────┘      └──────────────────────┘   │    │
│  │                                                                  │    │
│  │  特点:                                                           │    │
│  │  - 纯 YAML，无模板语法                                           │    │
│  │  - 声明式 Patch 机制                                             │    │
│  │  - 继承和覆盖而非渲染                                            │    │
│  │  - 适合多环境配置管理                                            │    │
│  │  - 原生集成 kubectl                                              │    │
│  │                                                                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  选择建议:                                                                │
│  - 需要打包分发应用 → Helm                                             │
│  - 需要复杂模板逻辑 → Helm                                             │
│  - 管理内部多环境配置 → Kustomize                                      │
│  - 追求 YAML 可读性 → Kustomize                                        │
│  - 不需要额外工具 → Kustomize (kubectl 内置)                           │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## 三、Kustomize 核心概念

### 3.1 基础目录结构

```
# Kustomize 标准目录结构
kustomize/
├── base/                          # 基础配置
│   ├── kustomization.yaml         # Kustomize 配置
│   ├── deployment.yaml            # 基础资源
│   ├── service.yaml
│   └── configmap.yaml
└── overlays/                      # 环境覆盖
    ├── development/               # 开发环境
    │   ├── kustomization.yaml
    │   ├── deployment-patch.yaml
    │   └── configmap-patch.yaml
    ├── staging/                   # 测试环境
    │   ├── kustomization.yaml
    │   ├── deployment-patch.yaml
    │   ├── ingress.yaml
    │   └── hpa.yaml
    └── production/                # 生产环境
        ├── kustomization.yaml
        ├── deployment-patch.yaml
        ├── pdb.yaml
        └── network-policy.yaml
```

### 3.2 Base 基础配置

```yaml
# base/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-app
  labels:
    app: web-app
spec:
  replicas: 1
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
        image: myapp:latest
        ports:
        - containerPort: 8080
        resources:
          requests:
            cpu: 100m
            memory: 128Mi

---
# base/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: web-app
spec:
  selector:
    app: web-app
  ports:
  - port: 80
    targetPort: 8080

---
# base/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

metadata:
  name: web-app-base

# 包含的资源文件
resources:
  - deployment.yaml
  - service.yaml

# 通用标签
commonLabels:
  app.kubernetes.io/name: web-app
  app.kubernetes.io/managed-by: kustomize

# 通用注解
commonAnnotations:
  app.kubernetes.io/description: "Web Application Base"

# 命名空间前缀
namePrefix: base-

# 命名空间
namespace: default

# 镜像标签替换
images:
  - name: myapp
    newName: registry.example.com/myapp
    newTag: v1.0.0
```

### 3.3 Overlay 环境覆盖

```yaml
# overlays/development/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

metadata:
  name: web-app-dev

# 引用基础配置
resources:
  - ../../base

# 开发环境特定资源
resources:
  - ../../base
  - node-port-service.yaml

# 命名空间
namespace: dev

# 名称前缀
namePrefix: dev-

# 通用标签
commonLabels:
  environment: development
  tier: dev

# 镜像覆盖
images:
  - name: myapp
    newTag: dev-latest

# 配置映射生成
configMapGenerator:
  - name: app-config
    literals:
      - LOG_LEVEL=debug
      - DEBUG=true
      - API_URL=http://localhost:8080

# Secret 生成
secretGenerator:
  - name: app-secrets
    literals:
      - API_KEY=dev-secret-key
    options:
      disableNameSuffixHash: true

# 补丁文件
patchesStrategicMerge:
  - deployment-patch.yaml
  - service-patch.yaml

# 使用 Json Patch
patchesJson6902:
  - target:
      group: apps
      version: v1
      kind: Deployment
      name: web-app
    path: replicas-patch.yaml

# 副本数设置
replicas:
  - name: web-app
    count: 1
```

```yaml
# overlays/development/deployment-patch.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-app
spec:
  template:
    spec:
      containers:
      - name: app
        resources:
          requests:
            cpu: 50m
            memory: 64Mi
          limits:
            cpu: 200m
            memory: 256Mi
        env:
        - name: NODE_ENV
          value: development
        - name: LOG_LEVEL
          value: debug
```

```yaml
# overlays/development/service-patch.yaml
apiVersion: v1
kind: Service
metadata:
  name: web-app
spec:
  type: NodePort
  ports:
  - port: 80
    targetPort: 8080
    nodePort: 30080
```

### 3.4 生产环境配置

```yaml
# overlays/production/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

metadata:
  name: web-app-prod

resources:
  - ../../base
  - ingress.yaml
  - hpa.yaml
  - pdb.yaml

namespace: production

namePrefix: prod-

commonLabels:
  environment: production
  tier: production

commonAnnotations:
  contact: "ops@example.com"
  pager: "oncall@example.com"

images:
  - name: myapp
    newName: registry.example.com/myapp
    newTag: v2.1.0

configMapGenerator:
  - name: app-config
    behavior: merge  # 合并而非替换
    literals:
      - LOG_LEVEL=warn
      - DEBUG=false
      - API_URL=https://api.example.com

secretGenerator:
  - name: app-secrets
    envs:
      - secrets.env  # 从文件加载

patchesStrategicMerge:
  - deployment-patch.yaml

replicas:
  - name: web-app
    count: 5
```

```yaml
# overlays/production/deployment-patch.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-app
spec:
  template:
    metadata:
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
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
                  - web-app
              topologyKey: kubernetes.io/hostname
      containers:
      - name: app
        resources:
          requests:
            cpu: 500m
            memory: 512Mi
          limits:
            cpu: 1000m
            memory: 1Gi
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
```

```yaml
# overlays/production/hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: web-app
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: web-app
  minReplicas: 5
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
```

```yaml
# overlays/production/pdb.yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: web-app
spec:
  minAvailable: 80%
  selector:
    matchLabels:
      app: web-app
```

## 四、高级功能

### 4.1 ConfigMap 和 Secret 生成器

```yaml
# kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

# ConfigMap 生成
configMapGenerator:
  # 从字面量生成
  - name: app-config
    literals:
      - DATABASE_URL=postgres://localhost:5432/mydb
      - CACHE_SIZE=1000
    options:
      disableNameSuffixHash: false  # 添加 hash 后缀，触发 Pod 滚动更新

  # 从文件生成
  - name: nginx-config
    files:
      - nginx.conf
      - mime.types

  # 从目录生成
  - name: config-dir
    envs:
      - config.env

  # 合并现有 ConfigMap
  - name: shared-config
    behavior: merge
    literals:
      - EXTRA_VAR=value

# Secret 生成
secretGenerator:
  - name: db-credentials
    literals:
      - username=admin
      - password=secret123
    type: Opaque

  - name: tls-cert
    files:
      - tls.crt=cert.pem
      - tls.key=key.pem
    type: kubernetes.io/tls

  # 从环境文件生成
  - name: app-secrets
    envs:
      - secrets.env
```

### 4.2 JSON Patch 6902

```yaml
# patchesJson6902 配置
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
  - ../../base

patchesJson6902:
  # 修改 Deployment 副本数
  - target:
      group: apps
      version: v1
      kind: Deployment
      name: web-app
    patch: |
      - op: replace
        path: /spec/replicas
        value: 10

  # 添加环境变量
  - target:
      version: v1
      kind: Deployment
      name: web-app
    patch: |
      - op: add
        path: /spec/template/spec/containers/0/env/-
        value:
          name: NEW_VAR
          value: new_value

  # 从文件加载 patch
  - target:
      version: v1
      kind: Service
      name: web-app
    path: service-patch.yaml
```

```yaml
# service-patch.yaml (JSON Patch 格式)
- op: replace
  path: /spec/type
  value: LoadBalancer
- op: add
  path: /metadata/annotations
  value:
    service.beta.kubernetes.io/aws-load-balancer-type: nlb
```

### 4.3 变量替换

```yaml
# kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
  - deployment.yaml
  - service.yaml

# 定义变量
vars:
  - name: SERVICE_NAME
    objref:
      kind: Service
      name: web-app
      apiVersion: v1
    fieldref:
      fieldpath: metadata.name

  - name: SERVICE_NAMESPACE
    objref:
      kind: Service
      name: web-app
      apiVersion: v1
    fieldref:
      fieldpath: metadata.namespace

  - name: SERVICE_PORT
    objref:
      kind: Service
      name: web-app
      apiVersion: v1
    fieldref:
      fieldpath: spec.ports[0].port

# 注意: vars 在 Kustomize v5 中已弃用，推荐使用 replacements
```

```yaml
# kustomization.yaml (使用 replacements)
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
  - deployment.yaml
  - service.yaml

replacements:
  # 将 Service 的 clusterIP 注入到 Deployment 环境变量
  - source:
      kind: Service
      name: web-app
      fieldPath: spec.clusterIP
    targets:
      - select:
          kind: Deployment
          name: web-app
        fieldPaths:
          - spec.template.spec.containers.[name=app].env.[name=SERVICE_IP].value

  # 更复杂的替换
  - source:
      kind: ConfigMap
      name: app-config
      fieldPath: data.DATABASE_URL
    targets:
      - select:
          kind: Deployment
          name: web-app
        fieldPaths:
          - spec.template.spec.containers.[name=app].env.[name=DB_URL].value
```

### 4.4 组件（Components）

```yaml
# components/monitoring/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1alpha1
kind: Component

resources:
  - service-monitor.yaml
  - prometheus-rules.yaml

patchesStrategicMerge:
  - deployment-metrics-patch.yaml
```

```yaml
# overlays/production/kustomization.yaml
apiVersion: kustomize.config.k8s.io/v1beta1
kind: Kustomization

resources:
  - ../../base

components:
  - ../../components/monitoring
  - ../../components/istio
  - ../../components/cert-manager
```

## 五、Kustomize CLI 使用

### 5.1 基本命令

```bash
# ========== 构建输出 ==========
# 构建并输出到 stdout
kustomize build overlays/development

# 构建并保存到文件
kustomize build overlays/production > production-manifests.yaml

# 构建并直接应用到集群
kustomize build overlays/production | kubectl apply -f -

# 使用 kubectl 内置 kustomize
kubectl apply -k overlays/production

# ========== 验证和检查 ==========
# 验证 kustomization.yaml
kustomize cfg validate overlays/production

# 查看资源列表
kustomize cfg tree overlays/production

# 查看特定资源
kustomize cfg cat overlays/production --include-kind Deployment

# ========== 编辑和创建 ==========
# 创建新的 kustomization
cd base && kustomize init

# 添加资源
kustomize edit add resource deployment.yaml
kustomize edit add resource service.yaml

# 添加标签
kustomize edit add label environment:production

# 添加注解
kustomize edit add annotation version:v1.0.0

# 设置镜像
kustomize edit set image myapp=registry.example.com/myapp:v2.0.0

# 设置命名空间
kustomize edit set namespace production

# 设置名称前缀
kustomize edit set nameprefix prod-

# ========== 对比差异 ==========
# 比较两个 overlay 的差异
kustomize build overlays/development > dev.yaml
kustomize build overlays/production > prod.yaml
diff dev.yaml prod.yaml

# 使用 dyff 进行结构化比较
dyff between dev.yaml prod.yaml
```

### 5.2 多环境工作流

```bash
#!/bin/bash
# deploy.sh - 多环境部署脚本

ENV=${1:-development}
ACTION=${2:-apply}

case $ENV in
  development)
    OVERLAY="overlays/development"
    CONTEXT="minikube"
    ;;
  staging)
    OVERLAY="overlays/staging"
    CONTEXT="staging-cluster"
    ;;
  production)
    OVERLAY="overlays/production"
    CONTEXT="production-cluster"
    ;;
  *)
    echo "Unknown environment: $ENV"
    exit 1
    ;;
esac

# 切换上下文
kubectl config use-context $CONTEXT

# 验证配置
echo "Validating Kustomize configuration..."
kustomize build $OVERLAY > /dev/null
if [ $? -ne 0 ]; then
    echo "Validation failed!"
    exit 1
fi

# 执行操作
case $ACTION in
  apply)
    echo "Applying configuration to $ENV..."
    kustomize build $OVERLAY | kubectl apply -f -
    ;;
  delete)
    echo "Deleting configuration from $ENV..."
    kustomize build $OVERLAY | kubectl delete -f -
    ;;
  diff)
    echo "Showing diff for $ENV..."
    kustomize build $OVERLAY | kubectl diff -f - || true
    ;;
  *)
    echo "Unknown action: $ACTION"
    exit 1
    ;;
esac
```

## 六、CI/CD 集成

```yaml
# .github/workflows/deploy.yml
name: Deploy with Kustomize

on:
  push:
    branches: [main]

jobs:
  deploy-staging:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Setup Kubectl
      uses: azure/setup-kubectl@v3

    - name: Setup Kustomize
      run: |
        curl -s "https://raw.githubusercontent.com/kubernetes-sigs/kustomize/master/hack/install_kustomize.sh" | bash
        sudo mv kustomize /usr/local/bin/

    - name: Update Image Tag
      run: |
        cd overlays/staging
        kustomize edit set image myapp=registry.example.com/myapp:${{ github.sha }}

    - name: Build Manifests
      run: kustomize build overlays/staging > staging-manifests.yaml

    - name: Validate Manifests
      run: |
        kubectl apply --dry-run=client -f staging-manifests.yaml
        kubectl apply --dry-run=server -f staging-manifests.yaml

    - name: Deploy to Staging
      run: |
        kubectl config use-context staging
        kustomize build overlays/staging | kubectl apply -f -
        kubectl rollout status deployment/staging-web-app -n staging

    - name: Commit Image Tag Update
      run: |
        git config user.name github-actions
        git config user.email github-actions@github.com
        git add overlays/staging/kustomization.yaml
        git commit -m "Update staging image to ${{ github.sha }}"
        git push
```

## 七、最佳实践

### 7.1 目录结构建议

```
kubernetes/
├── README.md
├── base/                          # 基础资源
│   ├── kustomization.yaml
│   ├── namespace.yaml
│   ├── serviceaccount.yaml
│   ├── deployment.yaml
│   ├── service.yaml
│   └── config/
│       ├── default.conf
│       └── nginx.conf
├── components/                    # 可复用组件
│   ├── monitoring/
│   │   ├── kustomization.yaml
│   │   ├── service-monitor.yaml
│   │   └── grafana-dashboard.yaml
│   ├── istio/
│   │   ├── kustomization.yaml
│   │   ├── destinationrule.yaml
│   │   └── virtualservice.yaml
│   └── cert-manager/
│       ├── kustomization.yaml
│       └── certificate.yaml
└── overlays/                      # 环境覆盖
    ├── local/
    ├── development/
    ├── staging/
    └── production/
```

### 7.2 设计原则

1. **DRY (Don't Repeat Yourself)**
   - 基础配置只定义一次
   - 使用 overlay 进行环境特定修改

2. **显式优于隐式**
   - 所有变更都应在 kustomization.yaml 中声明
   - 避免魔法值

3. **可预测性**
   - 相同的输入总是产生相同的输出
   - 避免使用外部依赖

4. **可审查性**
   - 生成的 YAML 应该易于审查
   - 使用 `kustomize build` 查看最终输出

5. **版本控制**
   - 将所有配置纳入版本控制
   - 包括 kustomization.yaml 的变更

## 八、总结

Kustomize 是 Kubernetes 配置管理的强大工具，特别适合：

1. **多环境管理**：开发、测试、生产环境配置分离
2. **GitOps 工作流**：纯 YAML 易于版本控制和审查
3. **团队协作**：清晰的配置继承关系
4. **CI/CD 集成**：原生支持，无需额外工具

相比 Helm，Kustomize 更简单直观，适合不需要复杂模板逻辑的场景。两者也可以结合使用：使用 Helm 打包应用，使用 Kustomize 管理多环境部署。
