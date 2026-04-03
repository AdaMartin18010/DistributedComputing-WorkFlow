# Helm 包管理

## 一、概述

Helm 是 Kubernetes 的包管理工具，类似于 Linux 世界的 apt/yum 或 Mac 的 Homebrew。它使用 Charts 来定义、安装和升级复杂的 Kubernetes 应用。Helm 通过模板化配置，实现了 Kubernetes 应用的可复用、可配置和版本化管理。

## 二、Helm 架构

### 2.1 架构组件

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Helm 架构                                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                       Helm Client                                │    │
│  │                                                                  │    │
│  │  ┌──────────────┐   ┌──────────────┐   ┌──────────────────┐    │    │
│  │  │  Chart       │   │  Values      │   │  Release         │    │    │
│  │  │  包管理      │──►│  配置合并    │──►│  版本管理        │    │    │
│  │  │  - create    │   │  - default   │   │  - install       │    │    │
│  │  │  - package   │   │  - custom    │   │  - upgrade       │    │    │
│  │  │  - lint      │   │  - override  │   │  - rollback      │    │    │
│  │  └──────────────┘   └──────────────┘   └──────────────────┘    │    │
│  │                                                                  │    │
│  └────────────────────────────────────┬─────────────────────────────┘    │
│                                       │                                  │
│                                       ▼ gRPC/HTTP                        │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                       Helm 3 (无 Tiller)                         │    │
│  │                                                                  │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │  使用 kubeconfig 直接操作 Kubernetes API                 │    │    │
│  │  │  - Secrets 存储 Release 信息                             │    │    │
│  │  │  - 与 kubectl 相同的权限模型                              │    │    │
│  │  └─────────────────────────────────────────────────────────┘    │    │
│  │                                                                  │    │
│  └────────────────────────────────────┬─────────────────────────────┘    │
│                                       │                                  │
│                                       ▼                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                    Kubernetes Cluster                            │    │
│  │                                                                  │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────┐    │    │
│  │  │Secret    │  │Deployment│  │Service   │  │ConfigMap     │    │    │
│  │  │(Release) │  │          │  │          │  │              │    │    │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────────┘    │    │
│  │                                                                  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Chart 结构

```
mychart/                          # Chart 目录
├── Chart.yaml                    # Chart 元数据
├── values.yaml                   # 默认配置值
├── values.schema.json            # 配置值校验 Schema
├── charts/                       # 依赖的子 Chart
│   ├── redis-17.0.0.tgz
│   └── postgresql-12.0.0.tgz
├── crds/                         # CRD 定义
│   └── myresource.yaml
├── templates/                    # K8s 资源模板
│   ├── _helpers.tpl              # 辅助模板函数
│   ├── NOTES.txt                 # 安装后说明
│   ├── deployment.yaml
│   ├── service.yaml
│   ├── ingress.yaml
│   ├── configmap.yaml
│   ├── serviceaccount.yaml
│   ├── hpa.yaml
│   └── tests/                    # 测试模板
│       └── test-connection.yaml
└── README.md                     # 文档
```

## 三、Chart 开发

### 3.1 Chart.yaml

```yaml
# Chart.yaml
apiVersion: v2                          # v2 用于 Helm 3
name: web-application                   # Chart 名称
version: 1.2.3                          # Chart 版本 (SemVer)
appVersion: "2.0.0"                     # 应用版本
kubeVersion: ">=1.20.0-0"               # 兼容的 K8s 版本
description: A Helm chart for Web Application  # 描述
type: application                       # application/library

keywords:                               # 关键词
  - web
  - frontend
  - backend

home: https://example.com               # 项目主页
sources:                                # 源码地址
  - https://github.com/example/web-app

maintainers:                            # 维护者
  - name: John Doe
    email: john@example.com
    url: https://example.com/john

dependencies:                           # 依赖
  - name: postgresql
    version: "12.x.x"
    repository: "https://charts.bitnami.com/bitnami"
    condition: postgresql.enabled
    tags:
      - database
    alias: db

  - name: redis
    version: "17.x.x"
    repository: "https://charts.bitnami.com/bitnami"
    condition: redis.enabled
    import-values:                      # 导入子 Chart 值
      - child: defaults
        parent: global

annotations:                            # 元数据注解
  category: ApplicationServer
  licenses: Apache-2.0
```

### 3.2 values.yaml

```yaml
# values.yaml - 默认配置值

# 全局配置
global:
  imageRegistry: ""
  imagePullSecrets: []
  storageClass: ""

# 镜像配置
image:
  registry: docker.io
  repository: myapp/web
  tag: "latest"
  pullPolicy: IfNotPresent
  pullSecrets: []

# 副本数
replicaCount: 3

# 部署策略
deploymentStrategy:
  type: RollingUpdate
  rollingUpdate:
    maxSurge: 25%
    maxUnavailable: 0

# Pod 配置
podAnnotations: {}
podLabels: {}
podSecurityContext:
  runAsNonRoot: true
  runAsUser: 1000
  fsGroup: 1000

# 容器安全上下文
securityContext:
  allowPrivilegeEscalation: false
  readOnlyRootFilesystem: true
  capabilities:
    drop:
      - ALL

# 服务配置
service:
  type: ClusterIP
  port: 80
  targetPort: 8080
  nodePort: null
  annotations: {}

# Ingress 配置
ingress:
  enabled: true
  className: nginx
  annotations:
    cert-manager.io/cluster-issuer: letsencrypt-prod
    nginx.ingress.kubernetes.io/rate-limit: "100"
  hosts:
    - host: app.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: app-tls
      hosts:
        - app.example.com

# 资源配置
resources:
  limits:
    cpu: 1000m
    memory: 1Gi
  requests:
    cpu: 250m
    memory: 256Mi

# 自动扩缩容
autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 20
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300

# 健康检查
livenessProbe:
  enabled: true
  path: /health
  initialDelaySeconds: 30
  periodSeconds: 10
  timeoutSeconds: 5
  failureThreshold: 3

readinessProbe:
  enabled: true
  path: /ready
  initialDelaySeconds: 5
  periodSeconds: 5
  timeoutSeconds: 3
  failureThreshold: 3

# 环境变量
env:
  - name: LOG_LEVEL
    value: info
  - name: DATABASE_URL
    valueFrom:
      secretKeyRef:
        name: app-secrets
        key: database-url

# 额外环境变量（通过 values 注入）
extraEnv: []
extraEnvFrom: []

# 卷配置
persistence:
  enabled: true
  storageClass: ""
  accessMode: ReadWriteOnce
  size: 10Gi
  mountPath: /data

# 配置 ConfigMap
config:
  app.name: My Application
  app.debug: "false"
  cache.ttl: "3600"

# 密钥 Secret
secrets:
  apiKey: ""
  jwtSecret: ""

# 依赖配置
postgresql:
  enabled: true
  auth:
    username: appuser
    password: ""
    database: appdb
  primary:
    persistence:
      size: 20Gi

redis:
  enabled: true
  auth:
    enabled: true
    password: ""
  master:
    persistence:
      size: 8Gi

# 网络策略
networkPolicy:
  enabled: true
  ingress:
    - from:
        - podSelector:
            matchLabels:
              app.kubernetes.io/name: frontend
      ports:
        - protocol: TCP
          port: 8080

# Pod 亲和性
affinity:
  podAntiAffinity:
    preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 100
        podAffinityTerm:
          labelSelector:
            matchExpressions:
              - key: app.kubernetes.io/name
                operator: In
                values:
                  - web-application
          topologyKey: kubernetes.io/hostname

# 容忍
tolerations: []

# 节点选择器
nodeSelector: {}

# 服务账户
serviceAccount:
  create: true
  annotations: {}
  name: ""
```

### 3.3 模板文件

```yaml
# templates/_helpers.tpl - 辅助模板
{{/*
Expand the name of the chart.
*/}}
{{- define "webapp.name" -}}
{{- default .Chart.Name .Values.nameOverride | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Create a default fully qualified app name.
*/}}
{{- define "webapp.fullname" -}}
{{- if .Values.fullnameOverride }}
{{- .Values.fullnameOverride | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- $name := default .Chart.Name .Values.nameOverride }}
{{- if contains $name .Release.Name }}
{{- .Release.Name | trunc 63 | trimSuffix "-" }}
{{- else }}
{{- printf "%s-%s" .Release.Name $name | trunc 63 | trimSuffix "-" }}
{{- end }}
{{- end }}
{{- end }}

{{/*
Create chart name and version as used by the chart label.
*/}}
{{- define "webapp.chart" -}}
{{- printf "%s-%s" .Chart.Name .Chart.Version | replace "+" "_" | trunc 63 | trimSuffix "-" }}
{{- end }}

{{/*
Common labels
*/}}
{{- define "webapp.labels" -}}
helm.sh/chart: {{ include "webapp.chart" . }}
{{ include "webapp.selectorLabels" . }}
{{- if .Chart.AppVersion }}
app.kubernetes.io/version: {{ .Chart.AppVersion | quote }}
{{- end }}
app.kubernetes.io/managed-by: {{ .Release.Service }}
{{- end }}

{{/*
Selector labels
*/}}
{{- define "webapp.selectorLabels" -}}
app.kubernetes.io/name: {{ include "webapp.name" . }}
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end }}

{{/*
Create the name of the service account to use
*/}}
{{- define "webapp.serviceAccountName" -}}
{{- if .Values.serviceAccount.create }}
{{- default (include "webapp.fullname" .) .Values.serviceAccount.name }}
{{- else }}
{{- default "default" .Values.serviceAccount.name }}
{{- end }}
{{- end }}
```

```yaml
# templates/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: {{ include "webapp.fullname" . }}
  labels:
    {{- include "webapp.labels" . | nindent 4 }}
spec:
  {{- if not .Values.autoscaling.enabled }}
  replicas: {{ .Values.replicaCount }}
  {{- end }}
  strategy:
    type: {{ .Values.deploymentStrategy.type }}
    {{- if eq .Values.deploymentStrategy.type "RollingUpdate" }}
    rollingUpdate:
      maxSurge: {{ .Values.deploymentStrategy.rollingUpdate.maxSurge }}
      maxUnavailable: {{ .Values.deploymentStrategy.rollingUpdate.maxUnavailable }}
    {{- end }}
  selector:
    matchLabels:
      {{- include "webapp.selectorLabels" . | nindent 6 }}
  template:
    metadata:
      annotations:
        checksum/config: {{ include (print $.Template.BasePath "/configmap.yaml") . | sha256sum }}
        checksum/secrets: {{ include (print $.Template.BasePath "/secret.yaml") . | sha256sum }}
        {{- with .Values.podAnnotations }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
      labels:
        {{- include "webapp.selectorLabels" . | nindent 8 }}
        {{- with .Values.podLabels }}
        {{- toYaml . | nindent 8 }}
        {{- end }}
    spec:
      {{- with .Values.imagePullSecrets }}
      imagePullSecrets:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      serviceAccountName: {{ include "webapp.serviceAccountName" . }}
      securityContext:
        {{- toYaml .Values.podSecurityContext | nindent 8 }}
      containers:
        - name: {{ .Chart.Name }}
          securityContext:
            {{- toYaml .Values.securityContext | nindent 12 }}
          image: "{{ .Values.image.registry }}/{{ .Values.image.repository }}:{{ .Values.image.tag | default .Chart.AppVersion }}"
          imagePullPolicy: {{ .Values.image.pullPolicy }}
          ports:
            - name: http
              containerPort: {{ .Values.service.targetPort }}
              protocol: TCP
          env:
            {{- toYaml .Values.env | nindent 12 }}
            {{- range $key, $value := .Values.config }}
            - name: {{ $key | upper | replace "." "_" }}
              value: {{ $value | quote }}
            {{- end }}
            {{- if .Values.postgresql.enabled }}
            - name: DATABASE_HOST
              value: {{ include "webapp.fullname" . }}-db
            - name: DATABASE_PORT
              value: "5432"
            {{- end }}
          envFrom:
            {{- toYaml .Values.extraEnvFrom | nindent 12 }}
            - secretRef:
                name: {{ include "webapp.fullname" . }}
          {{- if .Values.persistence.enabled }}
          volumeMounts:
            - name: data
              mountPath: {{ .Values.persistence.mountPath }}
          {{- end }}
          livenessProbe:
            {{- if .Values.livenessProbe.enabled }}
            httpGet:
              path: {{ .Values.livenessProbe.path }}
              port: http
            initialDelaySeconds: {{ .Values.livenessProbe.initialDelaySeconds }}
            periodSeconds: {{ .Values.livenessProbe.periodSeconds }}
            timeoutSeconds: {{ .Values.livenessProbe.timeoutSeconds }}
            failureThreshold: {{ .Values.livenessProbe.failureThreshold }}
            {{- end }}
          readinessProbe:
            {{- if .Values.readinessProbe.enabled }}
            httpGet:
              path: {{ .Values.readinessProbe.path }}
              port: http
            initialDelaySeconds: {{ .Values.readinessProbe.initialDelaySeconds }}
            periodSeconds: {{ .Values.readinessProbe.periodSeconds }}
            timeoutSeconds: {{ .Values.readinessProbe.timeoutSeconds }}
            failureThreshold: {{ .Values.readinessProbe.failureThreshold }}
            {{- end }}
          resources:
            {{- toYaml .Values.resources | nindent 12 }}
      {{- with .Values.nodeSelector }}
      nodeSelector:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.affinity }}
      affinity:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- with .Values.tolerations }}
      tolerations:
        {{- toYaml . | nindent 8 }}
      {{- end }}
      {{- if .Values.persistence.enabled }}
      volumes:
        - name: data
          persistentVolumeClaim:
            claimName: {{ include "webapp.fullname" . }}
      {{- end }}
```

```yaml
# templates/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: {{ include "webapp.fullname" . }}
  labels:
    {{- include "webapp.labels" . | nindent 4 }}
  {{- with .Values.service.annotations }}
  annotations:
    {{- toYaml . | nindent 4 }}
  {{- end }}
spec:
  type: {{ .Values.service.type }}
  ports:
    - port: {{ .Values.service.port }}
      targetPort: http
      protocol: TCP
      name: http
      {{- if and (eq .Values.service.type "NodePort") .Values.service.nodePort }}
      nodePort: {{ .Values.service.nodePort }}
      {{- end }}
  selector:
    {{- include "webapp.selectorLabels" . | nindent 4 }}
```

```yaml
# templates/hpa.yaml
{{- if .Values.autoscaling.enabled }}
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: {{ include "webapp.fullname" . }}
  labels:
    {{- include "webapp.labels" . | nindent 4 }}
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: {{ include "webapp.fullname" . }}
  minReplicas: {{ .Values.autoscaling.minReplicas }}
  maxReplicas: {{ .Values.autoscaling.maxReplicas }}
  metrics:
    {{- if .Values.autoscaling.targetCPUUtilizationPercentage }}
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: {{ .Values.autoscaling.targetCPUUtilizationPercentage }}
    {{- end }}
    {{- if .Values.autoscaling.targetMemoryUtilizationPercentage }}
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: {{ .Values.autoscaling.targetMemoryUtilizationPercentage }}
    {{- end }}
  {{- if .Values.autoscaling.behavior }}
  behavior:
    {{- toYaml .Values.autoscaling.behavior | nindent 4 }}
  {{- end }}
{{- end }}
```

## 四、Helm 命令使用

### 4.1 常用命令

```bash
# ========== Chart 管理 ==========
# 创建新 Chart
helm create mychart

# 打包 Chart
helm package mychart

# 验证 Chart
helm lint mychart

# 渲染模板（测试）
helm template mychart
helm template mychart --values custom-values.yaml

# ========== Release 管理 ==========
# 安装 Chart
helm install myrelease mychart
helm install myrelease mychart --values values-prod.yaml
helm install myrelease mychart --set replicaCount=5
helm install myrelease mychart --set image.tag=v2.0.0

# 升级 Release
helm upgrade myrelease mychart
helm upgrade myrelease mychart --install  # 如果不存在则安装
helm upgrade myrelease mychart --force    # 强制升级

# 回滚 Release
helm rollback myrelease 1  # 回滚到版本 1

# 卸载 Release
helm uninstall myrelease
helm uninstall myrelease --keep-history  # 保留历史记录

# ========== 查询命令 ==========
# 列出所有 Release
helm list
helm list --all-namespaces
helm list --filter "web-"

# 查看 Release 历史
helm history myrelease

# 查看 Release 状态
helm status myrelease

# 获取 Release 值
helm get values myrelease
helm get values myrelease --all  # 包括默认值

# 获取 Release 清单
helm get manifest myrelease

# ========== 仓库管理 ==========
# 添加仓库
helm repo add bitnami https://charts.bitnami.com/bitnami
helm repo add prometheus https://prometheus-community.github.io/helm-charts

# 列出仓库
helm repo list

# 更新仓库索引
helm repo update

# 搜索 Chart
helm search repo nginx
helm search hub prometheus  # 在 Artifact Hub 搜索

# ========== 依赖管理 ==========
# 更新依赖
helm dependency update mychart

# 构建依赖
helm dependency build mychart

# 列出依赖
helm dependency list mychart
```

### 4.2 高级用法

```bash
# 使用 --dry-run 测试安装
helm install myrelease mychart --dry-run --debug

# 使用 --wait 等待资源就绪
helm install myrelease mychart --wait --timeout 10m

# 使用 --atomic 失败时自动回滚
helm upgrade myrelease mychart --atomic

# 使用 post-render 处理（如 kustomize）
helm install myrelease mychart --post-renderer ./kustomize.sh

# 导出已渲染的清单
helm template mychart > rendered.yaml
```

## 五、Helm 最佳实践

### 5.1 版本管理策略

```yaml
# 语义化版本管理
# Chart version: 主版本.次版本.补丁版本
# - 主版本：不兼容的 API 变更
# - 次版本：向后兼容的功能添加
# - 补丁版本：向后兼容的问题修复

# 版本升级策略
# 1. 修复 bug -> 补丁版本 (1.2.3 -> 1.2.4)
# 2. 新增功能 -> 次版本 (1.2.3 -> 1.3.0)
# 3. 破坏性变更 -> 主版本 (1.2.3 -> 2.0.0)

# Chart.yaml
apiVersion: v2
name: myapp
version: 2.1.0        # Chart 版本
appVersion: "3.5.0"   # 应用版本
```

### 5.2 多环境配置

```yaml
# values.yaml (默认值)
replicaCount: 1
resources:
  requests:
    cpu: 100m
    memory: 128Mi

# values-development.yaml
ingress:
  enabled: false

# values-staging.yaml
replicaCount: 2
resources:
  requests:
    cpu: 250m
    memory: 256Mi

# values-production.yaml
replicaCount: 5
resources:
  requests:
    cpu: 500m
    memory: 512Mi
  limits:
    cpu: 1000m
    memory: 1Gi
autoscaling:
  enabled: true
  minReplicas: 5
  maxReplicas: 20

# 部署命令
helm install myapp ./mychart -f values.yaml -f values-production.yaml
```

### 5.3 CI/CD 集成

```yaml
# .github/workflows/helm-deploy.yml
name: Helm Deploy

on:
  push:
    branches: [ main ]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Setup Helm
      uses: azure/setup-helm@v3
      with:
        version: '3.12.0'

    - name: Lint Chart
      run: helm lint ./chart

    - name: Template Chart
      run: helm template myapp ./chart --values values-production.yaml

    - name: Setup kubeconfig
      uses: azure/k8s-set-context@v3
      with:
        method: kubeconfig
        kubeconfig: ${{ secrets.KUBECONFIG }}

    - name: Deploy with Helm
      run: |
        helm upgrade --install myapp ./chart \
          --namespace production \
          --create-namespace \
          --values values-production.yaml \
          --set image.tag=${{ github.sha }} \
          --wait \
          --timeout 10m \
          --atomic

    - name: Verify Deployment
      run: |
        kubectl rollout status deployment/myapp -n production
```

## 六、总结

Helm 是 Kubernetes 应用管理的标准工具，主要优势包括：

1. **可复用性**：Chart 可以打包和分享
2. **可配置性**：通过 values 文件灵活配置
3. **版本管理**：支持发布版本控制和回滚
4. **依赖管理**：自动管理子 Chart 依赖
5. **模板化**：减少重复配置，提高效率

最佳实践：

- 使用语义化版本管理 Chart
- 为不同环境维护独立的 values 文件
- 充分利用模板函数减少重复
- 添加充分的注释和文档
- 在 CI/CD 中集成 Helm 验证步骤
