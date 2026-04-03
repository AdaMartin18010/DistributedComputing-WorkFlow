# K8s Operator 模式

## 一、概述

Operator 模式是一种用于扩展 Kubernetes API 的方法，它将运维知识编码为软件，实现复杂有状态应用的自动化部署、管理和运维。Operator 通过自定义资源（CRD）和控制器（Controller）来实现对应用程序生命周期的完全控制。

## 二、Operator 架构

### 2.1 核心组件

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Operator 架构                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                       Custom Resource                            │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │ apiVersion: myapp.io/v1                                 │    │    │
│  │  │ kind: Database                                           │    │    │
│  │  │ metadata:                                                │    │    │
│  │  │   name: production-db                                    │    │    │
│  │  │ spec:                                                    │    │    │
│  │  │   version: "15.2"                                        │    │    │
│  │  │   replicas: 3                                            │    │    │
│  │  │   storage: 100Gi                                         │    │    │
│  │  │   backup:                                                │    │    │
│  │  │     enabled: true                                        │    │    │
│  │  │     schedule: "0 2 * * *"                                │    │    │
│  │  └─────────────────────────────────────────────────────────┘    │    │
│  └────────────────────────────────────┬────────────────────────────┘    │
│                                       │                                  │
│                                       ▼                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                      Operator Controller                         │    │
│  │                                                                  │    │
│  │  ┌──────────────┐   ┌──────────────┐   ┌──────────────────┐    │    │
│  │  │   Informer   │   │   Reconciler │   │  Event Handler   │    │    │
│  │  │              │──►│              │──►│                  │    │    │
│  │  │ Watch CR     │   │ 调谐循环      │   │ 执行运维操作      │    │    │
│  │  │ 变化事件     │   │ Compare      │   │ 创建/更新/删除   │    │    │
│  │  └──────────────┘   │ Actual ↔     │   │ 子资源           │    │    │
│  │                     │ Desired      │   └──────────────────┘    │    │
│  │                     └──────────────┘                            │    │
│  │                                                                  │    │
│  └────────────────────────────────────┬────────────────────────────┘    │
│                                       │                                  │
│                                       ▼                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                      Managed Resources                           │    │
│  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────┐    │    │
│  │  │StatefulSet│  │  Secret  │  │  ConfigMap│  │  Service     │    │    │
│  │  ├──────────┤  ├──────────┤  ├──────────┤  ├──────────────┤    │    │
│  │  │   Pod    │  │   PVC    │  │  Job     │  │  Ingress     │    │    │
│  │  └──────────┘  └──────────┘  └──────────┘  └──────────────┘    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 控制器模式

```
┌─────────────────────────────────────────────────────────────┐
│                  控制器调谐循环 (Reconciliation Loop)         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│     ┌─────────────────────────────────────────────────┐     │
│     │              Reconcile Request                   │     │
│     │         (Namespace + Name of CR)                 │     │
│     └───────────────────────┬─────────────────────────┘     │
│                             │                                │
│                             ▼                                │
│     ┌─────────────────────────────────────────────────┐     │
│     │  1. 获取当前状态 (Actual State)                  │     │
│     │     - 从 API Server 读取 CR                     │     │
│     │     - 获取所有管理的子资源状态                   │     │
│     └───────────────────────┬─────────────────────────┘     │
│                             │                                │
│                             ▼                                │
│     ┌─────────────────────────────────────────────────┐     │
│     │  2. 比较期望状态 vs 实际状态                      │     │
│     │     - Spec vs Status                            │     │
│     │     - 创建缺失的资源                            │     │
│     │     - 更新变化的资源                            │     │
│     │     - 删除多余的资源                            │     │
│     └───────────────────────┬─────────────────────────┘     │
│                             │                                │
│                             ▼                                │
│     ┌─────────────────────────────────────────────────┐     │
│     │  3. 执行调和动作                                  │     │
│     │     - Create/Update/Delete 子资源               │     │
│     │     - 调用外部 API                              │     │
│     │     - 更新 CR Status                            │     │
│     └───────────────────────┬─────────────────────────┘     │
│                             │                                │
│                             ▼                                │
│     ┌─────────────────────────────────────────────────┐     │
│     │  4. 返回结果                                      │     │
│     │     - 成功: requeue=false                       │     │
│     │     - 失败: requeue=true (稍后重试)              │     │
│     │     - 周期性: requeueAfter=duration             │     │
│     └─────────────────────────────────────────────────┘     │
│                                                              │
│     ┌─────────────────────────────────────────────────┐     │
│     │  设计原则:                                        │     │
│     │  - 幂等性: 多次执行结果一致                        │     │
│     │  - 水平触发 (Level-triggered): 持续调和            │     │
│     │  - 边缘触发 (Edge-triggered): 事件驱动             │     │
│     └─────────────────────────────────────────────────┘     │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## 三、CRD（自定义资源定义）

### 3.1 CRD 定义

```yaml
# database-crd.yaml
apiVersion: apiextensions.k8s.io/v1
kind: CustomResourceDefinition
metadata:
  name: databases.myapp.io
spec:
  group: myapp.io
  names:
    kind: Database
    listKind: DatabaseList
    plural: databases
    singular: database
    shortNames:
    - db
    categories:
    - all
    - storage
  scope: Namespaced
  versions:
  - name: v1
    served: true
    storage: true
    deprecated: false
    schema:
      openAPIV3Schema:
        type: object
        properties:
          spec:
            type: object
            required:
            - version
            - storage
            properties:
              version:
                type: string
                description: "PostgreSQL版本"
                pattern: '^\d+\.\d+$'
              replicas:
                type: integer
                default: 1
                minimum: 1
                maximum: 10
                description: "副本数量"
              storage:
                type: string
                pattern: '^\d+(Gi|Mi)$'
                description: "存储容量"
              storageClassName:
                type: string
                description: "StorageClass名称"
              resources:
                type: object
                properties:
                  requests:
                    type: object
                    properties:
                      cpu:
                        type: string
                      memory:
                        type: string
                  limits:
                    type: object
                    properties:
                      cpu:
                        type: string
                      memory:
                        type: string
              backup:
                type: object
                properties:
                  enabled:
                    type: boolean
                    default: false
                  schedule:
                    type: string
                    description: "Cron表达式"
                  retention:
                    type: integer
                    default: 7
                    description: "备份保留天数"
              monitoring:
                type: object
                properties:
                  enabled:
                    type: boolean
                    default: true
                  exporterImage:
                    type: string
                    default: "prometheuscommunity/postgres-exporter:latest"
          status:
            type: object
            properties:
              phase:
                type: string
                enum:
                - Pending
                - Creating
                - Running
                - Failed
                - Deleting
              conditions:
                type: array
                items:
                  type: object
                  properties:
                    type:
                      type: string
                    status:
                      type: string
                    lastTransitionTime:
                      type: string
                      format: date-time
                    reason:
                      type: string
                    message:
                      type: string
              observedGeneration:
                type: integer
              readyReplicas:
                type: integer
              currentVersion:
                type: string
              lastBackupTime:
                type: string
                format: date-time
    subresources:
      status: {}
      scale:
        specReplicasPath: .spec.replicas
        statusReplicasPath: .status.readyReplicas
        labelSelectorPath: .status.labelSelector
    additionalPrinterColumns:
    - name: Version
      type: string
      description: PostgreSQL版本
      jsonPath: .spec.version
    - name: Replicas
      type: integer
      description: 副本数
      jsonPath: .spec.replicas
    - name: Storage
      type: string
      description: 存储容量
      jsonPath: .spec.storage
    - name: Status
      type: string
      description: 状态
      jsonPath: .status.phase
    - name: Age
      type: date
      jsonPath: .metadata.creationTimestamp
```

### 3.2 创建和使用 CR

```bash
# 创建 CRD
kubectl apply -f database-crd.yaml

# 查看 CRD
kubectl get crd databases.myapp.io -o yaml
kubectl get crd databases.myapp.io -o jsonpath='{.spec.versions[0].schema.openAPIV3Schema}'

# 创建自定义资源实例
kubectl apply -f - <<EOF
apiVersion: myapp.io/v1
kind: Database
metadata:
  name: production-db
  namespace: default
spec:
  version: "15.2"
  replicas: 3
  storage: 100Gi
  storageClassName: gp3
  resources:
    requests:
      cpu: "500m"
      memory: "1Gi"
    limits:
      cpu: "2000m"
      memory: "4Gi"
  backup:
    enabled: true
    schedule: "0 2 * * *"
    retention: 14
  monitoring:
    enabled: true
EOF

# 查看 CR
kubectl get databases
kubectl get db production-db -o yaml
kubectl describe db production-db
```

## 四、Operator SDK 开发

### 4.1 项目初始化

```bash
# 安装 Operator SDK
export ARCH=$(case $(uname -m) in x86_64) echo -n amd64 ;; aarch64) echo -n arm64 ;; *) echo -n $(uname -m) ;; esac)
export OS=$(uname | awk '{print tolower($0)}')
export OPERATOR_SDK_DL_URL=https://github.com/operator-framework/operator-sdk/releases/download/v1.32.0
curl -LO ${OPERATOR_SDK_DL_URL}/operator-sdk_${OS}_${ARCH}
gpg --keyserver keyserver.ubuntu.com --recv-keys 052996E2A20B5C7E
curl -LO ${OPERATOR_SDK_DL_URL}/checksums.txt
curl -LO ${OPERATOR_SDK_DL_URL}/checksums.txt.asc
gpg -u "Operator SDK (release) <cncf-operator-sdk@cncf.io>" --verify checksums.txt.asc
chmod +x operator-sdk_${OS}_${ARCH} && sudo mv operator-sdk_${OS}_${ARCH} /usr/local/bin/operator-sdk

# 初始化项目
mkdir -p $HOME/projects/
cd $HOME/projects/
operator-sdk init --domain=myapp.io --repo=github.com/myorg/database-operator

# 创建 API 和控制器
operator-sdk create api --group=myapp.io --version=v1 --kind=Database --resource=true --controller=true

# 项目结构
# .
# ├── Dockerfile
# ├── Makefile
# ├── PROJECT
# ├── api/
# │   └── v1/
# │       ├── database_types.go      # CR 结构定义
# │       ├── groupversion_info.go
# │       └── zz_generated.deepcopy.go
# ├── bin/
# ├── config/
# │   ├── crd/                       # CRD 配置
# │   ├── default/
# │   ├── manager/
# │   ├── manifests/
# │   ├── prometheus/
# │   ├── rbac/                      # RBAC 配置
# │   └── samples/                   # CR 示例
# ├── controllers/
# │   ├── database_controller.go     # 控制器逻辑
# │   └── suite_test.go
# ├── go.mod
# ├── go.sum
# ├── hack/
# └── main.go
```

### 4.2 类型定义（Types）

```go
// api/v1/database_types.go
package v1

import (
 metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

// DatabaseSpec 定义了 Database 的期望状态
type DatabaseSpec struct {
 // PostgreSQL 版本
 // +kubebuilder:validation:Pattern=`^\d+\.\d+$`
 Version string `json:"version"`

 // 副本数量
 // +kubebuilder:validation:Minimum=1
 // +kubebuilder:validation:Maximum=10
 // +kubebuilder:default=1
 Replicas int32 `json:"replicas,omitempty"`

 // 存储配置
 Storage StorageSpec `json:"storage"`

 // 资源限制
 // +optional
 Resources ResourceRequirements `json:"resources,omitempty"`

 // 备份配置
 // +optional
 Backup BackupSpec `json:"backup,omitempty"`

 // 监控配置
 // +optional
 Monitoring MonitoringSpec `json:"monitoring,omitempty"`
}

type StorageSpec struct {
 // 存储容量
 // +kubebuilder:validation:Pattern=`^\d+(Gi|Mi)$`
 Size string `json:"size"`

 // StorageClass 名称
 // +optional
 StorageClassName string `json:"storageClassName,omitempty"`
}

type BackupSpec struct {
 // 是否启用备份
 // +kubebuilder:default=false
 Enabled bool `json:"enabled,omitempty"`

 // Cron 表达式
 // +optional
 Schedule string `json:"schedule,omitempty"`

 // 保留天数
 // +kubebuilder:default=7
 // +optional
 Retention int `json:"retention,omitempty"`
}

type MonitoringSpec struct {
 // 是否启用监控
 // +kubebuilder:default=true
 Enabled bool `json:"enabled,omitempty"`

 // Exporter 镜像
 // +optional
 ExporterImage string `json:"exporterImage,omitempty"`
}

// DatabaseStatus 定义了 Database 的观测状态
type DatabaseStatus struct {
 // 当前阶段
 // +optional
 Phase string `json:"phase,omitempty"`

 // 状态条件
 // +optional
 Conditions []metav1.Condition `json:"conditions,omitempty"`

 // 观察到的资源版本
 // +optional
 ObservedGeneration int64 `json:"observedGeneration,omitempty"`

 // 就绪副本数
 // +optional
 ReadyReplicas int32 `json:"readyReplicas,omitempty"`

 // 当前版本
 // +optional
 CurrentVersion string `json:"currentVersion,omitempty"`

 // 上次备份时间
 // +optional
 LastBackupTime *metav1.Time `json:"lastBackupTime,omitempty"`
}

// +kubebuilder:object:root=true
// +kubebuilder:subresource:status
// +kubebuilder:subresource:scale:specpath=.spec.replicas,statuspath=.status.readyReplicas,selectorpath=.status.labelSelector
// +kubebuilder:resource:shortName=db,scope=Namespaced,categories={all,storage}
// +kubebuilder:printcolumn:name="Version",type=string,JSONPath=`.spec.version`
// +kubebuilder:printcolumn:name="Replicas",type=integer,JSONPath=`.spec.replicas`
// +kubebuilder:printcolumn:name="Storage",type=string,JSONPath=`.spec.storage.size`
// +kubebuilder:printcolumn:name="Status",type=string,JSONPath=`.status.phase`
// +kubebuilder:printcolumn:name="Age",type=date,JSONPath=`.metadata.creationTimestamp`

// Database 是 Database API 的 Schema
type Database struct {
 metav1.TypeMeta   `json:",inline"`
 metav1.ObjectMeta `json:"metadata,omitempty"`

 Spec   DatabaseSpec   `json:"spec,omitempty"`
 Status DatabaseStatus `json:"status,omitempty"`
}

//+kubebuilder:object:root=true

// DatabaseList contains a list of Database
type DatabaseList struct {
 metav1.TypeMeta `json:",inline"`
 metav1.ListMeta `json:"metadata,omitempty"`
 Items           []Database `json:"items"`
}

func init() {
 SchemeBuilder.Register(&Database{}, &DatabaseList{})
}
```

### 4.3 控制器实现

```go
// controllers/database_controller.go
package controllers

import (
 "context"
 "fmt"
 "time"

 appsv1 "k8s.io/api/apps/v1"
 corev1 "k8s.io/api/core/v1"
 "k8s.io/apimachinery/pkg/api/errors"
 "k8s.io/apimachinery/pkg/api/resource"
 metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
 "k8s.io/apimachinery/pkg/runtime"
 "k8s.io/apimachinery/pkg/types"
 ctrl "sigs.k8s.io/controller-runtime"
 "sigs.k8s.io/controller-runtime/pkg/client"
 "sigs.k8s.io/controller-runtime/pkg/controller/controllerutil"
 "sigs.k8s.io/controller-runtime/pkg/log"

 databasev1 "github.com/myorg/database-operator/api/v1"
)

// DatabaseReconciler 协调 Database 对象
type DatabaseReconciler struct {
 client.Client
 Scheme *runtime.Scheme
}

//+kubebuilder:rbac:groups=myapp.io,resources=databases,verbs=get;list;watch;create;update;patch;delete
//+kubebuilder:rbac:groups=myapp.io,resources=databases/status,verbs=get;update;patch
//+kubebuilder:rbac:groups=myapp.io,resources=databases/finalizers,verbs=update
//+kubebuilder:rbac:groups=apps,resources=statefulsets,verbs=get;list;watch;create;update;patch;delete
//+kubebuilder:rbac:groups="",resources=services,verbs=get;list;watch;create;update;patch;delete
//+kubebuilder:rbac:groups="",resources=configmaps,verbs=get;list;watch;create;update;patch;delete
//+kubebuilder:rbac:groups="",resources=secrets,verbs=get;list;watch;create;update;patch;delete
//+kubebuilder:rbac:groups="",resources=persistentvolumeclaims,verbs=get;list;watch;create;update;patch;delete

// Reconcile 是主要的调谐逻辑
func (r *DatabaseReconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
 log := log.FromContext(ctx)

 // 1. 获取 Database 对象
 db := &databasev1.Database{}
 if err := r.Get(ctx, req.NamespacedName, db); err != nil {
  if errors.IsNotFound(err) {
   log.Info("Database resource not found. Ignoring since object must be deleted")
   return ctrl.Result{}, nil
  }
  log.Error(err, "Failed to get Database")
  return ctrl.Result{}, err
 }

 // 2. 处理删除逻辑（Finalizer）
 if db.DeletionTimestamp != nil {
  return r.handleDeletion(ctx, db)
 }

 // 3. 添加 Finalizer
 if !controllerutil.ContainsFinalizer(db, "database.myapp.io/finalizer") {
  controllerutil.AddFinalizer(db, "database.myapp.io/finalizer")
  if err := r.Update(ctx, db); err != nil {
   return ctrl.Result{}, err
  }
 }

 // 4. 更新状态为 Creating
 if db.Status.Phase == "" {
  db.Status.Phase = "Creating"
  if err := r.Status().Update(ctx, db); err != nil {
   return ctrl.Result{}, err
  }
  return ctrl.Result{Requeue: true}, nil
 }

 // 5. 协调 Secret（生成密码）
 if err := r.reconcileSecret(ctx, db); err != nil {
  return r.updateStatus(ctx, db, "Failed", err)
 }

 // 6. 协调 ConfigMap（配置文件）
 if err := r.reconcileConfigMap(ctx, db); err != nil {
  return r.updateStatus(ctx, db, "Failed", err)
 }

 // 7. 协调 Service
 if err := r.reconcileService(ctx, db); err != nil {
  return r.updateStatus(ctx, db, "Failed", err)
 }

 // 8. 协调 StatefulSet
 if err := r.reconcileStatefulSet(ctx, db); err != nil {
  return r.updateStatus(ctx, db, "Failed", err)
 }

 // 9. 协调 Backup CronJob（如果启用）
 if db.Spec.Backup.Enabled {
  if err := r.reconcileBackup(ctx, db); err != nil {
   return r.updateStatus(ctx, db, "Failed", err)
  }
 }

 // 10. 更新状态为 Running
 return r.updateStatus(ctx, db, "Running", nil)
}

// reconcileStatefulSet 创建或更新 StatefulSet
func (r *DatabaseReconciler) reconcileStatefulSet(ctx context.Context, db *databasev1.Database) error {
 sts := &appsv1.StatefulSet{}
 stsName := types.NamespacedName{Name: db.Name, Namespace: db.Namespace}

 err := r.Get(ctx, stsName, sts)
 if err != nil && errors.IsNotFound(err) {
  // 创建新的 StatefulSet
  sts = r.buildStatefulSet(db)
  if err := controllerutil.SetControllerReference(db, sts, r.Scheme); err != nil {
   return err
  }
  return r.Create(ctx, sts)
 } else if err != nil {
  return err
 }

 // 更新 StatefulSet
 sts.Spec.Replicas = &db.Spec.Replicas
 sts.Spec.Template.Spec.Containers[0].Image = fmt.Sprintf("postgres:%s", db.Spec.Version)
 return r.Update(ctx, sts)
}

// buildStatefulSet 构建 StatefulSet 对象
func (r *DatabaseReconciler) buildStatefulSet(db *databasev1.Database) *appsv1.StatefulSet {
 labels := map[string]string{
  "app":                          "database",
  "database.myapp.io/name":       db.Name,
  "database.myapp.io/managed-by": "database-operator",
 }

 replicas := db.Spec.Replicas
 if replicas == 0 {
  replicas = 1
 }

 return &appsv1.StatefulSet{
  ObjectMeta: metav1.ObjectMeta{
   Name:      db.Name,
   Namespace: db.Namespace,
   Labels:    labels,
  },
  Spec: appsv1.StatefulSetSpec{
   ServiceName: db.Name,
   Replicas:    &replicas,
   Selector: &metav1.LabelSelector{
    MatchLabels: labels,
   },
   Template: corev1.PodTemplateSpec{
    ObjectMeta: metav1.ObjectMeta{
     Labels: labels,
    },
    Spec: corev1.PodSpec{
     Containers: []corev1.Container{
      {
       Name:  "postgres",
       Image: fmt.Sprintf("postgres:%s", db.Spec.Version),
       Ports: []corev1.ContainerPort{
        {
         Name:          "postgres",
         ContainerPort: 5432,
        },
       },
       Env: []corev1.EnvVar{
        {
         Name: "POSTGRES_PASSWORD",
         ValueFrom: &corev1.EnvVarSource{
          SecretKeyRef: &corev1.SecretKeySelector{
           LocalObjectReference: corev1.LocalObjectReference{
            Name: db.Name + "-secret",
           },
           Key: "password",
          },
         },
        },
       },
       Resources: corev1.ResourceRequirements{
        Requests: corev1.ResourceList{
         corev1.ResourceCPU:    resource.MustParse(db.Spec.Resources.Requests.CPU),
         corev1.ResourceMemory: resource.MustParse(db.Spec.Resources.Requests.Memory),
        },
        Limits: corev1.ResourceList{
         corev1.ResourceCPU:    resource.MustParse(db.Spec.Resources.Limits.CPU),
         corev1.ResourceMemory: resource.MustParse(db.Spec.Resources.Limits.Memory),
        },
       },
       VolumeMounts: []corev1.VolumeMount{
        {
         Name:      "data",
         MountPath: "/var/lib/postgresql/data",
        },
       },
      },
     },
    },
   },
   VolumeClaimTemplates: []corev1.PersistentVolumeClaim{
    {
     ObjectMeta: metav1.ObjectMeta{
      Name: "data",
     },
     Spec: corev1.PersistentVolumeClaimSpec{
      AccessModes: []corev1.PersistentVolumeAccessMode{corev1.ReadWriteOnce},
      Resources: corev1.ResourceRequirements{
       Requests: corev1.ResourceList{
        corev1.ResourceStorage: resource.MustParse(db.Spec.Storage.Size),
       },
      },
      StorageClassName: &db.Spec.Storage.StorageClassName,
     },
    },
   },
  },
 }
}

// updateStatus 更新资源状态
func (r *DatabaseReconciler) updateStatus(ctx context.Context, db *databasev1.Database,
 phase string, err error) (ctrl.Result, error) {

 db.Status.Phase = phase
 db.Status.ObservedGeneration = db.Generation

 condition := metav1.Condition{
  Type:               "Ready",
  Status:             metav1.ConditionTrue,
  ObservedGeneration: db.Generation,
  LastTransitionTime: metav1.Now(),
  Reason:             "Reconciled",
  Message:            "Database is " + phase,
 }

 if err != nil {
  condition.Status = metav1.ConditionFalse
  condition.Reason = "Failed"
  condition.Message = err.Error()
 }

 meta.SetStatusCondition(&db.Status.Conditions, condition)

 if updateErr := r.Status().Update(ctx, db); updateErr != nil {
  return ctrl.Result{}, updateErr
 }

 if err != nil {
  return ctrl.Result{RequeueAfter: time.Minute}, err
 }

 return ctrl.Result{}, nil
}

// SetupWithManager 设置控制器
func (r *DatabaseReconciler) SetupWithManager(mgr ctrl.Manager) error {
 return ctrl.NewControllerManagedBy(mgr).
  For(&databasev1.Database{}).
  Owns(&appsv1.StatefulSet{}).
  Owns(&corev1.Service{}).
  Owns(&corev1.ConfigMap{}).
  Owns(&corev1.Secret{}).
  Complete(r)
}
```

## 五、Helm Operator 与 Ansible Operator

### 5.1 Helm-based Operator

```bash
# 创建 Helm Operator
operator-sdk init --plugins=helm --domain=myapp.io --helm-chart=myrepo/postgres

# 或使用现有 Chart
operator-sdk create api --helm-chart=stable/postgresql \
  --helm-chart-repo=https://charts.bitnami.com/bitnami

# Helm Operator 项目结构
# ├── helm-charts/
# │   └── postgres/           # Helm Chart
# │       ├── Chart.yaml
# │       ├── values.yaml
# │       └── templates/
# ├── config/
# │   ├── crd/
# │   ├── manager/
# │   ├── rbac/
# │   └── samples/
# │       └── cache_v1_postgres.yaml
# └── watches.yaml
```

```yaml
# watches.yaml
- group: cache.myapp.io
  version: v1
  kind: Postgres
  chart: helm-charts/postgres
  overrideValues:
    image.tag: "${POSTGRES_IMAGE_TAG}"
  selector:
    matchLabels:
      app: postgres
```

### 5.2 Ansible-based Operator

```bash
# 创建 Ansible Operator
operator-sdk init --plugins=ansible --domain=myapp.io
operator-sdk create api --group=database --version=v1 --kind=Postgres --generate-role

# Ansible Operator 项目结构
# ├── config/
# ├── playbooks/
# ├── roles/
# │   └── postgres/
# │       ├── tasks/
# │       │   └── main.yml
# │       ├── templates/
# │       └── vars/
# └── watches.yaml
```

```yaml
# watches.yaml
- version: v1
  group: database.myapp.io
  kind: Postgres
  role: postgres
  vars:
    state: present
    replicas: "{{ size | default(1) }}"
  finalizer:
    name: database.myapp.io/finalizer
    role: postgres
    vars:
      state: absent
```

```yaml
# roles/postgres/tasks/main.yml
---
- name: Create PostgreSQL StatefulSet
  k8s:
    state: present
    definition:
      apiVersion: apps/v1
      kind: StatefulSet
      metadata:
        name: "{{ meta.name }}"
        namespace: "{{ meta.namespace }}"
      spec:
        replicas: "{{ replicas }}"
        selector:
          matchLabels:
            app: postgres
        template:
          metadata:
            labels:
              app: postgres
          spec:
            containers:
            - name: postgres
              image: "postgres:{{ version }}"
              ports:
              - containerPort: 5432
```

## 六、Operator 生命周期管理（OLM）

### 6.1 OLM 架构

```
┌─────────────────────────────────────────────────────────────────┐
│                  Operator Lifecycle Manager                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Catalog Source ──► Subscription ──► InstallPlan ──► ClusterServiceVersion
│       │                  │               │                  │    │
│       │                  │               │                  │    │
│       ▼                  ▼               ▼                  ▼    │
│  ┌──────────┐      ┌──────────┐    ┌──────────┐    ┌──────────┐│
│  │Operator  │      │ 自动/手动 │    │ 审批安装  │    │ 运行Operator││
│  │ 目录     │      │ 更新通道  │    │ 版本     │    │ 管理CR    ││
│  └──────────┘      └──────────┘    └──────────┘    └──────────┘│
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 6.2 打包和发布 Operator

```bash
# 生成 Bundle
make bundle VERSION=0.0.1

# 构建和推送 Bundle 镜像
docker build -f bundle.Dockerfile -t myrepo/database-operator-bundle:v0.0.1 .
docker push myrepo/database-operator-bundle:v0.0.1

# 验证 Bundle
operator-sdk bundle validate ./bundle

# 测试安装
operator-sdk run bundle myrepo/database-operator-bundle:v0.0.1

# 生成 Package Manifests
make packagemanifests VERSION=0.0.1

# 提交到 OperatorHub (https://operatorhub.io)
# 1. Fork https://github.com/k8s-operatorhub/community-operators
# 2. 在 operators/ 目录下创建 operator 目录
# 3. 提交 PR
```

## 七、常用 Operator 推荐

| Operator | 用途 | 特点 |
|----------|------|------|
| **Prometheus Operator** | 监控 | 完整的监控栈管理 |
| **Cert-Manager** | 证书管理 | 自动 TLS 证书颁发和续期 |
| **Argo CD Operator** | GitOps | 声明式持续交付 |
| **Strimzi** | Kafka | 简化 Kafka 集群管理 |
| **Zalando Postgres** | PostgreSQL | 生产级数据库集群 |
| **Redis Operator** | Redis | 高可用 Redis 集群 |
| **Vault Operator** | 密钥管理 | HashiCorp Vault 管理 |
| **Knative Operator** | Serverless | Knative 组件管理 |

## 八、最佳实践

### 8.1 Operator 开发准则

1. **单一职责**：一个 Operator 管理一类应用
2. **幂等性**：多次执行结果一致
3. **水平触发**：基于期望状态持续调和
4. **优雅降级**：部分失败时保持可用
5. **observability**：提供充分的指标和日志
6. **安全**：最小权限，不使用 cluster-admin
7. **升级平滑**：支持无中断升级

### 8.2 测试策略

```bash
# 单元测试
go test ./controllers/... -v

# 集成测试 (envtest)
make test

# 端到端测试
make e2e

# Scorecard 测试
operator-sdk scorecard ./bundle
```

Operator 模式是 Kubernetes 扩展的核心机制，通过将运维知识编码为软件，实现了复杂应用的自动化管理。掌握 Operator 开发可以大大提升 Kubernetes 平台的自动化和运维能力。
