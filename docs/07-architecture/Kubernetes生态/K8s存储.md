# K8s 存储

## 一、概述

Kubernetes 存储系统为容器化应用提供了数据持久化能力。与容器本身的生命周期不同，存储可以独立于 Pod 存在，确保数据在 Pod 重启、迁移或删除后仍然保留。本章将深入探讨 Kubernetes 的存储架构、资源类型和使用模式。

## 二、Kubernetes 存储架构

### 2.1 存储架构层次

```
┌─────────────────────────────────────────────────────────────┐
│                  Kubernetes 存储架构                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Layer 4: 应用层                                        │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐ │  │
│  │  │   Pod       │  │   Pod       │  │      Pod        │ │  │
│  │  │ ┌─────────┐ │  │ ┌─────────┐ │  │   ┌─────────┐   │ │  │
│  │  │ │Container│ │  │ │Container│ │  │   │Container│   │ │  │
│  │  │ │  Mount  │ │  │ │  Mount  │ │  │   │  Mount  │   │ │  │
│  │  │ │  /data  │ │  │ │  /data  │ │  │   │  /data  │   │ │  │
│  │  │ └─────────┘ │  │ └─────────┘ │  │   └─────────┘   │ │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────┘ │  │
│  └───────────────────────────────────────────────────────┘  │
│                              │                               │
│                              ▼                               │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Layer 3: Kubernetes 抽象层                            │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐ │  │
│  │  │     PVC     │  │     PVC     │  │      PVC        │ │  │
│  │  │  (ReadWrite)│  │(ReadOnlyMany│  │ (ReadWriteMany) │ │  │
│  │  └──────┬──────┘  └──────┬──────┘  └────────┬────────┘ │  │
│  │         │                │                   │          │  │
│  │         └────────────────┴───────────────────┘          │  │
│  │                          │                               │  │
│  │                   ┌──────┴──────┐                        │  │
│  │                   │     PV      │                        │  │
│  │                   │  (实际存储)  │                        │  │
│  │                   └─────────────┘                        │  │
│  └───────────────────────────────────────────────────────┘  │
│                              │                               │
│                              ▼                               │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Layer 2: 存储编排层                                    │  │
│  │  ┌─────────────────────────────────────────────────┐  │  │
│  │  │  StorageClass (动态供应配置)                      │  │  │
│  │  │  - Provisioner: ebs.csi.aws.com                 │  │  │
│  │  │  - Parameters: type=gp3, encrypted=true         │  │  │
│  │  │  - ReclaimPolicy: Delete/Retain                 │  │  │
│  │  └─────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────┘  │
│                              │                               │
│                              ▼                               │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  Layer 1: 基础设施层                                    │  │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌───────────┐ │  │
│  │  │  AWS EBS │ │  NFS     │ │  Ceph    │ │  Local SSD│ │  │
│  │  │  GCP PD  │ │  Gluster │ │  MinIO   │ │  HostPath │ │  │
│  │  │  Azure Disk│ │  S3    │ │  Portworx│ │  tmpfs    │ │  │
│  │  └──────────┘ └──────────┘ └──────────┘ └───────────┘ │  │
│  └───────────────────────────────────────────────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 存储资源关系

```
┌─────────────────────────────────────────────────────────────────┐
│                     存储资源关系图                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Pod ──► claims ──► PVC ──► binds ──► PV ──► provisions ──► Storage│
│                      │                │                         │
│                      │                │                         │
│                      ▼                ▼                         │
│                 ┌─────────┐      ┌─────────┐                   │
│                 │ Storage │      │ Storage │                   │
│                 │ Class   │      │ Class   │                   │
│                 └─────────┘      └─────────┘                   │
│                                                                  │
│  静态供应:                                                       │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  管理员手动创建 PV ──► 用户创建 PVC ──► PVC 绑定 PV       │   │
│  │       (Pre-provisioned)         (Claim)                 │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
│  动态供应:                                                       │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  用户创建 PVC + StorageClass ──► 自动创建 PV ──► 绑定   │   │
│  │       (On-demand provision)                             │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## 三、卷类型详解

### 3.1 临时存储卷

```yaml
# emptyDir - 空目录卷
apiVersion: v1
kind: Pod
metadata:
  name: emptydir-pod
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: cache
      mountPath: /cache
  volumes:
  - name: cache
    emptyDir:
      medium: Memory  # 使用内存作为存储（tmpfs）
      sizeLimit: 500Mi

---
# configMap - 配置卷
apiVersion: v1
kind: Pod
metadata:
  name: configmap-pod
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: config
      mountPath: /etc/nginx/conf.d
      readOnly: true
  volumes:
  - name: config
    configMap:
      name: nginx-config
      items:
      - key: default.conf
        path: default.conf
      defaultMode: 0644

---
# secret - 密钥卷
apiVersion: v1
kind: Pod
metadata:
  name: secret-pod
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: tls
      mountPath: /etc/nginx/ssl
      readOnly: true
  volumes:
  - name: tls
    secret:
      secretName: tls-secret
      items:
      - key: tls.crt
        path: cert.pem
      - key: tls.key
        path: key.pem

---
# downwardAPI - 元数据卷
apiVersion: v1
kind: Pod
metadata:
  name: downward-api-pod
  labels:
    app: myapp
    version: v1
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: podinfo
      mountPath: /etc/podinfo
  volumes:
  - name: podinfo
    downwardAPI:
      items:
      - path: "labels"
        fieldRef:
          fieldPath: metadata.labels
      - path: "annotations"
        fieldRef:
          fieldPath: metadata.annotations
      - path: "name"
        fieldRef:
          fieldPath: metadata.name
      - path: "namespace"
        fieldRef:
          fieldPath: metadata.namespace
```

### 3.2 持久存储卷

```yaml
# hostPath - 主机路径（仅单节点测试）
apiVersion: v1
kind: Pod
metadata:
  name: hostpath-pod
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: data
      mountPath: /data
  volumes:
  - name: data
    hostPath:
      path: /var/lib/mydata
      type: DirectoryOrCreate

---
# nfs - 网络文件系统
apiVersion: v1
kind: Pod
metadata:
  name: nfs-pod
spec:
  containers:
  - name: app
    image: nginx:alpine
    volumeMounts:
    - name: nfs-volume
      mountPath: /usr/share/nginx/html
  volumes:
  - name: nfs-volume
    nfs:
      server: 192.168.1.100
      path: /exports/web
      readOnly: false

---
# local - 本地持久卷（需要 PV 预创建）
apiVersion: v1
kind: Pod
metadata:
  name: local-pod
spec:
  containers:
  - name: app
    image: postgres:15
    volumeMounts:
    - name: pgdata
      mountPath: /var/lib/postgresql/data
  volumes:
  - name: pgdata
    persistentVolumeClaim:
      claimName: local-pvc

---
# CSI 卷（以 AWS EBS 为例）
apiVersion: v1
kind: Pod
metadata:
  name: ebs-pod
spec:
  containers:
  - name: app
    image: mysql:8.0
    volumeMounts:
    - name: mysql-data
      mountPath: /var/lib/mysql
  volumes:
  - name: mysql-data
    persistentVolumeClaim:
      claimName: ebs-pvc
```

## 四、PV 与 PVC

### 4.1 PersistentVolume (PV)

```yaml
# 静态供应 PV 示例
apiVersion: v1
kind: PersistentVolume
metadata:
  name: nfs-pv-001
  labels:
    type: nfs
    env: production
spec:
  capacity:
    storage: 100Gi
  volumeMode: Filesystem
  accessModes:
    - ReadWriteMany
  persistentVolumeReclaimPolicy: Retain
  storageClassName: nfs-slow
  mountOptions:
    - hard
    - nfsvers=4.1
  nfs:
    server: 192.168.1.100
    path: /exports/pv001

---
# AWS EBS PV
apiVersion: v1
kind: PersistentVolume
metadata:
  name: ebs-pv-001
  annotations:
    pv.kubernetes.io/provisioned-by: ebs.csi.aws.com
spec:
  capacity:
    storage: 50Gi
  volumeMode: Block  # 块设备模式
  accessModes:
    - ReadWriteOnce
  persistentVolumeReclaimPolicy: Delete
  storageClassName: gp3
  csi:
    driver: ebs.csi.aws.com
    volumeHandle: vol-0a1b2c3d4e5f67890
    fsType: ext4
    volumeAttributes:
      encrypted: "true"

---
# Local PV
apiVersion: v1
kind: PersistentVolume
metadata:
  name: local-pv-001
spec:
  capacity:
    storage: 500Gi
  volumeMode: Filesystem
  accessModes:
    - ReadWriteOnce
  persistentVolumeReclaimPolicy: Delete
  storageClassName: local-ssd
  local:
    path: /mnt/disks/ssd1
  nodeAffinity:
    required:
      nodeSelectorTerms:
      - matchExpressions:
        - key: kubernetes.io/hostname
          operator: In
          values:
          - node-1
```

### 4.2 PersistentVolumeClaim (PVC)

```yaml
# 基本 PVC
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: app-pvc
  namespace: production
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 10Gi
  storageClassName: gp3

---
# 选择器匹配 PVC
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: nfs-pvc
spec:
  accessModes:
    - ReadWriteMany
  resources:
    requests:
      storage: 100Gi
  selector:
    matchLabels:
      type: nfs
      env: production

---
# 数据卷快照恢复 PVC
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: restored-pvc
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 50Gi
  dataSource:
    name: my-snapshot
    kind: VolumeSnapshot
    apiGroup: snapshot.storage.k8s.io

---
# 克隆 PVC
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: cloned-pvc
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 50Gi
  dataSource:
    name: source-pvc
    kind: PersistentVolumeClaim
```

### 4.3 访问模式详解

| 访问模式 | 缩写 | 说明 | 适用场景 |
|----------|------|------|----------|
| ReadWriteOnce | RWO | 单节点读写 | 数据库、大多数应用 |
| ReadOnlyMany | ROX | 多节点只读 | 静态资源、配置分发 |
| ReadWriteMany | RWX | 多节点读写 | 共享存储、内容管理 |
| ReadWriteOncePod | RWOP | 单 Pod 读写 | Kubernetes 1.22+ |

```yaml
# RWX 使用示例
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-servers
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
        volumeMounts:
        - name: shared-data
          mountPath: /usr/share/nginx/html
      volumes:
      - name: shared-data
        persistentVolumeClaim:
          claimName: nfs-rwx-pvc
---
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: nfs-rwx-pvc
spec:
  accessModes:
    - ReadWriteMany
  resources:
    requests:
      storage: 100Gi
  storageClassName: nfs-client
```

## 五、StorageClass

### 5.1 StorageClass 配置

```yaml
# AWS EBS gp3 StorageClass
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: ebs-gp3
  annotations:
    storageclass.kubernetes.io/is-default-class: "true"
provisioner: ebs.csi.aws.com
volumeBindingMode: WaitForFirstConsumer
allowVolumeExpansion: true
parameters:
  type: gp3
  encrypted: "true"
  kmsKeyId: alias/aws/ebs
  iops: "3000"
  throughput: "125"
  fsType: ext4
reclaimPolicy: Delete

---
# NFS Client StorageClass
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: nfs-client
provisioner: cluster.local/nfs-client-provisioner
parameters:
  archiveOnDelete: "true"
  pathPattern: "${.PVC.namespace}/${.PVC.name}"
reclaimPolicy: Delete
volumeBindingMode: Immediate

---
# Local SSD StorageClass
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: local-ssd
provisioner: kubernetes.io/no-provisioner
volumeBindingMode: WaitForFirstConsumer
reclaimPolicy: Delete

---
# Ceph RBD StorageClass
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: ceph-rbd
provisioner: rbd.csi.ceph.com
parameters:
  clusterID: rook-ceph
  pool: replicapool
  imageFormat: "2"
  imageFeatures: layering
  csi.storage.k8s.io/provisioner-secret-name: rook-csi-rbd-provisioner
  csi.storage.k8s.io/provisioner-secret-namespace: rook-ceph
  csi.storage.k8s.io/node-stage-secret-name: rook-csi-rbd-node
  csi.storage.k8s.io/node-stage-secret-namespace: rook-ceph
reclaimPolicy: Delete
allowVolumeExpansion: true
volumeBindingMode: Immediate
```

### 5.2 卷绑定模式

```yaml
# Immediate 模式 - 立即绑定
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: immediate-sc
provisioner: ebs.csi.aws.com
volumeBindingMode: Immediate  # PVC 创建后立即绑定 PV
reclaimPolicy: Delete

---
# WaitForFirstConsumer 模式 - 延迟绑定
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: delayed-sc
provisioner: ebs.csi.aws.com
volumeBindingMode: WaitForFirstConsumer  # 等 Pod 调度后再绑定
reclaimPolicy: Delete
```

## 六、StatefulSet 存储

### 6.1 StatefulSet 存储模板

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: postgres
  namespace: database
spec:
  serviceName: postgres-headless
  replicas: 3
  podManagementPolicy: OrderedReady
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
        image: postgres:15-alpine
        ports:
        - containerPort: 5432
        env:
        - name: POSTGRES_USER
          value: postgres
        - name: POSTGRES_PASSWORD
          valueFrom:
            secretKeyRef:
              name: postgres-secret
              key: password
        - name: PGDATA
          value: /var/lib/postgresql/data/pgdata
        volumeMounts:
        - name: data
          mountPath: /var/lib/postgresql/data
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes:
        - ReadWriteOnce
      storageClassName: ebs-gp3
      resources:
        requests:
          storage: 50Gi
```

### 6.2 生成的 PVC 命名规则

```
StatefulSet: postgres (3 replicas)

生成 PVC:
├── data-postgres-0  (绑定到 Pod postgres-0)
├── data-postgres-1  (绑定到 Pod postgres-1)
└── data-postgres-2  (绑定到 Pod postgres-2)

命名规则: <volumeClaimTemplate-name>-<statefulset-name>-<ordinal>
```

## 七、CSI（容器存储接口）

### 7.1 CSI 架构

```
┌─────────────────────────────────────────────────────────────┐
│                    CSI 架构                                  │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Kubernetes                                                  │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              External Provisioner                    │    │
│  │         (监听 PVC，调用 CSI CreateVolume)           │    │
│  └────────────────────────┬────────────────────────────┘    │
│                           │                                  │
│                           ▼                                  │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              External Attacher                       │    │
│  │       (监听 VolumeAttachment，调用 Controller)       │    │
│  └────────────────────────┬────────────────────────────┘    │
│                           │                                  │
│                           ▼ gRPC                             │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              CSI Controller                          │    │
│  │  ┌───────────────┐ ┌───────────────┐ ┌───────────┐ │    │
│  │  │ CreateVolume  │ │ DeleteVolume  │ │ Controller│ │    │
│  │  │ ControllerPublish│ ControllerUnpublish│ExpandVolume│   │
│  │  └───────────────┘ └───────────────┘ └───────────┘ │    │
│  └────────────────────────┬────────────────────────────┘    │
│                           │                                  │
│                           ▼                                  │
│  ┌─────────────────────────────────────────────────────┐    │
│  │           Storage Backend (AWS/GCP/Ceph等)           │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                              │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              CSI Node Driver                         │    │
│  │  (运行在每个节点，处理 mount/format/attach)           │    │
│  │  ┌───────────────┐ ┌───────────────┐ ┌───────────┐ │    │
│  │  │ NodeStage     │ │ NodePublish   │ │ NodeExpand│ │    │
│  │  │ Volume        │ │ Volume        │ │ Volume    │ │    │
│  │  └───────────────┘ └───────────────┘ └───────────┘ │    │
│  └─────────────────────────────────────────────────────┘    │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 7.2 CSI 部署示例

```yaml
# CSI 驱动部署 (以 AWS EBS 为例)
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ebs-csi-controller
  namespace: kube-system
spec:
  replicas: 2
  selector:
    matchLabels:
      app: ebs-csi-controller
  template:
    metadata:
      labels:
        app: ebs-csi-controller
    spec:
      serviceAccountName: ebs-csi-controller-sa
      containers:
      - name: ebs-plugin
        image: public.ecr.aws/ebs-csi-driver/aws-ebs-csi-driver:v1.24.0
        args:
        - --endpoint=$(CSI_ENDPOINT)
        - --v=5
        env:
        - name: CSI_ENDPOINT
          value: unix:///var/lib/csi/sockets/pluginproxy/csi.sock
        volumeMounts:
        - name: socket-dir
          mountPath: /var/lib/csi/sockets/pluginproxy/
      - name: csi-provisioner
        image: registry.k8s.io/sig-storage/csi-provisioner:v3.5.0
        args:
        - --csi-address=$(ADDRESS)
        - --v=5
        - --feature-gates=Topology=true
        env:
        - name: ADDRESS
          value: /var/lib/csi/sockets/pluginproxy/csi.sock
        volumeMounts:
        - name: socket-dir
          mountPath: /var/lib/csi/sockets/pluginproxy/
      - name: csi-attacher
        image: registry.k8s.io/sig-storage/csi-attacher:v4.3.0
        args:
        - --csi-address=$(ADDRESS)
        - --v=5
        env:
        - name: ADDRESS
          value: /var/lib/csi/sockets/pluginproxy/csi.sock
        volumeMounts:
        - name: socket-dir
          mountPath: /var/lib/csi/sockets/pluginproxy/
      volumes:
      - name: socket-dir
        emptyDir: {}

---
# CSI Node DaemonSet
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: ebs-csi-node
  namespace: kube-system
spec:
  selector:
    matchLabels:
      app: ebs-csi-node
  template:
    metadata:
      labels:
        app: ebs-csi-node
    spec:
      hostNetwork: true
      containers:
      - name: ebs-plugin
        image: public.ecr.aws/ebs-csi-driver/aws-ebs-csi-driver:v1.24.0
        args:
        - --endpoint=$(CSI_ENDPOINT)
        - --v=5
        env:
        - name: CSI_ENDPOINT
          value: unix:/csi/csi.sock
        securityContext:
          privileged: true
        volumeMounts:
        - name: kubelet-dir
          mountPath: /var/lib/kubelet
          mountPropagation: Bidirectional
        - name: plugin-dir
          mountPath: /csi
      volumes:
      - name: kubelet-dir
        hostPath:
          path: /var/lib/kubelet
          type: Directory
      - name: plugin-dir
        hostPath:
          path: /var/lib/kubelet/plugins/ebs.csi.aws.com/
          type: DirectoryOrCreate
```

## 八、存储快照与克隆

### 8.1 VolumeSnapshot

```yaml
# VolumeSnapshotClass
apiVersion: snapshot.storage.k8s.io/v1
kind: VolumeSnapshotClass
metadata:
  name: ebs-snapshot-class
driver: ebs.csi.aws.com
deletionPolicy: Retain
parameters:
  tagSpecification_1: "Name=kubernetes-snapshot"

---
# 创建快照
apiVersion: snapshot.storage.k8s.io/v1
kind: VolumeSnapshot
metadata:
  name: mysql-snapshot
  namespace: database
spec:
  volumeSnapshotClassName: ebs-snapshot-class
  source:
    persistentVolumeClaimName: mysql-pvc

---
# 从快照恢复
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: mysql-restored
  namespace: database
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 50Gi
  dataSource:
    apiGroup: snapshot.storage.k8s.io
    kind: VolumeSnapshot
    name: mysql-snapshot
```

## 九、存储最佳实践

### 9.1 生产环境建议

```yaml
# 1. 使用延迟绑定避免调度问题
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: production-sc
provisioner: ebs.csi.aws.com
volumeBindingMode: WaitForFirstConsumer  # 关键！
allowVolumeExpansion: true
reclaimPolicy: Retain  # 防止误删数据

---
# 2. 合理设置资源限制
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: database-pvc
  annotations:
    resize.topolvm.io/increase: "10%"
    resize.topolvm.io/threshold: "20%"
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 100Gi
    limits:
      storage: 500Gi  # 设置上限防止无限增长

---
# 3. 使用加密存储
apiVersion: storage.k8s.io/v1
kind: StorageClass
metadata:
  name: encrypted-sc
provisioner: ebs.csi.aws.com
parameters:
  encrypted: "true"
  kmsKeyId: "arn:aws:kms:us-west-2:111122223333:key/1234abcd-12ab-34cd-56ef-1234567890ab"

---
# 4. 备份策略
apiVersion: velero.io/v1
kind: Schedule
metadata:
  name: database-backup
spec:
  schedule: "0 2 * * *"  # 每天凌晨 2 点
  template:
    includedNamespaces:
    - database
    snapshotVolumes: true
    storageLocation: default
    ttl: 720h0m0s  # 保留 30 天
```

### 9.2 常见问题排查

```bash
# 检查 PV/PVC 状态
kubectl get pv,pvc -A
kubectl describe pvc <pvc-name>

# 检查存储类
kubectl get storageclass
kubectl describe storageclass <sc-name>

# 检查 CSI 驱动
kubectl get csidrivers
kubectl get pods -n kube-system -l app=csi-driver

# 查看事件
kubectl get events --field-selector reason=FailedMount

# 检查节点存储
kubectl get nodes -o custom-columns=NAME:.metadata.name,STORAGE:.status.allocatable.ephemeral-storage

# 扩展 PVC
kubectl patch pvc <pvc-name> -p '{"spec":{"resources":{"requests":{"storage":"20Gi"}}}}'
```

## 十、总结

Kubernetes 存储系统提供了灵活的数据持久化能力：

1. **临时存储**：emptyDir、ConfigMap、Secret 适合临时数据和配置
2. **持久存储**：PV/PVC 抽象提供了与具体存储解耦的接口
3. **动态供应**：StorageClass 实现了按需自动创建存储
4. **有状态应用**：StatefulSet 配合 PVC 模板管理有状态工作负载
5. **CSI 标准**：统一的存储接口支持各种存储后端

在生产环境中，建议：

- 使用 `WaitForFirstConsumer` 绑定模式优化调度
- 启用卷扩展能力应对数据增长
- 实施加密保护敏感数据
- 建立定期备份策略
- 监控存储使用率和性能指标
