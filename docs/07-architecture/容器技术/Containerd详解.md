# Containerd 详解

## 一、概述

Containerd 是一个行业标准的容器运行时，强调简单性、健壮性和可移植性。它最初是 Docker 项目的一部分，在 2015 年捐赠给云原生计算基金会（CNCF），并于 2019 年成为 CNCF 毕业项目。作为 Kubernetes 的默认容器运行时，Containerd 在现代云原生架构中扮演着核心角色。

## 二、Containerd 架构设计

### 2.1 整体架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           Client Layer                                   │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐ │
│  │  ctr CLI    │  │  nerdctl    │  │  crictl     │  │  Kubernetes     │ │
│  │  (调试工具)  │  │  (Docker兼容)│  │  (K8s调试)   │  │  (CRI Plugin)   │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────────┘ │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼ gRPC API
┌─────────────────────────────────────────────────────────────────────────┐
│                      Containerd Daemon (containerd)                      │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                      Core Services                                   │ │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐  │ │
│  │  │  Images  │ │   Push   │ │ Content  │ │ Snapshots│ │ Runtime  │  │ │
│  │  │  (镜像)   │ │   Pull   │ │ (内容存储)│ │ (快照)    │ │ (运行时)  │  │ │
│  │  └──────────┘ └──────────┘ └──────────┘ └──────────┘ └──────────┘  │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
│  ┌─────────────────────────────────────────────────────────────────────┐ │
│  │                      Built-in Plugins                                │ │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────────────────────┐ │ │
│  │  │     CRI      │ │    Events    │ │        Diff/Metadata         │ │ │
│  │  │  (K8s接口)   │ │   (事件)     │ │      (差异/元数据)            │ │ │
│  │  └──────────────┘ └──────────────┘ └──────────────────────────────┘ │ │
│  └─────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
            ┌───────────────────────┼───────────────────────┐
            ▼                       ▼                       ▼
┌──────────────────┐     ┌──────────────────┐    ┌──────────────────┐
│    runc (OCI)    │     │ containerd-shim  │    │    Snapshotter   │
│  ┌──────────────┐│     │  ┌──────────────┐│    │  ┌──────────────┐│
│  │ Namespace隔离 ││     │  │ 管理容器进程  ││    │  │ overlayfs    ││
│  │ Cgroup限制   ││     │  │ 保持容器运行  ││    │  │ btrfs        ││
│  │ 容器进程执行  ││◄────│  │ 转发stdin/out ││    │  │ zfs          ││
│  └──────────────┘│     │  └──────────────┘│    │  │ devmapper    ││
└──────────────────┘     └──────────────────┘    │  └──────────────┘│
                                                 └──────────────────┘
```

### 2.2 核心组件说明

| 组件 | 功能 | 说明 |
|------|------|------|
| **Service Layer** | 核心服务 | 提供镜像、容器、快照等管理功能 |
| **Metadata** | 元数据存储 | 使用 BoltDB 存储容器和镜像元数据 |
| **Content** | 内容存储 | 不可变的内容寻址存储（CAS） |
| **Snapshots** | 快照系统 | 管理文件系统分层和挂载点 |
| **Runtime** | 运行时管理 | 通过 shim 调用 OCI 运行时 |
| **CRI Plugin** | K8s 接口 | 实现 Kubernetes CRI 规范 |

## 三、Containerd 与 Docker 对比

### 3.1 架构对比

```
Docker 架构：                                      Containerd 架构：
┌─────────────────────┐                          ┌─────────────────────┐
│     Docker CLI      │                          │    ctr/nerdctl      │
└──────────┬──────────┘                          └──────────┬──────────┘
           │                                               │
           ▼                                               ▼
┌─────────────────────┐                          ┌─────────────────────┐
│   Docker Daemon     │                          │    Containerd       │
│  ┌───────────────┐  │                          │  ┌───────────────┐  │
│  │  REST API     │  │                          │  │  gRPC API     │  │
│  │  Image Mgmt   │  │                          │  │  Core Services│  │
│  │  Network/Volume│ │                          │  │  CRI Plugin   │  │
│  └───────────────┘  │                          │  └───────────────┘  │
└──────────┬──────────┘                          └──────────┬──────────┘
           │                                               │
           ▼                                               ▼
┌─────────────────────┐                          ┌─────────────────────┐
│    containerd       │                          │      runc/shim      │
│  ┌───────────────┐  │                          │  ┌───────────────┐  │
│  │  gRPC Server  │  │                          │  │ OCI Runtime   │  │
│  │  Task Mgmt    │  │                          │  │ Namespace隔离 │  │
│  └───────────────┘  │                          │  └───────────────┘  │
└──────────┬──────────┘                          └─────────────────────┘
           ▼
┌─────────────────────┐
│    containerd-shim  │
└──────────┬──────────┘
           ▼
┌─────────────────────┐
│    runc (OCI)       │
└─────────────────────┘
```

### 3.2 功能对比

| 特性 | Docker | Containerd |
|------|--------|------------|
| 镜像管理 | ✅ | ✅ |
| 容器生命周期 | ✅ | ✅ |
| 网络管理 | 内置 | 通过 CNI |
| 卷管理 | 内置 | 通过插件 |
| 构建镜像 | ✅ | ❌（需 buildkit） |
| 命令行工具 | docker | ctr/nerdctl |
| CRI 支持 | 需 dockershim | 原生支持 |
| 资源占用 | 较高 | 轻量 |
| 启动速度 | 较慢 | 快 |

## 四、Containerd 安装与配置

### 4.1 安装 Containerd

```bash
# 下载 containerd
wget https://github.com/containerd/containerd/releases/download/v1.7.11/containerd-1.7.11-linux-amd64.tar.gz

# 解压安装
sudo tar Cxzvf /usr/local containerd-1.7.11-linux-amd64.tar.gz

# 安装 runc
wget https://github.com/opencontainers/runc/releases/download/v1.1.10/runc.amd64
sudo install -m 755 runc.amd64 /usr/local/sbin/runc

# 安装 CNI 插件
wget https://github.com/containernetworking/plugins/releases/download/v1.4.0/cni-plugins-linux-amd64-v1.4.0.tgz
sudo mkdir -p /opt/cni/bin
sudo tar Cxzvf /opt/cni/bin cni-plugins-linux-amd64-v1.4.0.tgz

# 创建 systemd 服务
sudo mkdir -p /etc/containerd
containerd config default | sudo tee /etc/containerd/config.toml

sudo tee /etc/systemd/system/containerd.service > /dev/null <<EOF
[Unit]
Description=containerd container runtime
Documentation=https://containerd.io
After=network.target

[Service]
ExecStartPre=/sbin/modprobe overlay
ExecStart=/usr/local/bin/containerd
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
EOF

# 启动服务
sudo systemctl daemon-reload
sudo systemctl enable --now containerd
```

### 4.2 配置文件详解

```toml
# /etc/containerd/config.toml

# 根目录配置
root = "/var/lib/containerd"
state = "/run/containerd"

# gRPC 配置
[grpc]
address = "/run/containerd/containerd.sock"
gid = 0
max_recv_message_size = 16777216
max_send_message_size = 16777216

# 调试配置
[debug]
address = "/run/containerd/debug.sock"
level = "info"

# 指标配置
[metrics]
address = "0.0.0.0:1338"

# CRI 插件配置
[plugins."io.containerd.grpc.v1.cri"]
# 沙箱镜像
sandbox_image = "registry.k8s.io/pause:3.9"

[plugins."io.containerd.grpc.v1.cri".containerd]
# 默认运行时
default_runtime_name = "runc"

[plugins."io.containerd.grpc.v1.cri".containerd.runtimes.runc]
# 运行时类型
runtime_type = "io.containerd.runc.v2"

[plugins."io.containerd.grpc.v1.cri".containerd.runtimes.runc.options]
# 使用 systemd cgroup
SystemdCgroup = true

[plugins."io.containerd.grpc.v1.cri".cni]
# CNI 配置路径
bin_dir = "/opt/cni/bin"
conf_dir = "/etc/cni/net.d"

# 镜像仓库配置
[plugins."io.containerd.grpc.v1.cri".registry]
[plugins."io.containerd.grpc.v1.cri".registry.mirrors]
[plugins."io.containerd.grpc.v1.cri".registry.mirrors."docker.io"]
endpoint = ["https://mirror.ccs.tencentyun.com", "https://registry-1.docker.io"]

# 私有仓库认证
[plugins."io.containerd.grpc.v1.cri".registry.configs."myregistry.io".auth]
username = "admin"
password = "password123"
```

## 五、ctr 命令行工具使用

### 5.1 镜像管理

```bash
# 拉取镜像
ctr images pull docker.io/library/nginx:alpine

# 列出镜像
ctr images list

# 导出镜像
ctr images export nginx.tar docker.io/library/nginx:alpine

# 导入镜像
ctr images import nginx.tar

# 删除镜像
ctr images remove docker.io/library/nginx:alpine

# 挂载镜像（查看内容）
ctr images mount docker.io/library/nginx:alpine /mnt/nginx

# 取消挂载
ctr images unmount /mnt/nginx
```

### 5.2 容器管理

```bash
# 创建容器
ctr run -d --net-host docker.io/library/nginx:alpine nginx-test

# 列出容器
tr containers list

# 查看容器信息
ctr containers info nginx-test

# 启动/停止/删除容器
tr tasks start nginx-test
tr tasks pause nginx-test
tr tasks resume nginx-test
tr tasks kill -9 nginx-test
tr containers delete nginx-test

# 进入容器
tr tasks exec --exec-id shell -t nginx-test /bin/sh

# 查看容器资源使用
tr tasks metrics nginx-test
```

### 5.3 Namespace 管理

```bash
# 列出命名空间
tr namespace list

# 创建命名空间
tr namespace create production

# 在指定命名空间操作
tr -n production images pull docker.io/library/redis:alpine
tr -n production run -d docker.io/library/redis:alpine redis-prod

# 删除命名空间
tr namespace remove production
```

## 六、nerdctl 使用指南

nerdctl 是 Docker 兼容的 CLI 工具，提供与 docker 命令几乎相同的体验。

### 6.1 安装 nerdctl

```bash
# 下载 nerdctl
wget https://github.com/containerd/nerdctl/releases/download/v1.7.2/nerdctl-1.7.2-linux-amd64.tar.gz

# 解压安装
sudo tar Cxzvf /usr/local/bin nerdctl-1.7.2-linux-amd64.tar.gz

# 验证安装
nerdctl version
```

### 6.2 基本命令

```bash
# 镜像操作（与 docker 相同）
nerdctl pull nginx:alpine
nerdctl images
nerdctl rmi nginx:alpine

# 容器操作（与 docker 相同）
nerdctl run -d -p 80:80 --name my-nginx nginx:alpine
nerdctl ps -a
nerdctl stop my-nginx
nerdctl start my-nginx
nerdctl rm my-nginx

# 进入容器
nerdctl exec -it my-nginx /bin/sh

# 查看日志
nerdctl logs -f my-nginx

# 构建镜像（需要 buildkit）
nerdctl build -t myapp:latest .

# 网络管理
nerdctl network create my-bridge
nerdctl network ls
nerdctl run -d --network my-bridge --name app nginx:alpine

# 卷管理
nerdctl volume create my-data
nerdctl run -d -v my-data:/data nginx:alpine

# Compose 支持
nerdctl compose up -d
nerdctl compose down
```

### 6.3 Docker 与 nerdctl 命令对照

| Docker 命令 | nerdctl 命令 | 说明 |
|-------------|--------------|------|
| docker pull | nerdctl pull | 拉取镜像 |
| docker push | nerdctl push | 推送镜像 |
| docker run | nerdctl run | 运行容器 |
| docker ps | nerdctl ps | 列出容器 |
| docker exec | nerdctl exec | 执行命令 |
| docker logs | nerdctl logs | 查看日志 |
| docker build | nerdctl build | 构建镜像 |
| docker compose | nerdctl compose | 编排服务 |
| docker network | nerdctl network | 网络管理 |
| docker volume | nerdctl volume | 卷管理 |

## 七、CRI 与 Kubernetes 集成

### 7.1 CRI 架构

```
┌─────────────────────────────────────────────────────────────┐
│                     Kubernetes (kubelet)                     │
│                    ┌─────────────────┐                      │
│                    │   CRI Client    │                      │
│                    │  (gRPC Client)  │                      │
│                    └────────┬────────┘                      │
└─────────────────────────────┼───────────────────────────────┘
                              │ CRI API (gRPC)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│              Containerd with CRI Plugin                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Image     │  │  Runtime    │  │    PodSandbox       │  │
│  │   Service   │  │   Service   │  │     Service         │  │
│  │             │  │             │  │                     │  │
│  │ PullImage   │  │ CreateContainer│  │ RunPodSandbox    │  │
│  │ RemoveImage │  │ StartContainer │  │ StopPodSandbox   │  │
│  │ ListImages  │  │ StopContainer  │  │ RemovePodSandbox │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
```

### 7.2 CRI 核心接口

```protobuf
// CRI API 定义（简化）
service RuntimeService {
    // Pod 沙箱管理
    rpc RunPodSandbox(RunPodSandboxRequest) returns (RunPodSandboxResponse);
    rpc StopPodSandbox(StopPodSandboxRequest) returns (StopPodSandboxResponse);
    rpc RemovePodSandbox(RemovePodSandboxRequest) returns (RemovePodSandboxResponse);

    // 容器管理
    rpc CreateContainer(CreateContainerRequest) returns (CreateContainerResponse);
    rpc StartContainer(StartContainerRequest) returns (StartContainerResponse);
    rpc StopContainer(StopContainerRequest) returns (StopContainerResponse);
    rpc RemoveContainer(RemoveContainerRequest) returns (RemoveContainerResponse);

    // 执行和日志
    rpc ExecSync(ExecSyncRequest) returns (ExecSyncResponse);
    rpc Attach(AttachRequest) returns (AttachResponse);
    rpc ContainerStats(ContainerStatsRequest) returns (ContainerStatsResponse);
}

service ImageService {
    rpc ListImages(ListImagesRequest) returns (ListImagesResponse);
    rpc PullImage(PullImageRequest) returns (PullImageResponse);
    rpc RemoveImage(RemoveImageRequest) returns (RemoveImageResponse);
    rpc ImageFsInfo(ImageFsInfoRequest) returns (ImageFsInfoResponse);
}
```

### 7.3 Kubernetes 配置 Containerd

```bash
# 配置 kubelet 使用 containerd
sudo tee /var/lib/kubelet/config.yaml > /dev/null <<EOF
apiVersion: kubelet.config.k8s.io/v1beta1
kind: KubeletConfiguration
cgroupDriver: systemd
containerRuntimeEndpoint: unix:///run/containerd/containerd.sock
EOF

# 验证 CRI 接口
crictl --runtime-endpoint unix:///run/containerd/containerd.sock version

# 常用 crictl 命令
crictl images                    # 列出镜像
crictl ps -a                     # 列出容器
crictl pods                      # 列出 Pod
crictl logs <container-id>       # 查看日志
crictl exec -it <container-id> sh # 进入容器
crictl stats                     # 查看资源使用
```

## 八、Snapshotter 详解

### 8.1 Snapshotter 架构

```
┌─────────────────────────────────────────────────────────────┐
│                      Snapshotter Interface                   │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Prepare   │  │    View     │  │      Mount          │  │
│  │  (准备层)    │  │  (只读视图)  │  │    (挂载点)          │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Commit    │  │   Remove    │  │      Stat           │  │
│  │  (提交层)    │  │   (删除层)   │  │    (统计信息)        │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                     ▼
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│  overlayfs   │     │    btrfs     │     │     zfs      │
│  (默认)       │     │              │     │              │
└──────────────┘     └──────────────┘     └──────────────┘
```

### 8.2 配置 Snapshotter

```toml
# /etc/containerd/config.toml
[plugins."io.containerd.grpc.v1.cri".containerd]
default_runtime_name = "runc"
snapshotter = "overlayfs"  # 可选: overlayfs, btrfs, zfs, devmapper

# btrfs snapshotter 配置
[plugins."io.containerd.snapshotter.v1.btrfs"]
root_path = "/var/lib/containerd/snapshots/btrfs"

# devmapper snapshotter 配置
[plugins."io.containerd.snapshotter.v1.devmapper"]
pool_name = "containerd-pool"
root_path = "/var/lib/containerd/snapshots/devmapper"
base_image_size = "10GB"
```

## 九、Containerd 插件系统

### 9.1 插件类型

```
┌─────────────────────────────────────────────────────────────┐
│                    Containerd 插件类型                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────┐    ┌─────────────────┐                │
│  │  Internal Plugins│    │  External Plugins│               │
│  │  (内置插件)      │    │  (外部插件)       │               │
│  ├─────────────────┤    ├─────────────────┤                │
│  │ • Content        │    │ • gRPC 服务插件   │               │
│  │ • Snapshotter    │    │ • Runtime 插件    │               │
│  │ • Runtime        │    │ • 自定义处理器    │               │
│  │ • Metadata       │    │                  │               │
│  │ • GC             │    │                  │               │
│  └─────────────────┘    └─────────────────┘                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 9.2 开发自定义插件

```go
// 自定义 Snapshotter 插件示例
package main

import (
    "context"
    "github.com/containerd/containerd/snapshots"
    "github.com/containerd/containerd/plugin"
)

func init() {
    plugin.Register(&plugin.Registration{
        Type: plugin.SnapshotPlugin,
        ID:   "custom",
        InitFn: func(ic *plugin.InitContext) (interface{}, error) {
            return NewCustomSnapshotter(ic.Root)
        },
    })
}

type CustomSnapshotter struct {
    root string
}

func NewCustomSnapshotter(root string) (snapshots.Snapshotter, error) {
    return &CustomSnapshotter{root: root}, nil
}

func (s *CustomSnapshotter) Prepare(ctx context.Context, key, parent string, opts ...snapshots.Opt) ([]mount.Mount, error) {
    // 实现准备逻辑
}

func (s *CustomSnapshotter) View(ctx context.Context, key, parent string, opts ...snapshots.Opt) ([]mount.Mount, error) {
    // 实现视图逻辑
}

func (s *CustomSnapshotter) Commit(ctx context.Context, name, key string, opts ...snapshots.Opt) error {
    // 实现提交逻辑
}
// ... 其他接口方法
```

## 十、性能优化与监控

### 10.1 性能调优

```toml
# /etc/containerd/config.toml

# 并行镜像拉取
[plugins."io.containerd.grpc.v1.cri"]
max_concurrent_downloads = 3

# 垃圾回收配置
[gc]
default_policy = "keep-all"  # 或 "keep-last-n"

# 内容存储配置
[plugins."io.containerd.service.v1.diff-service"]
default = ["walking"]

# 运行时配置优化
[plugins."io.containerd.grpc.v1.cri".containerd.runtimes.runc.options]
SystemdCgroup = true
no_shim = false
```

### 10.2 监控指标

```bash
# 启用 Prometheus 指标
curl http://localhost:1338/v1/metrics

# 关键指标
# containerd_container_cpu_usage_seconds_total
# containerd_container_memory_usage_bytes
# containerd_container_spec_memory_limit_bytes
# containerd_snapshotter_usage_bytes
# containerd_image_size_bytes

# 使用 cAdvisor 监控
docker run -d \
  --volume=/:/rootfs:ro \
  --volume=/var/run:/var/run:ro \
  --volume=/sys:/sys:ro \
  --volume=/var/lib/containerd/:/var/lib/containerd:ro \
  --publish=8080:8080 \
  gcr.io/cadvisor/cadvisor:latest
```

## 十一、故障排查

### 11.1 常见问题诊断

```bash
# 查看 containerd 状态
sudo systemctl status containerd

# 查看详细日志
sudo journalctl -u containerd -f

# 检查 CRI 接口
crictl info

# 查看容器运行时
crictl pods -v
crictl ps -v

# 检查 namespace
tr namespace list
tr -n <namespace> containers list

# 检查 shim 进程
ps aux | grep containerd-shim

# 查看 socket
curl -s --unix-socket /run/containerd/containerd.sock \
  http://localhost/v1/version
```

### 11.2 调试模式

```bash
# 启用 debug 日志
sudo tee /etc/containerd/config.toml > /dev/null <<EOF
version = 2
[debug]
level = "debug"
address = "/run/containerd/debug.sock"
EOF

sudo systemctl restart containerd

# 使用 ctr 调试
tr -d plugins list
tr -d snapshots list
tr -d content ls
```

## 十二、总结

Containerd 作为云原生时代的核心容器运行时，具有以下优势：

1. **轻量高效**：相比 Docker 更轻量，资源占用更少
2. **标准兼容**：完整实现 OCI 和 CRI 规范
3. **插件架构**：灵活的插件系统便于扩展
4. **生产就绪**：经过大规模生产环境验证
5. **生态丰富**：与 Kubernetes、nerdctl 等工具无缝集成

在生产环境中使用 Containerd 时，建议：

- 使用 nerdctl 替代 ctr 获得更好的用户体验
- 配置镜像加速和私有仓库认证
- 启用 SystemdCgroup 以更好地与 systemd 集成
- 定期清理无用镜像和容器释放空间
- 配置合适的监控和告警机制
