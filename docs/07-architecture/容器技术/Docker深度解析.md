# Docker深度解析

## 一、概述

Docker 是一个开源的容器化平台，它彻底改变了应用程序的开发、部署和运行方式。通过将应用程序及其依赖打包到标准化的容器中，Docker 实现了"一次构建，到处运行"的理念，解决了传统部署中"在我的机器上可以运行"的困境。

## 二、容器技术原理

### 2.1 容器 vs 虚拟机

容器和虚拟机是两种不同的资源隔离和虚拟化技术：

| 特性 | 容器 | 虚拟机 |
|------|------|--------|
| 启动速度 | 秒级 | 分钟级 |
| 资源占用 | 轻量（MB级） | 重量级（GB级） |
| 性能损耗 | 接近原生（<5%） | 较高（10-20%） |
| 隔离级别 | 进程级 | 操作系统级 |
| 镜像大小 | 小（共享宿主机内核） | 大（完整OS） |
| 密度 | 单机可运行数千个 | 单机通常数十个 |

### 2.2 Linux 容器技术基础

Docker 容器基于 Linux 内核的三大核心技术实现：

```
┌─────────────────────────────────────────────────────────────┐
│                      用户态应用程序                           │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   容器 A     │  │   容器 B     │  │      容器 C          │  │
│  │ ┌─────────┐ │  │ ┌─────────┐ │  │ ┌─────────────────┐ │  │
│  │ │ 应用进程 │ │  │ │ 应用进程 │ │  │ │    应用进程      │ │  │
│  │ │ 独立视图 │ │  │ │ 独立视图 │ │  │ │    独立视图      │ │  │
│  │ └─────────┘ │  │ └─────────┘ │  │ └─────────────────┘ │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
├─────────────────────────────────────────────────────────────┤
│           Namespace（资源隔离） + Cgroup（资源限制）           │
├─────────────────────────────────────────────────────────────┤
│                      Linux 内核                             │
└─────────────────────────────────────────────────────────────┘
```

## 三、Namespace 详解

Namespace 是 Linux 内核提供的一种资源隔离机制，让每个进程拥有独立的系统资源视图。

### 3.1 六种 Namespace 类型

| Namespace | 系统调用参数 | 隔离资源 | 引入内核版本 |
|-----------|-------------|---------|-------------|
| Mount (mnt) | CLONE_NEWNS | 文件系统挂载点 | 2.4.19 |
| Process ID (pid) | CLONE_NEWPID | 进程ID | 2.6.24 |
| Network (net) | CLONE_NEWNET | 网络设备、端口、路由 | 2.6.24 |
| Interprocess Communication (ipc) | CLONE_NEWIPC | 信号量、消息队列、共享内存 | 2.6.19 |
| UTS | CLONE_NEWUTS | 主机名、域名 | 2.6.19 |
| User ID (user) | CLONE_NEWUSER | 用户和组ID | 3.8 |
| Cgroup (cgroup) | CLONE_NEWCGROUP | cgroup根目录 | 4.6 |
| Time (time) | CLONE_NEWTIME | 系统时间 | 5.6 |

### 3.2 Namespace 操作示例

```bash
# 查看当前进程的 Namespace
ls -la /proc/self/ns/

# 输出示例：
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 cgroup -> cgroup:[4026531835]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 ipc -> ipc:[4026531839]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 mnt -> mnt:[4026531840]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 net -> net:[4026532008]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 pid -> pid:[4026531836]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 user -> user:[4026531837]
# lrwxrwxrwx 1 root root 0 Jan  1 00:00 uts -> uts:[4026531838]

# 创建新的 Namespace 并运行命令
sudo unshare --fork --pid --mount-proc /bin/bash

# 在新 Namespace 中查看进程
ps aux
# 只能看到当前 Namespace 的进程
```

### 3.3 PID Namespace 原理

```
宿主机视角：                        容器内视角：
┌─────────────────────┐           ┌─────────────────────┐
│ PID 1: systemd      │           │ PID 1: nginx        │
│ PID 234: dockerd    │           │ PID 7: worker       │
│ PID 345: container  │───映射────→│ PID 12: php-fpm     │
│   ├─ PID 567: nginx │           │                     │
│   ├─ PID 568: worker│           │                     │
│   └─ PID 569: php   │           │                     │
└─────────────────────┘           └─────────────────────┘
```

### 3.4 Network Namespace 详解

```bash
# 创建网络 Namespace
sudo ip netns add ns1
sudo ip netns add ns2

# 查看网络 Namespace 列表
ip netns list

# 在 Namespace 中执行命令
sudo ip netns exec ns1 ip link

# 创建虚拟网卡对（veth pair）连接两个 Namespace
sudo ip link add veth0 type veth peer name veth1
sudo ip link set veth0 netns ns1
sudo ip link set veth1 netns ns2

# 配置 IP 地址
sudo ip netns exec ns1 ip addr add 10.0.0.1/24 dev veth0
sudo ip netns exec ns1 ip link set veth0 up
sudo ip netns exec ns2 ip addr add 10.0.0.2/24 dev veth1
sudo ip netns exec ns2 ip link set veth1 up

# 测试连通性
sudo ip netns exec ns1 ping 10.0.0.2
```

## 四、Cgroup 详解

Cgroup（Control Group）是 Linux 内核提供的资源限制和统计机制。

### 4.1 Cgroup 版本对比

| 特性 | Cgroup v1 | Cgroup v2 |
|------|-----------|-----------|
| 层级结构 | 每个子系统独立 | 统一层级 |
| 控制器数量 | 多个独立控制器 | 统一控制器 |
| 资源控制 | 可能竞争 | 更好的协调 |
| 根用户限制 | 困难 | 原生支持 |
| eBPF 集成 | 有限 | 更好支持 |

### 4.2 Cgroup 子系统

```bash
# 查看 Cgroup 挂载点
mount | grep cgroup

# Cgroup v1 子系统
ls /sys/fs/cgroup/
# blkio    # 块设备 IO 限制
# cpu      # CPU 时间分配
# cpuacct  # CPU 使用统计
# cpuset   # CPU 和内存节点绑定
# devices  # 设备访问控制
# freezer  # 进程挂起/恢复
# hugetlb  # 大页内存限制
# memory   # 内存限制
# net_cls  # 网络分类标记
# net_prio # 网络优先级
# pids     # 进程数量限制
```

### 4.3 Cgroup 操作示例

```bash
# 创建 Cgroup 目录（Cgroup v1）
sudo mkdir /sys/fs/cgroup/memory/mygroup
sudo mkdir /sys/fs/cgroup/cpu/mygroup

# 限制内存使用（100MB）
echo 100M | sudo tee /sys/fs/cgroup/memory/mygroup/memory.limit_in_bytes

# 限制 CPU 使用（相当于 0.5 核）
echo 50000 | sudo tee /sys/fs/cgroup/cpu/mygroup/cpu.cfs_quota_us
echo 100000 | sudo tee /sys/fs/cgroup/cpu/mygroup/cpu.cfs_period_us

# 将进程加入 Cgroup
echo $$ | sudo tee /sys/fs/cgroup/memory/mygroup/tasks
echo $$ | sudo tee /sys/fs/cgroup/cpu/mygroup/tasks

# Cgroup v2 操作
sudo mkdir /sys/fs/cgroup/mygroup
# 启用控制器
echo "+memory +cpu" | sudo tee /sys/fs/cgroup/cgroup.subtree_control
# 设置限制
echo 100M | sudo tee /sys/fs/cgroup/mygroup/memory.max
echo "50000 100000" | sudo tee /sys/fs/cgroup/mygroup/cpu.max
```

### 4.4 Cgroup 资源限制架构

```
┌────────────────────────────────────────────────────────────┐
│                      Cgroup Hierarchy                       │
├────────────────────────────────────────────────────────────┤
│  ┌─────────────────────────────────────────────────────┐   │
│  │  Root Cgroup                                        │   │
│  │  ├─ System.slice (系统服务)                          │   │
│  │  │   ├─ sshd.service                               │   │
│  │  │   └─ cron.service                               │   │
│  │  └─ User.slice (用户会话)                            │   │
│  │      └─ docker-xxx.scope                           │   │
│  │          ├─ Container A (memory: 512MB, cpu: 0.5)  │   │
│  │          ├─ Container B (memory: 1GB, cpu: 1.0)    │   │
│  │          └─ Container C (memory: 256MB, cpu: 0.25) │   │
│  └─────────────────────────────────────────────────────┘   │
└────────────────────────────────────────────────────────────┘
```

## 五、Docker 架构详解

### 5.1 Docker 组件架构

```
┌─────────────────────────────────────────────────────────────┐
│                        Docker Client                         │
│                    (docker CLI命令)                          │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼ REST API
┌─────────────────────────────────────────────────────────────┐
│                      Docker Daemon (dockerd)                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │  Image Mgmt │  │ Container   │  │    Network/Volume   │  │
│  │  镜像管理    │  │ Runtime     │  │    网络卷管理        │  │
│  └─────────────┘  └─────────────┘  └─────────────────────┘  │
└─────────────────────────────────────────────────────────────┘
                              │
            ┌─────────────────┼─────────────────┐
            ▼                 ▼                 ▼
┌──────────────────┐ ┌───────────────┐ ┌──────────────────┐
│   containerd     │ │   runc        │ │   Docker Registry │
│  (容器生命周期)   │ │ (OCI运行时)   │ │    (镜像仓库)     │
│                  │ │               │ │                  │
│  ┌─────────────┐ │ │ 创建容器      │ │ Docker Hub       │
│  │ containerd- │ │ │ 执行进程      │ │ 私有Registry     │
│  │ shim        │ │ │ Namespace隔离 │ │ Harbor           │
│  └─────────────┘ │ │ Cgroup限制    │ │                  │
└──────────────────┘ └───────────────┘ └──────────────────┘
```

### 5.2 Docker 镜像分层结构

```
┌─────────────────────────────────────────────────────────────┐
│  容器读写层 (Container Layer) - 可写，容器删除后消失          │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  新增/修改的文件                                        │  │
│  │  - /app/config.json                                    │  │
│  │  - /var/log/app.log                                    │  │
│  └───────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────┤
│  镜像层 5: Application Layer (FROM node:16-alpine)          │
│  ┌───────────────────────────────────────────────────────┐  │
│  │  COPY package*.json ./                                 │  │
│  │  RUN npm ci --only=production                          │  │
│  └───────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────┤
│  镜像层 4: Build Dependencies                                │
├─────────────────────────────────────────────────────────────┤
│  镜像层 3: Base Runtime (nodejs)                             │
├─────────────────────────────────────────────────────────────┤
│  镜像层 2: Alpine Linux Base                                 │
├─────────────────────────────────────────────────────────────┤
│  镜像层 1: Scratch (空镜像)                                  │
└─────────────────────────────────────────────────────────────┘
```

### 5.3 联合文件系统（UnionFS）

```bash
# 查看镜像分层信息
docker history nginx:latest

# 输出示例：
# IMAGE          CREATED        CREATED BY                                      SIZE
# 605c77e624dd   2 months ago   /bin/sh -c #(nop)  CMD ["nginx" "-g" "daemon…   0B
# <missing>      2 months ago   /bin/sh -c #(nop)  STOPSIGNAL SIGQUIT          0B
# <missing>      2 months ago   /bin/sh -c #(nop)  EXPOSE 80                   0B
# <missing>      2 months ago   /bin/sh -c #(nop)  ENTRYPOINT ["/docker-entr…   0B
# <missing>      2 months ago   /bin/sh -c #(nop) COPY file:xxx in /            4kB
# <missing>      2 months ago   /bin/sh -c #(nop) COPY dir:xxx in /etc/nginx…   6kB
# <missing>      2 months ago   /bin/sh -c set -x     && addgroup --system -…   54MB
```

## 六、Docker 核心命令

### 6.1 镜像操作

```bash
# 镜像搜索与下载
docker search nginx
docker pull nginx:alpine
docker pull registry.cn-hangzhou.aliyuncs.com/nginx/nginx:latest

# 镜像管理
docker images
docker rmi nginx:alpine
docker tag nginx:alpine myregistry/nginx:v1.0
docker push myregistry/nginx:v1.0

# 镜像导出导入
docker save -o nginx.tar nginx:alpine
docker load -i nginx.tar

# 查看镜像详情
docker inspect nginx:alpine
docker history nginx:alpine
```

### 6.2 容器生命周期管理

```bash
# 运行容器
docker run -d \
  --name my-nginx \
  -p 80:80 \
  -v /host/data:/usr/share/nginx/html:ro \
  --restart unless-stopped \
  --memory 512m \
  --cpus 1.0 \
  nginx:alpine

# 容器管理
docker ps -a
docker start my-nginx
docker stop my-nginx
docker restart my-nginx
docker rm my-nginx

# 进入容器
docker exec -it my-nginx /bin/sh
docker attach my-nginx

# 查看容器资源使用
docker stats my-nginx
docker top my-nginx
```

### 6.3 网络管理

```bash
# 查看网络
docker network ls

# 创建自定义网络
docker network create --driver bridge my-bridge

# 容器间通信
docker run -d --name db --network my-bridge mysql:8.0
docker run -d --name app --network my-bridge myapp
# app 容器可通过 http://db:3306 访问数据库

# 端口映射
docker run -d -p 8080:80 -p 8443:443 nginx:alpine
```

## 七、Dockerfile 最佳实践

### 7.1 多阶段构建

```dockerfile
# 构建阶段
FROM node:18-alpine AS builder
WORKDIR /app
COPY package*.json ./
RUN npm ci
COPY . .
RUN npm run build

# 生产阶段
FROM nginx:alpine
COPY --from=builder /app/dist /usr/share/nginx/html
COPY nginx.conf /etc/nginx/conf.d/default.conf
EXPOSE 80
CMD ["nginx", "-g", "daemon off;"]
```

### 7.2 优化 Dockerfile

```dockerfile
# 不好的实践
FROM ubuntu:latest
RUN apt-get update
RUN apt-get install -y curl
RUN apt-get install -y nginx
RUN apt-get install -y nodejs
COPY . /app
RUN npm install

# 好的实践
FROM node:18-alpine
# 合并 RUN 指令减少层数
RUN apk add --no-cache curl nginx && \
    rm -rf /var/cache/apk/*
# 利用缓存：先复制依赖文件
WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production
# 再复制源码（源码变化频繁）
COPY src/ ./src/
# 非 root 用户运行
USER node
EXPOSE 3000
HEALTHCHECK --interval=30s --timeout=3s \
  CMD curl -f http://localhost:3000/health || exit 1
CMD ["node", "src/index.js"]
```

### 7.3 安全加固 Dockerfile

```dockerfile
FROM python:3.11-slim-bookworm AS builder

# 安装依赖到虚拟环境
RUN python -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# 生产镜像 - 使用 distroless
FROM gcr.io/distroless/python3-debian12
COPY --from=builder /opt/venv /opt/venv
COPY app.py /app/
ENV PYTHONPATH=/opt/venv/lib/python3.11/site-packages
WORKDIR /app
# distroless 镜像没有 shell，默认非 root
CMD ["app.py"]
```

## 八、Docker 安全实践

### 8.1 容器安全基线

```bash
# 以非 root 用户运行
docker run -d --user 1000:1000 nginx:alpine

# 限制容器能力（Capability）
docker run -d \
  --cap-drop=ALL \
  --cap-add=NET_BIND_SERVICE \
  nginx:alpine

# 只读文件系统
docker run -d --read-only \
  --tmpfs /tmp \
  --tmpfs /var/run \
  nginx:alpine

# 资源限制
docker run -d \
  --memory 512m \
  --memory-swap 512m \
  --cpus 1.0 \
  --pids-limit 100 \
  nginx:alpine
```

### 8.2 安全扫描

```bash
# 使用 Trivy 扫描镜像
trivy image nginx:alpine

# 使用 Docker Scout
docker scout cves nginx:alpine

# 使用 Clair
docker run -p 6060:6060 \
  -v /var/run/docker.sock:/var/run/docker.sock \
  quay.io/coreos/clair:latest
```

## 九、总结

Docker 通过 Namespace 实现资源隔离，Cgroup 实现资源限制，联合文件系统实现高效的镜像分层存储。理解这些底层原理，有助于我们更好地设计容器化应用，优化镜像大小，保障容器安全。

在生产环境中，建议：

1. 使用多阶段构建减小镜像体积
2. 以非 root 用户运行容器
3. 限制容器资源和权限
4. 定期扫描镜像漏洞
5. 使用官方或可信的基础镜像


---

## 相关主题

- [Docker容器技术](../cloud-computing/Docker容器技术.md)
- [Containerd详解](./Containerd详解.md)
- [OCI规范详解](./OCI规范详解.md)

## 参考资源

- [Docker文档](https://docs.docker.com/engine/)
- [容器技术深入](https://containerd.io/)
