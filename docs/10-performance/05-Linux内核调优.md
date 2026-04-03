# Linux内核调优：网络与文件系统

## 核心概念

### 1. Linux网络栈架构

Linux网络栈是高性能服务器的核心，理解其架构有助于针对性优化。

**网络数据包处理流程**：

```
┌─────────────────────────────────────────────────────────────┐
│                      网络栈处理流程                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   应用层    [Socket API]  send()/recv()                     │
│      ↓                                                      │
│   TCP/UDP   [传输层]    分段/重组、拥塞控制、流量控制        │
│      ↓                                                      │
│    IP层     [网络层]    路由选择、分片/重组                   │
│      ↓                                                      │
│   网络设备   [数据链路层]  qdisc排队、驱动处理                 │
│      ↓                                                      │
│   网卡硬件   [物理层]    DMA、中断、Ring Buffer              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**关键性能瓶颈点**：

```
1. 中断处理：单核处理网络中断成为瓶颈
2. 内存拷贝：数据在用户态和内核态之间多次拷贝
3. 上下文切换：系统调用和进程调度开销
4. 锁竞争：多核访问共享数据结构的锁开销
5. 缓存失效：CPU缓存未命中
```

### 2. 网络性能参数

**核心内核参数分类**：

```
┌─────────────────────────────────────────────────────────────┐
│                   网络调优参数分类                          │
├──────────────┬──────────────────────────────────────────────┤
│   连接管理    │  SYN队列、Accept队列、连接重用、TIME_WAIT    │
├──────────────┼──────────────────────────────────────────────┤
│   缓冲区      │  Socket发送/接收缓冲区、TCP窗口大小          │
├──────────────┼──────────────────────────────────────────────┤
│   拥塞控制    │  算法选择、初始窗口、拥塞窗口调整            │
├──────────────┼──────────────────────────────────────────────┤
│   中断处理    │  NAPI、软中断分发、多队列网卡                │
├──────────────┼──────────────────────────────────────────────┤
│   内核优化    │  端口范围、文件描述符、反向路径过滤          │
└──────────────┴──────────────────────────────────────────────┘
```

### 3. 文件系统性能

**Linux文件系统层次**：

```
应用层
   ↓ (系统调用)
VFS (Virtual File System)
   ↓
具体文件系统 (ext4/xfs/btrfs)
   ↓
Page Cache
   ↓
块设备层 (Block I/O Layer)
   ↓
设备驱动
   ↓
存储硬件
```

**Page Cache机制**：

```
读路径：
应用读请求 → 检查Page Cache → 命中则返回
                              → 未命中则从磁盘读取并缓存

写路径：
应用写请求 → 写入Page Cache → 标记dirty
                              → 后台flush线程定期刷盘
```

## 实践方法

### 网络内核参数调优

**1. TCP连接优化**：

```bash
# /etc/sysctl.conf

# ===== SYN队列优化 =====
# SYN队列长度，增大可应对SYN Flood
net.ipv4.tcp_max_syn_backlog = 65536

# 每个端口监听队列长度
net.core.somaxconn = 65535
net.core.netdev_max_backlog = 65536

# ===== TIME_WAIT优化 =====
# 重用TIME_WAIT端口（仅客户端安全）
net.ipv4.tcp_tw_reuse = 1

# 快速回收TIME_WAIT（NAT环境慎用）
net.ipv4.tcp_tw_recycle = 0

# TIME_WAIT保持时间（秒）
net.ipv4.tcp_fin_timeout = 30

# 最大TIME_WAIT套接字数量
net.ipv4.tcp_max_tw_buckets = 50000

# ===== 连接保活 =====
# TCP保活探测间隔
net.ipv4.tcp_keepalive_time = 300
net.ipv4.tcp_keepalive_probes = 5
net.ipv4.tcp_keepalive_intvl = 15
```

**2. 缓冲区优化**：

```bash
# ===== Socket缓冲区 =====
# 全局最大缓冲区
net.core.rmem_max = 134217728  # 128MB
net.core.wmem_max = 134217728

# 全局默认缓冲区
net.core.rmem_default = 16777216  # 16MB
net.core.wmem_default = 16777216

# TCP缓冲区自动调节
net.ipv4.tcp_rmem = 4096 87380 134217728  # min default max
net.ipv4.tcp_wmem = 4096 65536 134217728

# TCP内存限制
net.ipv4.tcp_mem = 134217728 201326592 268435456  # 低 压 高

# 启用窗口缩放（支持大窗口）
net.ipv4.tcp_window_scaling = 1
```

**3. 拥塞控制算法**：

```bash
# 查看可用算法
cat /sys/class/net/eth0/available_congestion_control
cubic reno bbr

# 设置BBR算法（高吞吐、低延迟）
net.ipv4.tcp_congestion_control = bbr
net.core.default_qdisc = fq

# BBR参数微调
echo 1 > /sys/module/tcp_bbr/parameters/pacing_gain
```

**4. 内核网络优化脚本**：

```bash
#!/bin/bash
# network_tune.sh - 高性能服务器网络调优

apply_sysctl() {
    echo "Applying network optimizations..."

    # 文件描述符限制
    ulimit -n 1048576

    # 端口范围
    sysctl -w net.ipv4.ip_local_port_range="1024 65535"

    # 禁用反向路径过滤（多网卡环境）
    sysctl -w net.ipv4.conf.all.rp_filter=0
    sysctl -w net.ipv4.conf.default.rp_filter=0

    # 禁用ICMP重定向
    sysctl -w net.ipv4.conf.all.accept_redirects=0
    sysctl -w net.ipv4.conf.all.send_redirects=0

    # 启用MTU探测（防止分片）
    sysctl -w net.ipv4.tcp_mtu_probing=1

    # 延迟ACK（吞吐vs延迟权衡）
    sysctl -w net.ipv4.tcp_no_delay=0  # Nagle算法启用
    sysctl -w net.ipv4.tcp_quickack=0

    # TCP Fast Open
    sysctl -w net.ipv4.tcp_fastopen=3

    echo "Network optimizations applied successfully"
}

# 验证配置
verify_settings() {
    echo "=== Current Settings ==="
    sysctl net.core.somaxconn
    sysctl net.ipv4.tcp_max_syn_backlog
    sysctl net.ipv4.tcp_congestion_control
    sysctl net.core.rmem_max
}

apply_sysctl
verify_settings
```

### 多队列网卡与中断优化

**网卡多队列配置**：

```bash
# 查看网卡队列数
ethtool -l eth0

# 设置网卡队列数
ethtool -L eth0 combined 8

# 查看中断分布
cat /proc/interrupts | grep eth0

# 绑定中断到指定CPU
# /etc/default/irqbalance 禁用自动均衡
systemctl stop irqbalance

# 手动绑定（示例：4个队列绑定到CPU 0-3）
echo 1 > /proc/irq/101/smp_affinity  # CPU0
echo 2 > /proc/irq/102/smp_affinity  # CPU1
echo 4 > /proc/irq/103/smp_affinity  # CPU2
echo 8 > /proc/irq/104/smp_affinity  # CPU3
```

**RPS/RFS配置**（接收包转向）：

```bash
# RPS - 将软中断分发到多核
# 配置所有网卡队列使用所有CPU
echo ffffffff > /sys/class/net/eth0/queues/rx-0/rps_cpus

# RFS - 将同一flow的包发送到同一CPU
sysctl -w net.core.rps_sock_flow_entries=32768

# 每个队列的flow表大小
for f in /sys/class/net/eth0/queues/rx-*/rps_flow_cnt; do
    echo 4096 > $f
done
```

### 文件系统调优

**1. ext4文件系统优化**：

```bash
# 挂载参数优化
mount -t ext4 -o noatime,nodiratime,nobarrier,data=writeback /dev/sda1 /data

# 参数说明：
# noatime      - 不更新访问时间，减少IO
# nodiratime   - 不更新目录访问时间
# nobarrier    - 禁用写屏障（配合BBU/SSD使用）
# data=writeback - 异步日志模式（性能最高，安全性较低）

# /etc/fstab 配置示例
UUID=xxx /data ext4 noatime,nodiratime,nobarrier,data=writeback,errors=remount-ro 0 1
```

**2. XFS文件系统优化**：

```bash
# XFS挂载优化
mount -t xfs -o noatime,nodiratime,nobarrier,largeio,inode64 /dev/sdb1 /data

# 参数说明：
# largeio      - 优化大文件顺序IO
# inode64      - 允许inode号超过2^32
# allocsize=1g - 预分配大小（大文件写入优化）
```

**3. I/O调度器选择**：

```bash
# 查看当前调度器
cat /sys/block/sda/queue/scheduler
# [mq-deadline] kyber bfq none

# SSD选择none/mq-deadline
echo none > /sys/block/nvme0n1/queue/scheduler

# HDD选择mq-deadline/bfq
echo mq-deadline > /sys/block/sda/queue/scheduler

# 预读优化（SSD可以调低）
blockdev --setra 256 /dev/sda  # 128KB预读
```

**4. Page Cache调优**：

```bash
# /etc/sysctl.conf

# 脏页比例阈值
vm.dirty_ratio = 40              # 脏页占内存40%开始刷盘
vm.dirty_background_ratio = 10   # 后台刷盘阈值10%

# 脏页时间阈值
vm.dirty_expire_centisecs = 3000  # 脏页30秒必须刷盘
vm.dirty_writeback_centisecs = 100  # 刷盘线程100ms检查一次

# 内存回收倾向
vm.swappiness = 10  # 倾向于保留文件缓存，少用swap

# 大页配置（数据库等）
vm.nr_hugepages = 1024
```

## 工具使用

### 网络性能监控工具

**1. ss命令（替代netstat）**：

```bash
# 查看连接状态统计
ss -s

# 查看TIME_WAIT连接
ss -tan state time-wait | wc -l
ss -tan state time-wait | head

# 查看ESTABLISHED连接并排序
ss -tan state established | awk '{print $4}' | cut -d: -f2 | sort | uniq -c | sort -rn

# 查看socket内存使用
ss -m

# 查看TCP内部信息
ss -tin
```

**2. 性能基准测试**：

```bash
# iperf3 - 网络吞吐测试
# 服务端
iperf3 -s -p 5201

# 客户端
iperf3 -c server_ip -p 5201 -t 30 -P 10 -w 1M
# -t 30: 测试30秒
# -P 10: 10个并发流
# -w 1M: 窗口大小1MB

# netperf - 延迟测试
netperf -H server_ip -t TCP_RR -- -r 64,64

# sockperf - TCP/UDP延迟测试
sockperf tp -i server_ip -p 11111 -t 30 --mps=max
```

**3. 内核网络监控**：

```bash
# nstat - 网络统计
nstat -az

# 查看TCP重传率
nstat | grep -E "TcpRetransSegs|TcpOutSegs"

# 查看丢包统计
cat /proc/net/snmp | grep -E "Tcp|Ip"

# 网卡统计
ethtool -S eth0
```

### 文件系统性能工具

**1. IO基准测试**：

```bash
# fio - 灵活的IO测试
# 随机读测试
fio --name=randread --ioengine=libaio --iodepth=32 \
    --rw=randread --bs=4k --direct=1 --size=10G \
    --numjobs=4 --runtime=60 --group_reporting

# 顺序写测试
fio --name=seqwrite --ioengine=libaio --iodepth=16 \
    --rw=write --bs=1M --direct=1 --size=10G \
    --numjobs=1 --runtime=60

# 混合读写测试
fio --name=mix --ioengine=libaio --iodepth=64 \
    --rw=randrw --rwmixread=70 --bs=4k --direct=1 \
    --size=10G --numjobs=8 --runtime=120
```

**2. IO监控工具**：

```bash
# iostat - 磁盘IO统计
iostat -xdm 1

# 输出说明：
# r/s, w/s    - 每秒读写请求数
# rkB/s, wkB/s - 每秒读写KB数
# await        - 平均IO等待时间(ms)
# %util        - 设备利用率

# iotop - 进程级IO监控
iotop -oP  # 只显示有IO的进程

# pidstat - 详细IO统计
pidstat -d 1 -p <pid>

# biosnoop (BCC) - 跟踪每个IO
biosnoop-bpfcc
```

## 案例数据

### 高并发服务器调优案例

**场景：API网关服务器（10万并发连接）**

**优化前配置**：

```
连接数限制：
- 文件描述符：65535
- 端口范围：32768-61000
- somaxconn：128
- max_syn_backlog：1024

网络性能：
- 吞吐：2Gbps
- P99延迟：50ms
- TIME_WAIT：50000+
```

**调优措施**：

```bash
# 1. 连接数扩容
ulimit -n 1048576
sysctl -w net.ipv4.ip_local_port_range="1024 65535"
sysctl -w net.core.somaxconn=65535
sysctl -w net.ipv4.tcp_max_syn_backlog=65536

# 2. TIME_WAIT优化
sysctl -w net.ipv4.tcp_tw_reuse=1
sysctl -w net.ipv4.tcp_fin_timeout=10
sysctl -w net.ipv4.tcp_max_tw_buckets=2000000

# 3. 缓冲区扩容
sysctl -w net.core.rmem_max=134217728
sysctl -w net.core.wmem_max=134217728
sysctl -w net.ipv4.tcp_rmem="4096 87380 134217728"
sysctl -w net.ipv4.tcp_wmem="4096 65536 134217728"

# 4. 网卡优化
ethtool -L eth0 combined 8
ethtool -G eth0 rx 4096 tx 4096

# 5. 中断优化
echo ffffffff > /sys/class/net/eth0/queues/rx-0/rps_cpus
```

**优化后效果**：

```
连接能力：
- 最大并发连接：50万
- 新建连接率：10万/秒
- TIME_WAIT：可控范围内

网络性能：
- 吞吐：9.5Gbps
- P99延迟：15ms
- CPU使用率：下降30%
```

### 数据库服务器文件系统调优

**场景：MySQL OLTP服务器**

**优化前**：

```
文件系统：ext4默认挂载
IO调度器：mq-deadline
脏页设置：默认值
磁盘类型：NVMe SSD

性能：
- 随机读IOPS：10万
- 随机写IOPS：8万
- 平均延迟：2ms
```

**调优配置**：

```bash
# 1. XFS文件系统优化
mkfs.xfs -d agcount=32 -l size=128m /dev/nvme0n1
mount -t xfs -o noatime,nodiratime,nobarrier,largeio,inode64 /dev/nvme0n1 /data

# 2. IO调度器
echo none > /sys/block/nvme0n1/queue/scheduler
echo 2 > /sys/block/nvme0n1/queue/iosched/fifo_batch

# 3. 预读优化
blockdev --setra 0 /dev/nvme0n1

# 4. Page Cache调优
sysctl -w vm.dirty_ratio=5
sysctl -w vm.dirty_background_ratio=1
sysctl -w vm.dirty_expire_centisecs=6000
sysctl -w vm.swappiness=1
sysctl -w vm.zone_reclaim_mode=0

# 5. 透明大页（数据库建议禁用）
echo never > /sys/kernel/mm/transparent_hugepage/enabled
echo never > /sys/kernel/mm/transparent_hugepage/defrag
```

**优化后**：

```
性能：
- 随机读IOPS：25万（+150%）
- 随机写IOPS：18万（+125%）
- 平均延迟：0.8ms（-60%）
- 长尾延迟：P99 2ms（-50%）
```

## 优化前后对比

| 优化项 | 优化前 | 优化后 | 改进 |
|--------|--------|--------|------|
| 最大连接数 | 6万 | 50万 | 733%↑ |
| 网络吞吐 | 2Gbps | 9.5Gbps | 375%↑ |
| 新建连接率 | 1万/s | 10万/s | 900%↑ |
| 随机读IOPS | 10万 | 25万 | 150%↑ |
| 随机写IOPS | 8万 | 18万 | 125%↑ |
| 磁盘延迟 | 2ms | 0.8ms | 60%↓ |
| 网络P99延迟 | 50ms | 15ms | 70%↓ |

---

**总结**：Linux内核调优是高性能系统的基础。通过合理配置网络参数、中断分发、文件系统挂载选项等，可以显著提升系统的并发处理能力和IO性能。调优需结合实际硬件和业务场景，避免盲目照搬配置。
