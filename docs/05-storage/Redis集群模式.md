# Redis集群模式专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

Redis作为高性能键值存储，提供了多种部署模式以满足不同规模的需求：主从复制提供读写分离和高可用；Sentinel实现自动故障转移；Cluster提供数据分片和水平扩展。理解各模式的架构原理、适用场景和配置方法，是构建可靠缓存层的基础。

---

## 一、核心概念

### 1.1 Redis部署模式概览

```
┌─────────────────────────────────────────────────────────────┐
│                    Redis部署模式演进                         │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  单机模式 (Standalone)                                      │
│  ┌─────────────────┐                                       │
│  │   Redis Node    │  简单，无高可用                        │
│  │  (全量数据)      │  适用于开发测试                        │
│  └─────────────────┘                                       │
│                                                            │
│  主从复制 (Replication)                                     │
│  ┌─────────┐         ┌─────────┐                           │
│  │ Master  │←────────│  Slave  │  读写分离，数据冗余          │
│  │ (写+R)  │  同步    │  (只读)  │  手动故障转移               │
│  └─────────┘         └─────────┘                           │
│       ↑                                                    │
│  ┌─────────┐                                               │
│  │  Slave  │  一主多从，扩展读性能                         │
│  └─────────┘                                               │
│                                                            │
│  Sentinel模式（哨兵）                                       │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                     │
│  │Sentinel1│  │Sentinel2│  │Sentinel3│  监控+自动故障转移   │
│  │(监控节点)│  │(监控节点)│  │(监控节点)│                     │
│  └────┬────┘  └────┬────┘  └────┬────┘                     │
│       └─────────────┼─────────────┘                        │
│                     ↓                                      │
│              ┌─────────┐                                   │
│              │ Master  │                                   │
│              └────┬────┘                                   │
│         ┌────────┼────────┐                                │
│    ┌────┴────┐  ┌┴───────┐┐                                │
│    │ Slave1  │  │ Slave2  │                                │
│    └─────────┘  └─────────┘                                │
│                                                            │
│  Cluster模式（集群）                                        │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                 │
│  │ MasterA │────│ MasterB │────│ MasterC │  数据分片        │
│  │ (0-5460)│    │(5461-10922)  │(10923-16383)               │
│  └────┬────┘    └────┬────┘    └────┬────┘                 │
│       │              │              │                       │
│  ┌────┴────┐    ┌────┴────┐    ┌────┴────┐                 │
│  │ SlaveA1 │    │ SlaveB1 │    │ SlaveC1 │  副本冗余        │
│  └─────────┘    └─────────┘    └─────────┘                 │
│                                                            │
│  Gossip协议互联，无中心节点，去中心化设计                      │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 模式对比

| 模式 | 数据容量 | 高可用 | 自动故障转移 | 数据分片 | 适用场景 |
|------|----------|--------|--------------|----------|----------|
| **Standalone** | 单机内存 | ✗ | ✗ | ✗ | 开发测试 |
| **Replication** | 单机内存 | △ | ✗ | ✗ | 读多写少 |
| **Sentinel** | 单机内存 | ✓ | ✓ | ✗ | 中小规模 |
| **Cluster** | 线性扩展 | ✓ | ✓ | ✓ | 大规模生产 |

---

## 二、技术细节

### 2.1 主从复制原理

```
┌─────────────────────────────────────────────────────────────┐
│                    主从复制机制                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  复制流程：                                                  │
│                                                            │
│  ┌─────────────┐                      ┌─────────────┐       │
│  │    Slave    │                      │    Master   │       │
│  │             │  1. PSYNC ?          │             │       │
│  │             │ ────────────────────→│             │       │
│  │             │                      │             │       │
│  │             │  2. +FULLRESYNC      │             │       │
│  │             │ ←────────────────────│             │       │
│  │             │     runid offset     │             │       │
│  │             │                      │             │       │
│  │             │  3. 接收RDB文件       │             │       │
│  │             │ ←────────────────────│ bgsave RDB  │       │
│  │             │                      │             │       │
│  │             │  4. 加载RDB          │             │       │
│  │             │  ==================→ │             │       │
│  │             │                      │             │       │
│  │             │  5. 接收增量命令      │             │       │
│  │             │ ←────────────────────│  replication│       │
│  │             │      AOF/缓冲区       │   backlog   │       │
│  │             │                      │             │       │
│  └─────────────┘                      └─────────────┘       │
│                                                            │
│  复制偏移量机制：                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Master维护: master_repl_offset                         │ │
│  │ Slave维护:  slave_repl_offset                          │ │
│  │                                                       │ │
│  │ 当slave_repl_offset < master_repl_offset:             │ │
│  │   - 差值在backlog范围内: 部分重同步(PSYNC)            │ │
│  │   - 差值超出backlog: 全量重同步(FULLRESYNC)           │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  复制缓冲区(replication backlog):                          │
│  - 固定大小环形缓冲区(默认1MB)                              │
│  - 存储最近传播的写命令                                     │
│  - 用于网络中断后的增量同步                                 │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

#### 复制配置

```bash
# master节点配置 (redis.conf)
# 基本无需特殊配置，默认开启复制

# slave节点配置
replicaof 192.168.1.100 6379    # 指定主节点
masterauth <password>           # 主节点密码
replica-read-only yes           # 从节点只读

# 复制缓冲区配置
repl-backlog-size 64mb          # 增大可减少全量同步
repl-backlog-ttl 3600           # 断开后保留时间

# 复制策略
repl-diskless-sync yes          # 无磁盘复制(实验性)
repl-ping-replica-period 10     # 心跳检测间隔
repl-timeout 60                 # 复制超时时间
```

### 2.2 Sentinel高可用架构

```
┌─────────────────────────────────────────────────────────────┐
│                  Sentinel 故障转移流程                       │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  正常状态：                                                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                     │
│  │   S1    │  │   S2    │  │   S3    │  Sentinel集群       │
│  │ (leader)│  │         │  │         │  通过Raft选举leader │
│  └────┬────┘  └────┬────┘  └────┬────┘                     │
│       └─────────────┼─────────────┘                        │
│                     ↓ 监控 (PING every 1s)                 │
│              ┌─────────────┐                               │
│              │    Master   │                               │
│              │  [健康: ✅]  │                               │
│              └──────┬──────┘                               │
│         ┌───────────┼───────────┐                          │
│    ┌────┴────┐ ┌────┴────┐ ┌────┴────┐                     │
│    │ Replica1│ │ Replica2│ │ Replica3│                     │
│    └─────────┘ └─────────┘ └─────────┘                     │
│                                                            │
│  ─────────────────────────────────────────────────────    │
│                                                            │
│  故障检测：                                                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                     │
│  │   S1    │  │   S2    │  │   S3    │                     │
│  │         │  │         │  │         │                     │
│  └────┬────┘  └────┬────┘  └────┬────┘                     │
│       │           │           │                            │
│       └───────────┼───────────┘                            │
│                   ↓ PING超时                                │
│            ┌─────────────┐                                 │
│            │    Master   │                                 │
│            │ [SDOWN: ⚠️]  │ 主观下线                        │
│            │ [ODOWN: ❌]  │ 客观下线(多数Sentinel确认)       │
│            └─────────────┘                                 │
│                                                            │
│  ─────────────────────────────────────────────────────    │
│                                                            │
│  故障转移：                                                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                     │
│  │   S1    │  │   S2    │  │   S3    │                     │
│  │ [leader]│  │         │  │         │  1. 选举Leader      │
│  └────┬────┘  └────┬────┘  └────┬────┘                     │
│       │            │            │                          │
│       │ 2. 选主(优先级+偏移量+RunID)                         │
│       │            │            │                          │
│       └─────────────┴─────────────┘                        │
│                     ↓                                      │
│              ┌─────────────┐  旧Master                     │
│              │   [故障]    │  待恢复后作为Replica加入        │
│              └─────────────┘                               │
│                     ↑                                      │
│         ┌───────────┼───────────┐                          │
│    ┌────┴────┐ ┌────┴────┐ ┌────┴────┐                     │
│    │ Replica1│ │Replica2 │ │Replica3 │                     │
│    │         │ │[New    │ │         │                     │
│    │         │ │ Master] │ │         │                     │
│    └─────────┘ └────┬────┘ └─────────┘                     │
│                     │                                      │
│              3. SLAVEOF NO ONE                             │
│              4. 其他Replica指向新Master                      │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

#### Sentinel配置

```bash
# sentinel.conf
port 26379
dir /tmp

# 监控主节点
# sentinel monitor <master-name> <ip> <port> <quorum>
sentinel monitor mymaster 192.168.1.100 6379 2

# 认证信息
sentinel auth-pass mymaster <password>

# 主观下线时间 (毫秒)
sentinel down-after-milliseconds mymaster 5000

# 并行同步数
sentinel parallel-syncs mymaster 1

# 故障转移超时
sentinel failover-timeout mymaster 180000

# 通知脚本
sentinel notification-script mymaster /path/to/notify.sh
sentinel client-reconfig-script mymaster /path/to/reconfig.sh
```

### 2.3 Cluster分片架构

```
┌─────────────────────────────────────────────────────────────┐
│                  Redis Cluster 架构详解                      │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  数据分片（16384个槽位）：                                   │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Slot 0-5460  │ Slot 5461-10922 │ Slot 10923-16383   │ │
│  │   MasterA     │     MasterB     │      MasterC        │ │
│  │   负责        │     负责        │      负责           │ │
│  └───────┬───────┴────────┬────────┴──────────┬──────────┘ │
│          │                │                   │            │
│    ┌─────┴─────┐    ┌─────┴─────┐      ┌─────┴─────┐      │
│    │  ReplicaA │    │  ReplicaB │      │  ReplicaC │      │
│    │ (从A)     │    │ (从B)     │      │ (从C)     │      │
│    └───────────┘    └───────────┘      └───────────┘      │
│                                                            │
│  键到槽的映射：                                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ HASH_SLOT = CRC16(key) mod 16384                      │ │
│  │                                                       │ │
│  │ 示例:                                                 │ │
│  │   key = "user:1001"                                   │ │
│  │   CRC16("user:1001") = 12345                          │ │
│  │   12345 mod 16384 = 12345 → 由MasterB负责              │ │
│  │                                                       │ │
│  │ Hash Tag: 确保相关key在同一槽                           │ │
│  │   key = "{user}:1001" 和 "{user}:profile"              │ │
│  │   只对{}内计算CRC16，确保同一槽                          │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  Gossip协议通信：                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ 每个节点维护集群状态（节点ID、槽分配、主从关系）           │ │
│  │                                                       │ │
│  │ 消息类型:                                             │ │
│  │ ├─ PING: 携带自身状态和部分其他节点状态                 │ │
│  │ ├─ PONG: 回复PING，同样携带状态                        │ │
│  │ └─ MEET: 新节点加入集群                                │ │
│  │                                                       │ │
│  │ 故障检测:                                             │ │
│  │ ├─ PFAIL (Possible Fail): 单节点标记疑似故障            │ │
│  │ └─ FAIL: 多数节点确认后广播                            │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  MOVED重定向：                                               │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Client → 任意Node: GET foo                            │ │
│  │                                                       │ │
│  │ 如果foo在目标节点: 直接返回                            │ │
│  │ 如果foo在其他节点: 返回MOVED slot target-node:port     │ │
│  │                                                       │ │
│  │ Client需要缓存槽到节点的映射，更新后重试                │ │
│  │                                                       │ │
│  │ ASK重定向: 迁移过程中使用                              │ │
│  │ Client收到ASK后，向目标节点发送ASKING命令再执行请求      │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

#### Cluster配置

```bash
# redis-cluster.conf
port 6379
cluster-enabled yes
cluster-config-file nodes-6379.conf
cluster-node-timeout 5000
cluster-require-full-coverage no
cluster-migration-barrier 1

# 持久化配置
appendonly yes
appendfsync everysec

# 内存配置
maxmemory 4gb
maxmemory-policy allkeys-lru

# 创建集群命令
# redis-cli --cluster create \
#   192.168.1.101:6379 192.168.1.102:6379 192.168.1.103:6379 \
#   192.168.1.104:6379 192.168.1.105:6379 192.168.1.106:6379 \
#   --cluster-replicas 1
```

---

## 三、系统对比

### 3.1 模式选型对比

| 维度 | 主从复制 | Sentinel | Cluster |
|------|----------|----------|---------|
| **节点数** | 2+ | 2+ Redis + 3+ Sentinel | 6+ (3主3从) |
| **数据容量** | 单机 | 单机 | 线性扩展 |
| **写入QPS** | 单机 | 单机 | 分片累加 |
| **读取QPS** | N × 单机 | N × 单机 | N × 单机 |
| **故障转移** | 手动 | 自动 | 自动 |
| **客户端复杂度** | 低 | 中 | 高(需处理MOVED) |
| **跨槽事务** | 支持 | 支持 | 不支持 |
| **多键操作** | 支持 | 支持 | 同槽限制 |

### 3.2 性能基准

```
┌─────────────────────────────────────────────────────────────┐
│                    Redis性能基准 (8核32GB)                   │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  单机性能：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ 操作类型        │ QPS          │ 延迟(p99)            │ │
│  ├─────────────────┼──────────────┼──────────────────────┤ │
│  │ GET (简单值)    │ 100,000+     │ 0.5ms               │ │
│  │ SET (简单值)    │ 80,000+      │ 0.6ms               │ │
│  │ GET (1KB值)     │ 60,000+      │ 1.0ms               │ │
│  │ Pipeline (批量) │ 500,000+     │ 5ms/1000命令        │ │
│  │ Lua脚本         │ 50,000+      │ 1.5ms               │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  Cluster扩展性：                                             │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ 节点配置        │ 理论容量      │ 实测写入QPS        │ │
│  ├─────────────────┼──────────────┼──────────────────────┤ │
│  │ 3主3从          │ 3×单节点      │ 200,000+            │ │
│  │ 6主6从          │ 6×单节点      │ 400,000+            │ │
│  │ 12主12从        │ 12×单节点     │ 800,000+            │ │
│  └───────────────────────────────────────────────────────┘ │
│  注: 受网络延迟和客户端处理能力影响，实际性能会有所下降        │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、实践指南

### 4.1 生产环境配置

#### 内核优化

```bash
# /etc/sysctl.conf
# 内存分配策略
vm.overcommit_memory = 1

# 透明大页禁用
echo never > /sys/kernel/mm/transparent_hugepage/enabled

# TCP连接优化
net.core.somaxconn = 511
net.ipv4.tcp_max_syn_backlog = 511

# 文件描述符
ulimit -n 65535
```

#### Redis参数优化

```bash
# redis.conf 生产配置

# 内存配置
maxmemory 8gb
maxmemory-policy allkeys-lru
maxmemory-samples 5

# 持久化优化
save 900 1
save 300 10
save 60 10000
stop-writes-on-bgsave-error yes
rdbcompression yes
rdbchecksum yes

appendonly yes
appendfsync everysec
no-appendfsync-on-rewrite yes
auto-aof-rewrite-percentage 100
auto-aof-rewrite-min-size 64mb

# 慢查询监控
slowlog-log-slower-than 10000
slowlog-max-len 128

# 客户端连接
timeout 300
tcp-keepalive 60
maxclients 10000
```

### 4.2 客户端连接模式

```java
// Jedis Cluster客户端
@Configuration
public class RedisClusterConfig {

    @Bean
    public JedisCluster jedisCluster() {
        Set<HostAndPort> nodes = new HashSet<>();
        nodes.add(new HostAndPort("192.168.1.101", 6379));
        nodes.add(new HostAndPort("192.168.1.102", 6379));
        nodes.add(new HostAndPort("192.168.1.103", 6379));

        JedisPoolConfig poolConfig = new JedisPoolConfig();
        poolConfig.setMaxTotal(100);
        poolConfig.setMaxIdle(50);
        poolConfig.setMinIdle(10);

        return new JedisCluster(nodes, 2000, 2000, 3,
            "password", poolConfig);
    }
}

// Lettuce连接池（推荐，支持响应式）
@Bean
public RedisConnectionFactory lettuceConnectionFactory() {
    RedisClusterConfiguration clusterConfig =
        new RedisClusterConfiguration(Arrays.asList(
            "192.168.1.101:6379",
            "192.168.1.102:6379",
            "192.168.1.103:6379"
        ));
    clusterConfig.setPassword(RedisPassword.of("password"));

    ClientOptions options = ClientOptions.builder()
        .socketOptions(SocketOptions.builder()
            .connectTimeout(Duration.ofMillis(100))
            .build())
        .timeoutOptions(TimeoutOptions.builder()
            .timeoutCommands(true)
            .build())
        .build();

    LettuceClientConfiguration clientConfig =
        LettuceClientConfiguration.builder()
            .clientOptions(options)
            .readFrom(ReadFrom.REPLICA_PREFERRED)
            .build();

    return new LettuceConnectionFactory(clusterConfig, clientConfig);
}
```

### 4.3 常见问题

**Q1: Cluster模式下为什么不能跨槽事务？**
A: Redis Cluster将数据分布在多个节点，每个槽位对应一个节点。跨槽事务需要分布式事务协调，Redis Cluster设计目标为高性能，不支持两阶段提交等复杂协议。

**Q2: 如何选择主从复制还是Cluster？**
A: 数据量 < 单节点内存、QPS < 10万：主从+Sentinel；数据量 > 单节点内存或需要水平扩展：Cluster。

**Q3: 脑裂问题如何避免？**
A: 配置`min-slaves-to-write 1`和`min-slaves-max-lag 10`，确保主节点至少有1个从节点连接且延迟<10秒才接受写入。

**Q4: 大Key问题如何处理？**
A: 1) 业务拆分，将大Hash拆分为多个小Hash；2) 使用unlink代替del异步删除；3) 监控并告警bigkey；4) 考虑使用其他存储（如HBase）。

---

## 五、与其他主题的关联

### 5.1 上游依赖

- [缓存设计模式](./缓存设计模式.md)
- [主从复制原理](./主从复制原理.md)

### 5.2 下游应用

- [缓存一致性](./缓存一致性.md)
- [缓存穿透与雪崩](./缓存穿透与雪崩.md)

---

## 六、参考资源

### 6.1 官方文档

1. [Redis Replication](https://redis.io/docs/management/replication/)
2. [Redis Sentinel](https://redis.io/docs/management/sentinel/)
3. [Redis Cluster](https://redis.io/docs/management/scaling/)

### 6.2 相关文档

- [缓存设计模式](./缓存设计模式.md)
- [缓存一致性](./缓存一致性.md)

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
