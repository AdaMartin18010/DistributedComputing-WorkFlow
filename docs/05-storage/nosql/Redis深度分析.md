# Redis 深度分析

**文档版本**：v1.0
**创建时间**：2026年4月
**状态**：✅ 初稿完成

---

## 📋 执行摘要

Redis（Remote Dictionary Server）是一个开源的内存数据结构存储系统，可用作数据库、缓存、消息代理和流引擎。Redis支持多种数据结构（字符串、哈希、列表、集合、有序集合、位图、HyperLogLog、流、地理空间索引），以其极高的性能（每秒可执行超过10万次读写操作）和丰富的功能而闻名。

**核心特性**：

- 纯内存操作，性能极高
- 丰富的数据类型和操作
- 支持持久化（RDB快照和AOF日志）
- 支持主从复制、哨兵、集群等高可用方案
- 支持事务、Lua脚本、发布订阅

---

## 一、核心概念

### 1.1 定义与原理

Redis是一个**键值存储数据库**，所有数据存储在内存中，通过键（Key）快速访问值（Value）。与传统关系型数据库不同，Redis：

- 不支持SQL查询语言
- 不支持复杂的关系模型
- 专注于高性能、低延迟的数据访问

### 1.2 数据类型

| 数据类型 | 描述 | 适用场景 |
|---------|------|---------|
| **String** | 字符串、整数、浮点数 | 缓存、计数器、分布式锁 |
| **Hash** | 键值对集合 | 对象存储、会话数据 |
| **List** | 双向链表 | 消息队列、时间线 |
| **Set** | 无序唯一集合 | 标签、共同好友 |
| **Sorted Set** | 带权重的有序集合 | 排行榜、延迟队列 |
| **Bitmap** | 位图 | 签到统计、布隆过滤器 |
| **HyperLogLog** | 基数估算 | UV统计（误差0.81%） |
| **Stream** | 日志型数据结构 | 消息流、事件溯源 |
| **Geospatial** | 地理空间索引 | 位置服务、附近的人 |

### 1.3 适用场景

| 场景 | 适用性 | 具体应用 |
|------|--------|---------|
| 缓存 | ⭐⭐⭐⭐⭐ | 页面缓存、对象缓存、会话缓存 |
| 实时计数 | ⭐⭐⭐⭐⭐ | 点赞、阅读数、库存计数 |
| 消息队列 | ⭐⭐⭐⭐ | 轻量级队列、发布订阅 |
| 排行榜 | ⭐⭐⭐⭐⭐ | 游戏排行榜、热门文章 |
| 分布式锁 | ⭐⭐⭐⭐⭐ | RedLock、Redisson |
| 会话存储 | ⭐⭐⭐⭐ | 用户登录状态、购物车 |
| 复杂查询 | ⭐⭐ | 不适合，无二级索引 |
| 持久化存储 | ⭐⭐⭐ | 需要配合RDB/AOF |

---

## 二、技术细节

### 2.1 内存数据结构

#### String（SDS - Simple Dynamic String）

```c
// SDS结构
struct sdshdr {
    int len;        // 字符串长度
    int free;       // 空闲空间
    char buf[];     // 字符数组
};
```

**特性**：

- O(1)获取长度
- 预分配空间，减少内存重分配
- 二进制安全（可存储任意数据）

#### Hash（ziplist / hashtable）

```
小规模（<512个元素，每个<64字节）：
  ziplist（压缩列表）→ 连续内存，节省空间

大规模：
  hashtable（字典）→ O(1)访问
  dict结构：2个哈希表，渐进式rehash
```

#### List（quicklist = ziplist + linked list）

```
quicklist节点：
- 每个节点是一个ziplist（默认8KB）
- 节点间双向链表连接

优势：
- 节省指针开销（ziplist内连续存储）
- 支持快速插入删除（链表特性）
```

#### Sorted Set（skiplist + hashtable）

```
结构：
- skiplist：按score排序，支持范围查询 O(log N)
- hashtable：member → score映射，O(1)查找

跳表示例（最大层数32）：
L3: 1 --------> 10 --------> 20
L2: 1 -> 5 -> 10 -> 15 -> 20
L1: 1 -> 3 -> 5 -> 8 -> 10 -> 12 -> 15 -> 18 -> 20
```

### 2.2 持久化机制

#### RDB（Redis Database）

**触发方式**：

- 手动：`SAVE`（阻塞）或 `BGSAVE`（后台）
- 自动：配置触发条件

```conf
# RDB配置
save 900 1      # 900秒内至少1个key变化
save 300 10     # 300秒内至少10个key变化
save 60 10000   # 60秒内至少10000个key变化

dbfilename dump.rdb
dir /var/lib/redis
```

**实现原理**（BGSAVE）：

```
1. Fork子进程（Copy-on-Write）
2. 子进程遍历内存数据，写入RDB文件
3. 父进程继续处理请求，修改的页复制到新内存
4. 子进程完成，替换旧RDB文件
```

**Copy-on-Write开销**：

- Fork时共享内存页
- 写操作时复制页面（约复制修改数据量的2倍）

#### AOF（Append Only File）

**写入策略**：

```conf
# AOF配置
appendonly yes
appendfilename "appendonly.aof"

# 同步策略
appendfsync always    # 每次写入都同步（最安全，最慢）
appendfsync everysec  # 每秒同步（默认，平衡）
appendfsync no        # 由OS决定（最快，最不安全）
```

**AOF重写（BGREWRITEAOF）**：

```
问题：AOF文件不断增长，包含冗余命令

解决：创建新AOF文件，只保留最终状态的最小命令集

示例：
  原AOF：SET x 1 → INCR x → INCR x（3条命令）
  重写后：SET x 3（1条命令）
```

#### RDB vs AOF 对比

| 特性 | RDB | AOF |
|------|-----|-----|
| **文件大小** | 紧凑（二进制） | 较大（文本命令） |
| **恢复速度** | 快（直接加载） | 慢（重放命令） |
| **数据安全** | 可能丢失最后一次快照 | 最多丢失1秒数据（everysec） |
| **性能影响** | Fork时短暂影响 | 持续fsync开销 |
| **推荐** | 全量备份 | 主从复制时从节点使用 |

**混合持久化（Redis 4.0+）**：

```
AOF文件格式：
[RDB格式快照][AOF增量命令]

优势：
- 恢复时先加载RDB（快），再重放AOF增量（少）
- 兼顾RDB速度和AOF安全性
```

### 2.3 高可用架构

#### 主从复制

```
┌─────────┐         ┌─────────┐         ┌─────────┐
│  Master │◄───────►│ Slave 1 │◄───────►│ Slave 2 │
│ (写+读) │  同步    │  (读)   │  级联   │  (读)   │
└─────────┘         └─────────┘         └─────────┘
```

**复制流程**：

```
1. 从节点发送 SYNC 命令
2. 主节点执行 BGSAVE，生成RDB
3. 主节点发送RDB给从节点
4. 从节点加载RDB
5. 主节点持续发送写命令到从节点（复制积压缓冲区）
```

**部分重同步（Redis 2.8+）**：

```
问题：网络闪断后需要全量同步

解决：
- 主从都维护复制偏移量（offset）
- 主节点维护复制积压缓冲区（默认1MB）
- 断线重连后，如果从节点offset在缓冲区内，只发送缺失部分
```

#### 哨兵模式（Sentinel）

```
        ┌─────────┐
        │ Client  │
        └────┬────┘
             │
    ┌────────┴────────┐
    │   Sentinel x3   │ (监控集群)
    │   (投票选举)     │
    └────────┬────────┘
             │
        ┌────┴────┐
   ┌────┤ Master  ├────┐
   │    └────┬────┘    │
   │    (故障时切换)    │
   │         │         │
┌──┴──┐   ┌─┴───┐   ┌─┴───┐
│Slave│   │Slave│   │Slave│
└─────┘   └─────┘   └─────┘
```

**Sentinel功能**：

- 监控主从节点健康
- 自动故障转移
- 通知客户端拓扑变化
- 配置提供者（客户端询问Sentinel获取当前主节点）

**故障转移流程**：

```
1. Sentinel检测到主节点主观下线（SDOWN）
2. 多个Sentinel达成共识，标记客观下线（ODOWN）
3. 选举Leader Sentinel（Raft算法）
4. Leader从从节点中选出新主节点（优先级、偏移量、ID）
5. 其他从节点重新配置为新主的从节点
6. 通知客户端新主节点地址
```

#### 集群模式（Cluster）

```
哈希槽（Hash Slot）：
- 共16384个槽（0-16383）
- 每个key通过CRC16(key) % 16384 映射到槽
- 每个主节点负责一部分槽

┌──────────┬──────────┬──────────┐
│ Master A │ Master B │ Master C │
│ (0-5460) │(5461-10922)│(10923-16383)│
└─────┬────┴────┬─────┴────┬─────┘
      │         │          │
   ┌──┴──┐   ┌─┴───┐   ┌──┴──┐
   │Slave│   │Slave│   │Slave│
   └──┬──┘   └──┬──┘   └──┬──┘
      └─────────┴─────────┘
         客户端路由
```

**节点通信**：

- 集群总线（Cluster Bus）：Gossip协议
- 每个节点定期向其他节点发送PING/PONG
- 交换槽映射信息和节点状态

**客户端路由**：

```python
# 客户端缓存槽映射
MOVED slot ip:port  # 槽已迁移，客户端更新缓存
ASK slot ip:port    # 槽正在迁移，临时访问
```

---

## 三、系统对比

### 3.1 键值存储对比

| 特性 | Redis | Memcached | etcd | Aerospike |
|------|-------|-----------|------|-----------|
| **数据结构** | 丰富（9种） | 仅String | String | 较丰富 |
| **持久化** | RDB/AOF | 无 | WAL | 有 |
| **集群** | 原生支持 | 客户端分片 | Raft | 原生支持 |
| **性能** | 10万+QPS | 10万+QPS | 较低 | 10万+QPS |
| **内存** | 内存优先 | 纯内存 | 内存 | 混合存储 |
| **适用** | 缓存+存储 | 纯缓存 | 配置中心 | 大数据 |

### 3.2 缓存策略对比

| 策略 | 实现 | 适用场景 |
|------|------|---------|
| **LRU** | 最近最少使用 | 通用场景（默认） |
| **LFU** | 最不经常使用 | 访问频率差异大 |
| **TTL** | 过期时间 | 时间敏感数据 |
| **Random** | 随机淘汰 | 测试场景 |

---

## 四、实践指南

### 4.1 最佳实践

**1. 键命名规范**

```
格式：业务:模块:标识
示例：
- user:profile:1001
- order:detail:20240101:10001
- product:inventory:sku123

避免：
- 过长的键名（占用内存）
- 没有命名空间（难以管理）
```

**2. 大Key治理**

```bash
# 发现大Key
redis-cli --bigkeys
redis-cli --mem-keys "pattern"

# 处理策略：
# 1. Hash分桶：hash:{id} → 多个小hash
# 2. List分片：list:{id}:0, list:{id}:1
# 3. String压缩：压缩后存储
```

**3. 热Key解决**

```
问题：单个Key访问量过高，单节点压力

解决：
1. 本地缓存（Caffeine/Guava）+ Redis
2. Key拆分：key_0, key_1, ..., key_9 随机访问
3. 读写分离：从节点分担读压力
4. 二级缓存（应用级缓存）
```

**4. 管道（Pipeline）使用**

```python
# 批量操作减少RTT
pipe = r.pipeline()
for i in range(1000):
    pipe.set(f"key:{i}", f"value:{i}")
pipe.execute()  # 一次发送所有命令

# vs 非管道：1000次RTT
```

**5. Lua原子操作**

```lua
-- 原子性扣减库存
local stock = redis.call('GET', KEYS[1])
if tonumber(stock) > 0 then
    redis.call('DECR', KEYS[1])
    return 1  -- 成功
else
    return 0  -- 库存不足
end
```

### 4.2 分布式锁

**RedLock算法**：

```
1. 获取当前时间戳T1
2. 依次向N个Redis节点申请锁（SET key value NX PX timeout）
3. 计算获取锁的总耗时T2-T1
4. 如果成功获取多数节点（N/2+1）且耗时<锁超时时间，则获取成功
5. 锁实际持有时间 = 超时时间 - (T2-T1)
6. 解锁时向所有节点发送DEL命令
```

**Redisson实现**：

```java
RLock lock = redisson.getLock("myLock");
try {
    lock.lock();
    // 执行业务逻辑
} finally {
    lock.unlock();
}
```

### 4.3 性能优化

**1. 内存优化**

```conf
# 使用更小的编码
hash-max-ziplist-entries 512
hash-max-ziplist-value 64
list-max-ziplist-size -2
zset-max-ziplist-entries 128
zset-max-ziplist-value 64

# 启用内存淘汰
maxmemory 4gb
maxmemory-policy allkeys-lru
```

**2. 慢查询优化**

```bash
# 配置慢查询日志
slowlog-log-slower-than 10000  # 10ms
slowlog-max-len 128

# 查看慢查询
redis-cli SLOWLOG GET 10
```

---

## 五、与其他主题的关联

### 5.1 上游依赖

- [内存数据结构](../存储引擎/内存数据结构.md)
- [主从复制](../replication/主从复制.md)
- [Raft算法](../../04-consensus/raft-family/Raft算法.md)

### 5.2 下游应用

- [分布式锁](../分布式锁/Redis分布式锁.md)
- [缓存模式](../缓存/缓存模式.md)
- [消息队列](../message-queue/Redis消息队列.md)

---

## 七、参考资源

### 7.1 官方资源

1. [Redis官方文档](https://redis.io/documentation)
2. [Redis命令参考](https://redis.io/commands)
3. [Redis源码](https://github.com/redis/redis)

### 7.2 学习资料

1. [Redis设计与实现](http://redisbook.com/) - 黄健宏
2. [Redis实战](https://redislabs.com/redis-in-action/) -  Josiah Carlson

---

**维护者**：项目团队
**最后更新**：2026年4月


---

## 相关主题

- [Redis集群模式](../Redis集群模式.md)
- [缓存设计模式](../缓存设计模式.md)
- [Caffeine本地缓存](../Caffeine本地缓存.md)

## 参考资源

- [Redis官方文档](https://redis.io/documentation)
- [Redis设计与实现](http://redisbook.com/)
