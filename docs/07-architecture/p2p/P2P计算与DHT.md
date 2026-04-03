# P2P计算与分布式哈希表（DHT）

**文档版本**：v1.0
**创建时间**：2026年4月
**状态**：✅ 初稿完成

---

## 📋 执行摘要

点对点（Peer-to-Peer, P2P）计算是一种去中心化的分布式计算范式，网络中的每个节点（Peer）既是客户端也是服务器。P2P系统具有天然的容错性、可扩展性和自组织能力，广泛应用于文件共享、区块链、内容分发网络等领域。

**分布式哈希表（DHT）** 是P2P系统的核心技术，提供分布式键值存储和高效查找机制，支持在O(log N)时间内定位数据。

---

## 一、核心概念

### 1.1 P2P架构类型

| 类型 | 结构 | 优点 | 缺点 | 代表系统 |
|------|------|------|------|---------|
| **非结构化** | 随机连接 | 容错性强，易加入 | 查找效率低 | Gnutella, BitTorrent |
| **结构化** | DHT组织 | 确定性查找 O(log N) | 维护成本高 | Chord, Kademlia |
| **混合式** | 超级节点 | 平衡性能与容错 | 超级节点单点 | Skype, BitTorrent |

### 1.2 P2P核心特性

- **去中心化**：无单点故障，无单点瓶颈
- **自组织**：节点自动发现和维护网络
- **可扩展性**：节点增加时性能平滑下降
- **匿名性**：通信不经过中心服务器
- **容错性**：节点故障不影响整体服务

### 1.3 适用场景

| 场景 | 适用性 | 代表应用 |
|------|--------|---------|
| 文件共享 | ⭐⭐⭐⭐⭐ | BitTorrent, IPFS |
| 内容分发 | ⭐⭐⭐⭐⭐ | CDN, 视频流媒体 |
| 区块链 | ⭐⭐⭐⭐⭐ | Bitcoin, Ethereum |
| 即时通讯 | ⭐⭐⭐⭐ | Skype, 微信早期 |
| 分布式计算 | ⭐⭐⭐⭐ | SETI@home, Folding@home |
|  DNS替代 | ⭐⭐⭐ | Namecoin |

---

## 二、分布式哈希表（DHT）

### 2.1 DHT基本原理

**目标**：在分布式环境中实现类似哈希表的接口

```
PUT(key, value) → 存储到负责该key的节点
GET(key) → 从负责该key的节点获取value
```

**核心问题**：

1. 如何确定哪个节点负责哪个key？
2. 节点加入/离开时如何重新分配数据？
3. 如何保证查找效率？

### 2.2 标识符空间

**一致性哈希环**：

```
    0 ←────────────────────→ 2^m-1
    │                        │
    │    N20    N50         │
    ◄────●───────●──────────►
    │              N80       │
    │               ●        │
    └────────────────────────┘

    Key分配规则：key分配给顺时针方向最近的节点
    key=30 → N50
    key=70 → N80
    key=90 → N20（环绕）
```

### 2.3 Chord协议

#### 路由表（Finger Table）

```
节点n的Finger Table：
┌─────────┬─────────────────────────────┐
│  i      │  successor(n + 2^(i-1))      │
├─────────┼─────────────────────────────┤
│  1      │  successor(n + 1)            │
│  2      │  successor(n + 2)            │
│  3      │  successor(n + 4)            │
│  ...    │  ...                         │
│  m      │  successor(n + 2^(m-1))      │
└─────────┴─────────────────────────────┘

m = 标识符位数（通常160位）
每个节点维护O(log N)个条目
```

#### 查找算法

```python
def find_successor(id):
    """查找负责id的后继节点"""
    if id in (n, successor]:
        return successor
    # 在Finger Table中找到最接近但不超过id的节点
    n_prime = closest_preceding_node(id)
    return n_prime.find_successor(id)

def closest_preceding_node(id):
    """在Finger Table中从后向前查找"""
    for i in range(m, 0, -1):
        if finger[i] in (n, id):
            return finger[i]
    return n
```

**查找复杂度**：O(log N)跳

**示例（N=1000节点）**：

```
查找key=1234（从节点1000开始）：
1. 节点1000的Finger指向1280, 1536, 2048...
2. 跳到1280
3. 节点1280的Finger指向1408, 1664...
4. 跳到1408
5. 节点1408的后继是1450
6. 1450负责1234？否，继续...
7. 平均约10跳可找到
```

#### 节点加入

```
1. 新节点n通过引导节点连接到网络
2. 初始化Finger Table（通过查找 successor(n + 2^i)）
3. 更新其他节点的Finger Table
4. 从后继节点接管部分key
5. 开始周期性稳定化协议
```

#### 稳定化协议

```python
def stabilize():
    """周期性执行，维护后继指针"""
    x = successor.predecessor
    if x in (n, successor):
        successor = x
    successor.notify(n)

def notify(n_prime):
    """n_prime认为它可能是当前节点的后继"""
    if predecessor is None or n_prime in (predecessor, n):
        predecessor = n_prime
```

### 2.4 Kademlia协议

#### XOR度量距离

```
distance(x, y) = x XOR y

特性：
1. 对称性：d(x,y) = d(y,x)
2. 非负性：d(x,y) ≥ 0
3. 三角不等式：d(x,z) ≤ d(x,y) + d(y,z)
```

#### K桶（K-Bucket）

```
节点ID：160位

K桶结构（按距离分层）：
┌────────┬────────────────────────────┐
│  K桶    │  距离范围                   │
├────────┼────────────────────────────┤
│  0      │  [2^0, 2^1)  = [1, 2)      │
│  1      │  [2^1, 2^2)  = [2, 4)      │
│  2      │  [2^2, 2^3)  = [4, 8)      │
│  ...    │  ...                        │
│  i      │  [2^i, 2^(i+1))             │
│  ...    │  ...                        │
│  159    │  [2^159, 2^160)             │
└────────┴────────────────────────────┘

每个K桶最多存储K个节点（通常K=20）
```

#### 查找算法

```python
def lookup(key):
    """并行查找最接近key的k个节点"""
    # 1. 从本地K桶选择α个最接近的节点
    candidates = select_alpha_closest(key)

    # 2. 并行向这些节点发送FIND_NODE请求
    results = parallel_query(candidates, key)

    # 3. 从结果中选择新的候选节点
    while not done:
        closer_nodes = [n for n in results if n not in queried]
        if not closer_nodes:
            break
        # 继续查询更接近的节点
        results.extend(parallel_query(closer_nodes[:α], key))

    # 4. 返回k个最接近的节点
    return k_closest(results, key)
```

**参数**：

- **α（并发度）**：并行查询数（通常3）
- **k（桶大小）**：每个桶节点数（通常20）

**查找复杂度**：O(log N)，平均查询次数 ≈ log₂N

### 2.5 Chord vs Kademlia

| 特性 | Chord | Kademlia |
|------|-------|----------|
| **路由表大小** | O(log N) | O(log N) |
| **查找跳数** | O(log N) | O(log N) |
| **并行查找** | 否 | 是（α并发） |
| **距离度量** | 环上距离 | XOR距离 |
| **节点信息** | Finger Table | K桶 |
| **刷新机制** | 稳定化协议 | LRU替换 |
| **实际应用** | 学术研究 | BitTorrent DHT, Ethereum |

---

## 三、P2P应用系统

### 3.1 BitTorrent协议

#### 核心组件

**Tracker**：

- 协调文件分发
- 维护Peer列表
- 可选（可使用DHT替代）

**.torrent文件**：

```
{
  "announce": "http://tracker.example.com:8080/announce",
  "info": {
    "name": "example_file.zip",
    "piece length": 262144,  // 256KB每块
    "pieces": "<20字节SHA1哈希列表>",
    "files": [...]
  }
}
```

**P2P网络**：

- 将文件分割为固定大小的piece（通常256KB-4MB）
- 每个peer维护bitmap表示拥有哪些piece
- 使用"最稀有优先"（Rarest First）策略选择下载piece

#### 阻塞算法（Choking Algorithm）

**目标**：优化整体下载速度，防止"搭便车"

```
每个Peer同时最多上传给4个Peer（非阻塞）

阻塞策略：
1. 每10秒：根据上传速率排序，解除上传最快的4个Peer的阻塞
2. 每30秒：随机解除一个Peer的阻塞（乐观非阻塞）
   - 给新Peer上传机会
   - 发现更好的上传源

下载策略：
- 优先从非阻塞自己的Peer下载
- 使用"最稀有优先"选择piece
```

### 3.2 IPFS（InterPlanetary File System）

#### 核心概念

**内容寻址**：

```
传统HTTP：位置寻址 → http://server.com/path/file
IPFS：内容寻址 → ipfs://<文件内容的哈希>

优势：
- 内容验证（哈希匹配）
- 去重（相同内容相同哈希）
- 缓存友好
```

**Merkle DAG**：

```
文件 → 分割为blocks → 构建Merkle树 → Root Hash标识整个文件

      Root Hash
      /       \
   Hash1     Hash2
   /   \     /   \
 B1   B2   B3   B4

任何块的修改都会改变Root Hash
```

#### IPFS组件

| 组件 | 功能 |
|------|------|
| **Bitswap** | 块交换协议，请求/提供数据块 |
| **DHT（Kademlia）** | 发现Peer和存储提供者 |
| **PubSub** | 发布订阅消息传递 |
| **IPNS** | 可变命名系统（将公钥映射到哈希） |
| **Libp2p** | 网络传输层（支持多种协议） |

### 3.3 区块链中的P2P

#### Bitcoin网络

**网络类型**：非结构化P2P + 泛洪传播

```
节点类型：
- 全节点：验证所有交易和区块
- SPV节点（轻节点）：只下载区块头
- 矿工节点：挖矿 + 全节点功能

消息传播：
1. 节点A发现新交易
2. 向8个连接节点广播INV消息
3. 邻居节点请求交易数据（GETDATA）
4. 节点A发送交易（TX）
5. 邻居继续向它们的邻居传播
```

#### Ethereum的Kademlia DHT

```
用途：
- 节点发现（Node Discovery）
- 存储和发现ENR（Ethereum Node Records）

ENR包含：
- 节点ID
- IP地址和端口
- 支持的协议版本
- 签名
```

---

## 四、系统对比

### 4.1 DHT实现对比

| 实现 | 协议 | 应用 | 特点 |
|------|------|------|------|
| **Chord** | Chord | 学术研究 | 简单，理论清晰 |
| **Mainline DHT** | Kademlia | BitTorrent | 最大规模DHT（千万级节点） |
| **Coral CDN** | Kademlia | CDN | 考虑网络拓扑的近邻优先 |
| **Kad** | Kademlia | eMule | 早期文件共享 |
| **S/Kademlia** | Kademlia | 安全增强 | 防护Sybil攻击 |

### 4.2 P2P系统对比

| 系统 | 类型 | 主要用途 | 节点规模 |
|------|------|---------|---------|
| **BitTorrent** | 混合P2P | 文件共享 | 千万级 |
| **IPFS** | 结构化P2P | 分布式存储 | 百万级 |
| **Bitcoin** | 非结构化 | 加密货币 | 万级（全节点） |
| **Ethereum** | Kademlia | 智能合约平台 | 万级（全节点） |
| **Skype** | 混合P2P | 即时通讯 | 亿级（历史上） |

---

## 五、实践指南

### 5.1 DHT节点选择

| 场景 | 推荐协议 | 理由 |
|------|---------|------|
| 文件共享 | Kademlia | 成熟，并行查找 |
| 内容分发 | Chord/Kademlia | 确定性路由 |
| 节点发现 | Kademlia | 高效，容错 |
| 学术研究 | Chord | 简单，易于分析 |

### 5.2 攻击与防护

| 攻击类型 | 描述 | 防护措施 |
|---------|------|---------|
| **Sybil攻击** | 单一实体创建大量恶意节点 | 身份验证，PoW/PoS |
| **Eclipse攻击** | 隔离目标节点的网络视图 | 随机连接，认证 |
| **路由污染** | 返回错误的路由信息 | 冗余查询，信任机制 |
| **拒绝服务** | 淹没网络流量 | 速率限制，资源控制 |

### 5.3 性能优化

**1. 邻近性感知**：

```
优先选择网络延迟低的节点
- 测量RTT
- 基于AS号/地理位置
- Coral DHT的clustering
```

**2. 缓存策略**：

```
- 热门数据本地缓存
- 路由表缓存
- 结果缓存
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [一致性哈希](../负载均衡/一致性哈希.md)
- [分布式存储](../storage/分布式存储基础.md)
- [网络协议](../../03-communication/网络协议基础.md)

### 6.2 下游应用

- [区块链与共识](../../04-consensus/blockchain/区块链基础.md)
- [分布式文件系统](../../05-storage/dfs/IPFS.md)
- [内容分发网络](../../07-architecture/cdn/CDN架构.md)

---

## 七、参考资源

### 7.1 学术论文

1. [Chord: A Scalable Peer-to-peer Lookup Service for Internet Applications](https://pdos.csail.mit.edu/papers/chord:sigcomm01/chord_sigcomm01.pdf) - Stoica et al., SIGCOMM 2001
2. [Kademlia: A Peer-to-Peer Information System Based on the XOR Metric](https://pdos.csail.mit.edu/~petar/papers/maymounkov-kademlia-lncs.pdf) - Maymounkov & Mazieres, 2002
3. [BitTorrent Protocol Specification](http://www.bittorrent.org/beps/bep_0003.html)

### 7.2 开源项目

1. [libp2p](https://libp2p.io/) - 模块化P2P网络栈
2. [IPFS](https://ipfs.io/) - 星际文件系统
3. [go-ethereum](https://github.com/ethereum/go-ethereum) - Ethereum实现

---

**维护者**：项目团队
**最后更新**：2026年4月
