# BitTorrent协议 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

BitTorrent是一种点对点（P2P）文件共享协议，通过将文件分割成多个piece并在对等节点间分发，实现高效的文件传输，解决了传统C/S架构的单点瓶颈和带宽压力问题。

---

## 一、核心概念

### 1.1 定义与原理

**定义**：BitTorrent是一种基于P2P网络的文件分发协议，由Bram Cohen于2001年设计，通过分片下载、多点传输和最优节点选择，实现大规模文件的高效分发。

**核心原理**：

- **文件分片**：大文件分割为固定大小的piece
- **多点下载**：从多个peer同时下载不同piece
- **tit-for-tat**：互惠互利的带宽交换策略
- **稀有优先**：优先下载网络中稀少的piece

### 1.2 关键特性

| 特性 | 描述 |
|------|------|
| **去中心化** | 无中心服务器，所有节点地位平等 |
| **可扩展性** | 下载人数越多，整体下载速度越快 |
| **断点续传** | 支持中断后继续下载 |
| **完整性校验** | 每个piece通过SHA1校验 |
| **动态带宽** | 自适应网络带宽变化 |

### 1.3 网络组件

```
┌─────────────────────────────────────────────────────────────┐
│                     BitTorrent网络                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│    ┌─────────────┐         ┌─────────────┐                 │
│    │   Tracker   │←───────→│    DHT      │                 │
│    │  (集中式)   │         │  (分布式)   │                 │
│    └──────┬──────┘         └──────┬──────┘                 │
│           │                       │                        │
│           └───────────┬───────────┘                        │
│                       │                                    │
│         ┌─────────────┼─────────────┐                      │
│         │             │             │                      │
│    ┌────┴────┐   ┌────┴────┐   ┌────┴────┐                │
│    │  Peer 1 │←─→│  Peer 2 │←─→│  Peer 3 │                │
│    │ (Seed)  │   │(Leecher)│   │(Leecher)│                │
│    └────┬────┘   └────┬────┘   └────┬────┘                │
│         │             │             │                      │
│         └─────────────┴─────────────┘                      │
│                   P2P网络                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、.torrent文件结构

### 2.1 文件格式

**.torrent文件是Bencode编码的字典**：

```
.torrent文件
├── announce: Tracker URL
├── announce-list: Tracker列表（可选）
├── creation date: 创建时间戳
├── comment: 注释（可选）
├── created by: 创建程序
├── info: 文件信息字典
│   ├── name: 文件名/目录名
│   ├── piece length: 每个piece的大小（字节）
│   ├── pieces: 所有piece的SHA1哈希拼接
│   ├── length: 文件大小（单文件）
│   └── files: 文件列表（多文件）
│       ├── length: 文件大小
│       └── path: 文件路径列表
└── url-list: Web种子URL（可选）
```

### 2.2 Bencode编码

**数据类型编码规则**：

| 类型 | 格式 | 示例 |
|------|------|------|
| 字符串 | `<长度>:<内容>` | `5:hello` → "hello" |
| 整数 | `i<数字>e` | `i42e` → 42 |
| 列表 | `l<内容>e` | `li1ei2ei3ee` → [1, 2, 3] |
| 字典 | `d<键值对>e` | `d3:fooi42ee` → {"foo": 42} |

**编码示例**：

```python
# Python字符串
{
    "announce": "http://tracker.example.com/announce",
    "info": {
        "name": "example.txt",
        "piece length": 262144,
        "length": 12345
    }
}

# Bencode编码
d8:announce36:http://tracker.example.com/announce4:infod6:lengthi12345e4:name11:example.txt12:piece lengthi262144eee
```

### 2.3 Piece与Hash

**Piece结构**：

```
┌─────────────────────────────────────────────────┐
│                 文件分割示意                     │
├─────────────────────────────────────────────────┤
│                                                 │
│  ┌────────┬────────┬────────┬────────┬────────┐ │
│  │Piece 0 │Piece 1 │Piece 2 │  ...   │Piece N│ │
│  │256KB   │256KB   │256KB   │        │<256KB │ │
│  └────────┴────────┴────────┴────────┴────────┘ │
│                                                 │
│  每个Piece的SHA1哈希：20字节                      │
│  pieces字段 = hash0 + hash1 + ... + hashN        │
│                                                 │
└─────────────────────────────────────────────────┘
```

**常见Piece大小**：

| 文件大小 | 推荐Piece大小 |
|---------|--------------|
| < 100MB | 256KB |
| 100MB - 1GB | 1MB |
| 1GB - 5GB | 2MB |
| > 5GB | 4MB |

### 2.4 Magnet链接

**格式**：

```
magnet:?xt=urn:btih:<info-hash>&dn=<display-name>&tr=<tracker-url>

示例：
magnet:?xt=urn:btih:08ada5a7a6183aae1e09d831df6748d566095a10
      &dn=Sintel
      &tr=http://tracker.example.com/announce
```

**参数说明**：

| 参数 | 说明 |
|------|------|
| xt | Exact Topic，包含info-hash |
| dn | Display Name，显示名称 |
| tr | Tracker URL |
| ws | Web Seed URL |
| kt | Keyword Topic，搜索关键词 |

---

## 三、Tracker与DHT

### 3.1 Tracker协议

**基于HTTP/UDP的Peer发现**：

```
HTTP Tracker请求：
GET /announce?
    info_hash=<20字节info哈希>
    &peer_id=<20字节peer标识>
    &port=<监听端口>
    &uploaded=<已上传字节>
    &downloaded=<已下载字节>
    &left=<剩余字节>
    &event=<started|completed|stopped>

Tracker响应（Bencode编码）：
{
    "interval": 1800,        // 下次请求间隔
    "peers": [              // Peer列表
        {"ip": "1.2.3.4", "port": 6881},
        {"ip": "5.6.7.8", "port": 6882}
    ],
    "complete": 10,         // 完整种子数
    "incomplete": 20        // 下载中peer数
}
```

**UDP Tracker协议（更高效）**：

```
连接请求 → 连接响应 →  announce请求 → announce响应
  (8字节)    (16字节)     (98字节)       (可变)
```

### 3.2 DHT（分布式哈希表）

**Kademlia DHT协议**：

```
┌─────────────────────────────────────────────────────────────┐
│                     DHT网络结构                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Node ID: 160位（与info-hash相同空间）                       │
│                                                             │
│  距离计算: XOR(node_id1, node_id2)                          │
│                                                             │
│  路由表: 160个bucket，每个bucket最多k个节点（k=8）           │
│                                                             │
│     Bucket 0: 距离 [2^0, 2^1) 的节点                         │
│     Bucket 1: 距离 [2^1, 2^2) 的节点                         │
│     ...                                                     │
│     Bucket 159: 距离 [2^159, 2^160) 的节点                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**DHT消息类型**：

| 消息 | 说明 |
|------|------|
| ping | 探测节点是否在线 |
| find_node | 查找距离目标ID最近的k个节点 |
| get_peers | 查找拥有特定torrent的peer |
| announce_peer | 宣布自己拥有特定torrent |

**Peer发现流程**：

```
┌──────────┐         ┌──────────┐         ┌──────────┐
│  新节点   │         │  DHT节点  │         │ 目标Peer │
└────┬─────┘         └────┬─────┘         └────┬─────┘
     │                    │                    │
     │──get_peers(info_hash)─────────────────→│
     │                    │                    │
     │←────token + 最近的k个节点────────────────│
     │                    │                    │
     │                    │                    │
     │──find_node迭代查询─→│                    │
     │                    │                    │
     │←────────返回更接近的节点─────────────────│
     │                    │                    │
     │                    │                    │
     │──announce_peer────→│                    │
     │   (提供token证明)   │                    │
     │                    │                    │
```

### 3.3 PEX（Peer Exchange）

**PEX协议**：已连接的peer之间交换已知peer列表

```
Libtorrent PEX消息：
{
    "added": <新发现的peer列表>,
    "added.f": <对应的flags>,
    "dropped": <不再可用的peer列表>
}

Flags:
- 0x01: 偏好加密
- 0x02: 做种者
- 0x04: 支持UTP
```

---

## 四、阻塞算法（Choking）

### 4.1 阻塞策略原理

**目标**：

1. 防止免费 riders（只下载不上传）
2. 优化网络带宽利用
3. 保证公平性和效率

**基本规则**：

```
┌─────────────────────────────────────────────────────────────┐
│                      阻塞状态                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  choked（被阻塞）   → 对方不会向我们发送数据                 │
│  unchoked（未阻塞） → 对方允许向我们发送数据                 │
│                                                             │
│  interested（感兴趣）   → 我们有对方拥有的piece              │
│  not interested（不感兴趣） → 我们不需要对方的piece          │
│                                                             │
│  有效连接 = unchoked + interested                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 Tit-for-Tat算法

**核心原则**：优先向给自己提供最快下载速度的peer上传

```
算法流程：
1. 每10秒计算一次各peer的上传速度
2. 选择最快的4个peer进行unchoking
3. 其余peer被choked
4. 每30秒随机unchoked一个peer（乐观非阻塞）
```

```
┌─────────────────────────────────────────────────────────────┐
│                   阻塞决策示例                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Peer    下载速度    状态          我们的决策                │
│  ─────────────────────────────────────────                  │
│  A       50 KB/s    unchoked     保持unchoked              │
│  B       30 KB/s    unchoked     保持unchoked              │
│  C       20 KB/s    unchoked     保持unchoked              │
│  D       10 KB/s    unchoked     → choked (第5名)          │
│  E       5 KB/s     choked       保持choked                │
│  F       0 KB/s     choked       乐观unchoked（随机）       │
│                                                             │
│  最大上传槽位: 4 (默认)                                      │
│  乐观非阻塞槽位: 1                                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 4.3 反吸血机制

**识别和惩罚免费riders**：

| 检测方法 | 说明 |
|---------|------|
| 上传/下载比例 | 比例过低则choked |
| 连接时长 | 长时间无数据传输则断开 |
| 虚假进度报告 | 检测并ban报告虚假piece的peer |
| 多个连接 | 同一IP多个连接可能为攻击 |

**Bitfield监控**：

```
定期检查peer报告的bitfield：
- 声称拥有但实际请求不到的piece → 虚假报告
- 进度异常快速增长 → 可能作弊
- 总是请求但从不提供 → 免费rider
```

---

## 五、Piece选择与下载

### 5.1 选择策略

**四种基本策略**：

```
1. 严格优先级（Strict Priority）
   └── 优先选择同piece的sub-piece完成整个piece

2. 稀有优先（Rarest First）
   └── 优先下载全网最稀少的piece

3. 随机选择（Random First）
   └── 开始时随机选择piece（获取piece多样性）

4. 顺序选择（Sequential）
   └── 按顺序下载（用于流媒体播放）
```

### 5.2 稀有优先算法

**算法实现**：

```python
def select_piece_to_download(peer_list, have_bitfields):
    # 统计每个piece的拥有者数量
    piece_rarity = {}
    for bitfield in have_bitfields:
        for i, has in enumerate(bitfield):
            if has:
                piece_rarity[i] = piece_rarity.get(i, 0) + 1

    # 选择我们需要的、最稀有的piece
    needed_pieces = get_needed_pieces()
    rarest_needed = sorted(
        needed_pieces,
        key=lambda p: piece_rarity.get(p, float('inf'))
    )

    return rarest_needed[0]
```

**为什么稀有优先？**：

- **提高可用性**：稀少的piece被更多peer拥有
- **减少单点依赖**：避免最后几个piece只有少数peer拥有
- **优化上传机会**：拥有稀有piece更容易获得上传机会

### 5.3 下载流水线

**Pipeline机制**：

```
传统方式：            Pipeline方式：
Request → Wait      Request1 → Request2 → Request3
  ↓                    ↓          ↓          ↓
Receive              Receive1   Receive2   Receive3
  ↓                    ↓          ↓          ↓
Request → Wait      Process1   Process2   Process3

流水线深度：通常5个请求
```

**请求队列管理**：

```
每个peer维护：
- pending_requests: 已发送但未收到的请求队列
- max_pending: 最大并发请求数（通常5）

当收到piece时：
1. 从pending_requests移除
2. 发送新的请求补充队列
3. 保持pipeline充满
```

### 5.4 Endgame模式

**触发条件**：几乎所有piece都已下载完成

**优化策略**：

```
正常模式：            Endgame模式：
每个piece只向         向所有peer请求
一个peer请求          所有缺失的piece
                         ↓
                   第一个响应被接受
                   其余请求取消
```

**为什么需要Endgame？**：

- 最后几个piece可能只有少数peer拥有
- 这些peer可能被choked或速度慢
- 多路请求提高获取概率
- 收到后取消多余请求避免浪费

---

## 六、扩展协议

### 6.1 快速扩展（Fast Extension）

**允许peer快速建议piece**：

```
消息类型：
- 0x06: Have All - 拥有所有piece
- 0x07: Have None - 没有piece
- 0x08: Suggest Piece - 建议下载某piece
- 0x09: Allowed Fast - 允许快速下载
- 0x0d: Reject Request - 拒绝请求
```

**Allowed Fast机制**：

- 新peer可以立即下载特定piece（无需tit-for-tat）
- 帮助新peer快速获得第一个piece
- 默认允许下载：piece索引 = (fast_set + r) % num_pieces

### 6.2 加密传输

**协议加密（PE/Message Stream Encryption）**：

```
握手过程：
1. 发送加密握手（DH密钥交换）
2. 验证支持加密
3. 使用RC4加密后续通信
4. 可选：伪装为HTTP流量

加密级别：
- 0: 禁用加密
- 1: 优先尝试加密，失败则明文
- 2: 强制加密，不允许明文
```

### 6.3 µTP（Micro Transport Protocol）

**基于UDP的拥塞控制协议**：

```
优势：
- 更好的拥塞控制（LEDBAT算法）
- 低延迟，不影响其他网络应用
- 穿透NAT更容易

LEDBAT算法：
- 目标是利用剩余带宽
- 当检测到其他流量时主动退让
- 通过测量延迟判断网络拥塞
```

---

## 七、性能优化

### 7.1 连接管理

**连接数优化**：

| 参数 | 默认值 | 说明 |
|------|--------|------|
| max_connections | 200 | 最大连接数 |
| max_uploads | 4 | 最大上传数 |
| min_connections | 40 | 最小连接数 |
| connection_limit | 每torrent 80 | 单torrent连接限制 |

**连接生命周期**：

```
建立连接 → 握手 → 交换bitfield → 传输数据 → 关闭
    │        │         │            │        │
    │        │         │            │        └── 完成或超时
    │        │         │            └── 阻塞/请求/传输
    │        │         └── 了解对方拥有piece
    │        └── 协议验证
    └── TCP连接建立
```

### 7.2 磁盘I/O优化

**缓存策略**：

```
写入缓存：
- 按piece组织写入缓冲区
- piece完整后一次性写入磁盘
- 减少磁盘随机写

读取缓存：
- 预读相邻piece
- LRU缓存策略
- 优先缓存稀有piece
```

**稀疏文件支持**：

```
Linux: fallocate(FALLOC_FL_KEEP_SIZE)
Windows: SetFileValidData

效果：
- 预分配文件空间
- 避免文件系统碎片
- 提高写入性能
```

### 7.3 带宽管理

**全局限速**：

```
upload_limit = 总上传带宽 × 0.8
download_limit = 总下载带宽 × 0.9

为其他应用保留带宽，避免网络拥塞
```

**智能限速算法**：

```
自动调整上传限速：
- 监控下载速度
- 如果下载慢，增加上传限速
- 如果下载快，适当降低上传限速
- 平衡上传下载，最大化整体效率
```

---

## 八、与其他主题的关联

### 8.1 上游依赖

- [点对点网络](../../03-network/p2p-networks.md)
- [分布式哈希表](../dht.md)
- [网络传输协议](../../03-network/transport-protocols.md)

### 8.2 下游应用

- [IPFS星际文件系统](./IPFS星际文件系统.md)
- [P2P流媒体](../p2p-streaming.md)
- [去中心化存储](../decentralized-storage.md)

### 8.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| eDonkey/eMule | 对比 | 另一种P2P文件共享协议 |
| WebTorrent | 扩展 | 浏览器中的BitTorrent实现 |
| Tribler | 扩展 | 去中心化的匿名BitTorrent |

---

## 九、参考资源

### 9.1 官方规范

1. [BitTorrent Protocol Specification](http://www.bittorrent.org/beps/bep_0003.html) - BEP 3
2. [BitTorrent Enhancement Proposals](http://www.bittorrent.org/beps/bep_0000.html) - 所有BEP文档
3. [DHT Protocol](http://www.bittorrent.org/beps/bep_0005.html) - BEP 5

### 9.2 开源项目

1. [libtorrent](https://github.com/arvidn/libtorrent) - C++ BitTorrent库
2. [Transmission](https://github.com/transmission/transmission) - 轻量级客户端
3. [qBittorrent](https://github.com/qbittorrent/qBittorrent) - 开源客户端
4. [WebTorrent](https://github.com/webtorrent/webtorrent) - JavaScript实现

### 9.3 学习资料

1. [BitTorrent Specification](https://wiki.theory.org/BitTorrentSpecification) - Theory.org
2. [Incentives Build Robustness in BitTorrent](http://www.bittorrent.org/bittorrentecon.pdf) - Bram Cohen
3. [Kademlia论文](https://pdos.csail.mit.edu/~petar/papers/maymounkov-kademlia-lncs.pdf) - Kademlia原始论文

### 9.4 相关文档

- [区块链基础](./区块链基础.md)
- [区块链共识机制](./区块链共识机制.md)
- [IPFS星际文件系统](./IPFS星际文件系统.md)

---

**维护者**：项目团队
**最后更新**：2026年
