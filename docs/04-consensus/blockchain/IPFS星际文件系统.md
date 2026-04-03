# IPFS星际文件系统 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

IPFS（InterPlanetary File System，星际文件系统）是一种点对点的分布式文件系统，旨在连接所有计算设备的统一文件系统，通过内容寻址替代传统HTTP的位置寻址，实现更快、更安全、更开放的Web。

---

## 一、核心概念

### 1.1 定义与原理

**定义**：IPFS是由Protocol Labs于2014年发起的分布式文件系统，旨在创建持久且分布式存储和共享文件的网络传输协议，目标是补充甚至取代HTTP。

**核心原理**：

- **内容寻址**：通过文件内容哈希而非位置URL定位资源
- **去重存储**：相同内容只存储一份
- **版本控制**：Merkle DAG支持版本历史和分支
- **P2P传输**：BitSwap协议实现节点间数据交换

### 1.2 IPFS vs HTTP

| 特性 | HTTP | IPFS |
|------|------|------|
| **寻址方式** | 位置寻址（URL） | 内容寻址（CID） |
| **服务器依赖** | 中心化服务器 | 分布式节点 |
| **冗余存储** | 多服务器重复存储 | 全局去重 |
| **离线访问** | 不可行 | 可行（已下载内容） |
| **带宽效率** | 重复下载 | 就近获取 |
| **数据持久性** | 服务器维护 | 网络共同维护 |
| **审查抵抗** | 弱 | 强 |

### 1.3 技术栈概览

```
┌─────────────────────────────────────────────────────────────┐
│                      IPFS技术栈                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      应用层                          │   │
│  │  IPFS CLI / IPFS HTTP API / IPFS PubSub / IPNS      │   │
│  └─────────────────────────────────────────────────────┘   │
│                            │                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      命名层                          │   │
│  │  IPNS (InterPlanetary Naming System)                │   │
│  └─────────────────────────────────────────────────────┘   │
│                            │                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      交换层                          │   │
│  │  BitSwap Protocol                                   │   │
│  └─────────────────────────────────────────────────────┘   │
│                            │                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      路由层                          │   │
│  │  DHT (Kademlia) / MDNS / delegated routing          │   │
│  └─────────────────────────────────────────────────────┘   │
│                            │                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      网络层                          │   │
│  │  libp2p: transport, security, muxing, peer routing  │   │
│  └─────────────────────────────────────────────────────┘   │
│                            │                                │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                      数据层                          │   │
│  │  IPLD (Merkle DAG) / UnixFS / Block Storage         │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、内容寻址（CID）

### 2.1 CID结构

**CID（Content Identifier）是IPFS中用于唯一标识内容的自描述哈希**：

```
CIDv1结构（推荐）
├─ multibase: 编码方式标识（如base32）
│
├─ version: CID版本号（0x01）
│
├─ multicodec: 内容类型编码
│   ├─ 0x70 = dag-pb (protobuf)
│   ├─ 0x71 = dag-cbor
│   ├─ 0x55 = raw binary
│   └─ 0x12 = sha2-256
│
└─ multihash: 哈希值
    ├─ hash function code
    ├─ hash length
    └─ hash digest

示例 CIDv1:
bafybeigdyrzt5sfp7udm7hu76uh7y26nf3efuylqabf3oclgtqy55fbzdi
│└──────────  multihash (sha2-256) ──────────┘
└── multibase (base32)
```

### 2.2 CID版本

| 特性 | CIDv0 | CIDv1 |
|------|-------|-------|
| **编码** | Base58btc | Multibase |
| **版本位** | 无 | 有 |
| **编解码器** | 固定dag-pb | 可配置 |
| **哈希函数** | 固定sha2-256 | 可配置 |
| **示例** | Qm... | bafy... |

**CIDv0格式**：

```
QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG
└──────────────── multihash ────────────────┘
     sha2-256(32字节) + base58btc编码
```

### 2.3 Multiformats

**自描述格式体系**：

```
┌─────────────────────────────────────────────────────────────┐
│                    Multiformats家族                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │  Multibase   │  │  Multicodec  │  │  Multihash   │      │
│  │  (编码)       │  │  (编解码器)  │  │  (哈希)      │      │
│  │              │  │              │  │              │      │
│  │  base58btc   │  │  dag-pb      │  │  sha2-256    │      │
│  │  base32      │  │  dag-cbor    │  │  sha3-256    │      │
│  │  base64      │  │  raw         │  │  blake2b-256 │      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
│                                                             │
│  组合示例：                                                  │
│  cid = multibase(multicodec + multihash(data))             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**常用Multicodec代码**：

| 代码 | 名称 | 用途 |
|------|------|------|
| 0x70 | dag-pb | Merkle DAG protobuf |
| 0x71 | dag-cbor | Merkle DAG CBOR |
| 0x55 | raw | 原始二进制数据 |
| 0x12 | sha2-256 | SHA2-256哈希 |
| 0x1b | sha3-256 | SHA3-256哈希 |
| 0xb220 | blake2b-256 | Blake2b-256哈希 |

---

## 三、Merkle DAG

### 3.1 Merkle DAG结构

**Merkle DAG是IPFS的核心数据结构**：

```
┌─────────────────────────────────────────────────────────────┐
│                    Merkle DAG节点                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────┐                                            │
│  │  UnixFS Node │                                           │
│  ├─────────────┤                                            │
│  │  Data:      │  实际文件内容（如果是叶子节点）            │
│  │  Links:     │                                            │
│  │    ┌─────┐  │  ┌─────┐  ┌─────┐                         │
│  │    │Link1│──┼─→│ CID │  │ Name│  Size                    │
│  │    └─────┘  │  └─────┘  └─────┘                         │
│  │    ┌─────┐  │                                            │
│  │    │Link2│──┼─→ 子节点CID                                │
│  │    └─────┘  │                                            │
│  └─────────────┘                                            │
│                                                             │
│  CID = Hash(Data + Links)                                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 文件分块

**大文件分块策略**：

```
文件大小      块大小       布局
──────────────────────────────────────────
< 256KB      整个文件     单节点
256KB-1MB    256KB        平衡树
1MB-?        256KB        平衡树（可能多层）

示例：1MB文件
┌─────────────────────────────────────────┐
│              Root Node                  │
│  CID: QmRoot                            │
│  Links: [QmA, QmB, QmC, QmD]            │
└─────────────────────────────────────────┘
       │      │      │      │
       ↓      ↓      ↓      ↓
    ┌────┐  ┌────┐  ┌────┐  ┌────┐
    │256K│  │256K│  │256K│  │256K│
    │ QmA│  │ QmB│  │ QmC│  │ QmD│
    └────┘  └────┘  └────┘  └────┘
```

### 3.3 去重机制

**内容寻址天然去重**：

```
用户A上传文件X ──→ IPFS计算CID: QmX ──→ 存储到本地
                            │
                            ↓
用户B上传相同文件X ──→ IPFS计算CID: QmX（相同）
                            │
                            ↓
                     发现已有QmX，无需重复存储
                     只需在B的pin列表添加引用
```

**好处**：

- 节省存储空间
- 加速内容传播
- 版本管理高效

### 3.4 UnixFS

**Unix文件系统抽象**：

```go
// UnixFS节点类型
enum DataType {
    Raw = 0;        // 原始数据
    Directory = 1;  // 目录
    File = 2;       // 文件
    Metadata = 3;   // 元数据
    Symlink = 4;    // 符号链接
    HAMTShard = 5;  // HAMT分片（大目录）
}

// UnixFS消息格式
message Data {
    DataType Type = 1;
    bytes Data = 2;
    uint64 filesize = 3;
    repeated uint64 blocksizes = 4;
    uint64 hashType = 5;
    uint64 fanout = 6;
    uint64 mode = 7;
    UnixTime mtime = 8;
}
```

---

## 四、BitSwap协议

### 4.1 协议概述

**BitSwap是IPFS的数据交换协议**：

```
核心设计原则：
1. 节点寻求下载block并上传block给其他节点
2. 不只有关系，独立决策
3. 激励节点共享（信用/债务系统）
4. 防止水蛭（只下载不上传）
```

**与BitTorrent对比**：

| 特性 | BitTorrent | BitSwap |
|------|-----------|---------|
| 交换单位 | Piece (256KB-4MB) | Block (256KB) |
| 激励机制 | Tit-for-tat | 信用账本 |
| 查找机制 | Tracker/DHT | DHT only |
| 数据模型 | 单文件 | Merkle DAG |
| 去重 | 单torrent内 | 全局去重 |

### 4.2 消息类型

```protobuf
message Message {
    message Wantlist {
        message Entry {
            bytes block = 1;      // CID前缀
            int32 priority = 2;    // 优先级
            bool cancel = 3;       // 取消请求
        }
        repeated Entry entries = 1;
        bool full = 2;             // 是否完整wantlist
    }

    message Block {
        bytes prefix = 1;          // CID前缀
        bytes data = 2;            // 数据
    }

    Wantlist wantlist = 1;
    repeated bytes blocks = 2;     // 原始block（旧版本）
    repeated Block payload = 3;    // 带CID的block
}
```

### 4.3 信用账本机制

**BitSwap Ledger**：

```
每个peer维护：
{
    peer_id: <peer identity>,
    sent: <bytes sent>,      // 已发送给对方
    received: <bytes received>, // 已从对方接收
    debt_ratio: received / sent  // 债务比率
}

决策策略：
- debt_ratio < 阈值：继续发送
- debt_ratio > 阈值：概率性拒绝或降低优先级
- 新peer：给予小额信用额度
```

### 4.4 请求流程

```
┌──────────┐                           ┌──────────┐
│  Node A  │                           │  Node B  │
│ (需要QmX) │                           │(拥有QmX) │
└────┬─────┘                           └────┬─────┘
     │                                      │
     │────── wantlist [QmX] ───────────────→│
     │                                      │
     │←───── block data for QmX ────────────│
     │                                      │
     │────── update ledger (received) ─────→│
     │                                      │
     │←───── update ledger (sent) ──────────│
     │                                      │
```

---

## 五、IPNS命名系统

### 5.1 为什么需要IPNS

**CID的局限性**：

```
问题：
网站 /ipfs/QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG
       └── 内容改变 → CID改变 → 链接失效

解决方案：
IPNS提供可变的指针指向不可变的CID
/ipns/k51qzi5uqu5dhl5q23p... → /ipfs/QmXgB6cM2SRai...
```

### 5.2 IPNS机制

**基于公钥的命名**：

```
生成IPNS密钥对：
  Private Key ──→ 用于签名IPNS记录
  Public Key ──→ 生成IPNS名称 (/ipns/<peer-id>)

IPNS记录结构：
{
    value: "/ipfs/QmNewContent",  // 指向的CID
    validity: "2027-01-01T00:00:00Z",  // 有效期
    validityType: 0,              // 0=EOL, 1=有效期时长
    sequence: 42,                 // 序列号（防重放）
    signature: <签名>             // 私钥签名
}
```

### 5.3 记录发布与解析

```
发布流程：
1. 创建或更新IPNS记录
2. 使用私钥签名记录
3. 通过DHT发布到网络
   - 记录key: /ipns/<peer-id>
   - 记录value: 序列化的IPNS记录

解析流程：
1. 解析 /ipns/<peer-id>
2. DHT查询 /ipns/<peer-id>
3. 获取IPNS记录
4. 验证签名
5. 提取并返回CID
```

### 5.4 DNSLink

**通过DNS解析IPNS**：

```
DNS配置：
_dnslink.example.com TXT "dnslink=/ipfs/QmXgB6cM2..."

解析：
/ipns/example.com ──→ 查询DNS ──→ 获取CID

或者：
_dnslink.example.com TXT "dnslink=/ipns/k51qzi5u..."
/ipns/example.com ──→ 查询DNS ──→ 获取IPNS ──→ 获取CID
```

---

## 六、路由与发现

### 6.1 DHT路由

**IPFS使用Kademlia DHT变体**：

```
DHT记录类型：
1. Provider记录：谁拥有某内容
   Key: /provider/<CID>
   Value: [peer-id1, peer-id2, ...]

2. IPNS记录：可变命名指向
   Key: /ipns/<peer-id>
   Value: 签名的IPNS记录

3. Peer路由：peer的网络地址
   Key: /ipfs/<peer-id>
   Value: 多地址列表
```

**内容提供流程**：

```
节点A提供QmX：
1. A计算DHT key: /provider/QmX
2. A找到距离key最近的k个节点
3. 在这些节点存储provider记录
4. 定期刷新（默认12小时）

节点B查找QmX：
1. B计算DHT key: /provider/QmX
2. B查询距离key最近的节点
3. 获取存储的provider记录
4. 连接这些provider获取内容
```

### 6.2 内容路由优化

**多层路由策略**：

```
查找CID: QmX
│
├── 1. 本地块存储
│   └── 命中 → 直接返回
│
├── 2. 节点缓存
│   └── 查询已连接的peer
│
├── 3. 预加载节点
│   └── 查询配置的预加载节点
│
└── 4. DHT查找
    └── 全网DHT查询
```

### 6.3 libp2p网络层

**libp2p模块化设计**：

```
┌─────────────────────────────────────────────────────────────┐
│                      libp2p模块                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │  Transport  │  │  Security   │  │  Multiplex  │         │
│  │             │  │             │  │             │         │
│  │ • TCP       │  │ • TLS       │  │ • Yamux     │         │
│  │ • WebSocket │  │ • Noise     │  │ • mplex     │         │
│  │ • QUIC      │  │ • SecIO     │  │             │         │
│  │ • WebRTC    │  │             │  │             │         │
│  └─────────────┘  └─────────────┘  └─────────────┘         │
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │   Peer ID   │  │   Routing   │  │   PubSub    │         │
│  │             │  │             │  │             │         │
│  │ • Ed25519   │  │ • DHT       │  │ • FloodSub  │         │
│  │ • Secp256k1 │  │ • MDNS      │  │ • GossipSub │         │
│  │             │  │ • Delegated │  │             │         │
│  └─────────────┘  └─────────────┘  └─────────────┘         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 七、实践应用

### 7.1 IPFS常用操作

```bash
# 初始化节点
ipfs init

# 启动守护进程
ipfs daemon

# 添加文件
ipfs add file.txt
# 输出: added QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG file.txt

# 添加目录
ipfs add -r mydirectory/

# 获取文件
ipfs get QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG -o file.txt

# 查看内容
ipfs cat QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG

# 固定内容（防止GC）
ipfs pin add QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG

# 发布IPNS
ipfs name publish QmXgB6cM2SRaiqpEr6Qwd2pr1XohF8WkwSUGyYF3h1LRhG
# 输出: Published to k51qzi5uqu5dhl5q23p...: QmXgB6cM2...

# 解析IPNS
ipfs name resolve k51qzi5uqu5dhl5q23p...
```

### 7.2 IPFS网关

**公共网关**：

| 网关 | URL |
|------|-----|
| ipfs.io | <https://ipfs.io/ipfs/{cid}> |
| cloudflare | <https://cloudflare-ipfs.com/ipfs/{cid}> |
| dweb.link | https://{cid}.ipfs.dweb.link |
| pinata | <https://gateway.pinata.cloud/ipfs/{cid}> |

**网关类型**：

```
路径网关: https://ipfs.io/ipfs/QmXgB6cM2...
子域名网关: https://QmXgB6cM2.ipfs.dweb.link
           （更好的安全隔离）
```

### 7.3 IPFS与Filecoin

**关系**：

```
┌─────────────────────────────────────────────────────────────┐
│                    IPFS + Filecoin                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  IPFS:                                                      │
│  • 内容寻址传输协议                                          │
│  • 提供热存储（缓存）                                        │
│  • 不保证持久性                                              │
│                                                             │
│  Filecoin:                                                  │
│  • 基于IPFS的激励层                                          │
│  • 提供冷存储（持久化）                                       │
│  • 通过经济激励保证数据可用性                                 │
│                                                             │
│  集成方式：                                                  │
│  1. IPFS获取热门内容（快速）                                  │
│  2. Filecoin备份重要内容（持久）                              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 八、与其他主题的关联

### 8.1 上游依赖

- [分布式哈希表](../dht.md)
- [点对点网络](../../03-network/p2p-networks.md)
- [Merkle树](../../02-foundations/cryptography.md)
- [BitTorrent协议](./BitTorrent协议.md)

### 8.2 下游应用

- [去中心化存储](../decentralized-storage.md)
- [Web3基础设施](../web3-infrastructure.md)
- [NFT存储](../nft-storage.md)

### 8.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| Filecoin | 扩展 | IPFS的激励层，提供持久存储 |
| libp2p | 基础 | IPFS底层的P2P网络库 |
| IPLD | 基础 | 星际关联数据，统一数据模型 |
| OrbitDB | 应用 | 基于IPFS的分布式数据库 |

---

## 九、参考资源

### 9.1 官方文档

1. [IPFS Documentation](https://docs.ipfs.io/) - 官方文档
2. [IPFS Specs](https://specs.ipfs.tech/) - 协议规范
3. [libp2p Documentation](https://docs.libp2p.io/) - 网络层文档
4. [IPLD Specifications](https://ipld.io/specs/) - 数据模型规范

### 9.2 学术论文

1. [IPFS - Content Addressed, Versioned, P2P File System](https://github.com/ipfs/papers/raw/master/ipfs-cap2pfs/ipfs-p2p-file-system.pdf) - Juan Benet, 2014
2. [Kademlia: A Peer-to-peer Information System](https://pdos.csail.mit.edu/~petar/papers/maymounkov-kademlia-lncs.pdf) - Maymounkov & Mazieres, 2002

### 9.3 开源项目

1. [go-ipfs/kubo](https://github.com/ipfs/kubo) - Go语言实现
2. [js-ipfs](https://github.com/ipfs/js-ipfs) - JavaScript实现
3. [rust-ipfs](https://github.com/rs-ipfs/rust-ipfs) - Rust实现
4. [ipfs-cluster](https://github.com/ipfs/ipfs-cluster) - IPFS集群管理

### 9.4 学习资料

1. [ProtoSchool](https://proto.school/) - IPFS互动教程
2. [IPFS命令行速查表](https://github.com/ipfs/ipfs-camp-workshop) - 实践指南
3. [IPFS设计哲学](https://docs.ipfs.io/concepts/) - 概念详解

### 9.5 相关文档

- [区块链基础](./区块链基础.md)
- [区块链共识机制](./区块链共识机制.md)
- [BitTorrent协议](./BitTorrent协议.md)

---

**维护者**：项目团队
**最后更新**：2026年
