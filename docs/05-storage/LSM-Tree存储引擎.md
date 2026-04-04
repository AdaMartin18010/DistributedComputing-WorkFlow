# LSM-Tree存储引擎专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

LSM-Tree（Log-Structured Merge Tree）是一种写优化的数据结构，通过将随机写转换为顺序写，配合后台Compaction机制，实现高吞吐写入和高效读取。RocksDB和LevelDB是该结构的代表实现，广泛应用于分布式存储、时序数据库和键值存储系统。

---

## 一、核心概念

### 1.1 LSM-Tree定义与原理

**LSM-Tree**核心思想：

- **写入路径**：数据先写入内存（MemTable），再顺序刷盘（SSTable）
- **读取路径**：按时间顺序从MemTable到各级SSTable查找
- **合并机制**：后台Compaction整合数据，清理过期版本

```
LSM-Tree架构概览：
┌─────────────────────────────────────────────────────────────┐
│                      写入路径（Write Path）                    │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────┐  │
│  │ 客户端写入  │ →  │  WAL日志    │ →  │  MemTable       │  │
│  │  (Put/Del)  │    │ (顺序写)    │    │  (内存有序结构)  │  │
│  └─────────────┘    └─────────────┘    └────────┬────────┘  │
│                                                  ↓          │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              Immutable MemTable（不可变内存表）          │  │
│  │              达到阈值后转为只读，后台刷盘                │  │
│  └───────────────────────────┬───────────────────────────┘  │
│                              ↓                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │                 Level 0 SSTable（Level 0）              │  │
│  │                 直接由MemTable转换，可能重叠             │  │
│  └───────────────────────────┬───────────────────────────┘  │
│                              ↓ Compaction                   │
│  ┌───────────────────────────────────────────────────────┐  │
│  │              Level 1 ~ N SSTable（层级结构）             │  │
│  │              每层数据有序且不重叠，容量呈指数增长         │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│                      读取路径（Read Path）                     │
│                                                            │
│  查询Key=X                                                │
│       ↓                                                     │
│  ┌──────────┐ ┌──────────────┐ ┌────────┐ ┌────────┐       │
│  │MemTable  │→│Immutable Mem │→│L0 SST  │→│L1 SST  │→...   │
│  │ (跳表)   │  │  (跳表/排序)  │  │(多文件)│  │(有序)  │       │
│  └──────────┘ └──────────────┘ └────────┘ └────────┘       │
│       ↓                                                     │
│   找到Key → 返回最新版本                                     │
│   未找到  → 继续下一层                                       │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 核心组件详解

#### MemTable（内存表）

```
MemTable实现：跳表（Skip List）
┌─────────────────────────────────────────────────────────────┐
│                     Skip List 结构                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Level 3:  head ─────────────────────────────→  tail       │
│                  ↓                                          │
│  Level 2:  head ────────→ [30] ─────────────→  tail       │
│                  ↓         ↓                                │
│  Level 1:  head ───→[20]→[30]────→[50]────→  tail          │
│                  ↓    ↓    ↓       ↓                        │
│  Level 0:  head→[10]→[20]→[30]→[40]→[50]→[60]→  tail       │
│                                                            │
│  特性：                                                      │
│  - 插入/删除/查找：O(log n)                                  │
│  - 支持范围查询                                              │
│  - 并发安全（CAS操作）                                        │
│  - 内存有序，便于转SSTable                                    │
└─────────────────────────────────────────────────────────────┘
```

#### SSTable（Sorted String Table）

```
SSTable文件格式：
┌─────────────────────────────────────────────────────────────┐
│                    SSTable 文件结构                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Data Block 1                                          │ │
│  │ ┌─────────────────────────────────────────────────┐  │ │
│  │ │ 共享前缀长度 │ 非共享长度 │ 值长度 │ 键差值 │ 值   │  │ │
│  │ │  (varint)  │  (varint) │(varint)│(bytes)│(bytes)│  │ │
│  │ └─────────────────────────────────────────────────┘  │ │
│  │ ┌─────────────────────────────────────────────────┐  │ │
│  │ │ 重启点（Restart Point）                         │  │ │
│  │ │ 每16个Entry记录完整Key位置，便于二分查找          │  │ │
│  │ └─────────────────────────────────────────────────┘  │ │
│  └───────────────────────────────────────────────────────┘ │
│                           ...                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Data Block N                                          │ │
│  └───────────────────────────────────────────────────────┘ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Meta Block: Filter Block (Bloom Filter)               │ │
│  │ 用于快速判断Key是否可能存在，减少磁盘I/O               │ │
│  └───────────────────────────────────────────────────────┘ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Meta Block: Index Block                               │ │
│  │ 记录每个Data Block的起始Key和偏移量                    │ │
│  └───────────────────────────────────────────────────────┘ │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Footer (固定48字节)                                   │ │
│  │ ├─ Meta Index Block 偏移量和大小                      │ │
│  │ ├─ Index Block 偏移量和大小                           │ │
│  │ └─ 魔数（Magic Number）                               │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.3 关键特性

| 特性 | 说明 | 优势 |
|------|------|------|
| **写优化** | 顺序写入WAL和SSTable | 磁盘I/O效率高 |
| **批量合并** | 后台Compaction整合数据 | 读取性能优化 |
| **版本控制** | 支持多版本数据共存 | MVCC实现简单 |
| **Bloom Filter** | 快速判断Key是否存在 | 减少无效I/O |
| **分层存储** | 冷热数据自动分层 | 存储效率高 |

### 1.4 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 高吞吐写入 | ⭐⭐⭐⭐⭐ | 顺序写优势显著 |
| 时序数据 | ⭐⭐⭐⭐⭐ | 时间有序写入 |
| 键值存储 | ⭐⭐⭐⭐⭐ | 简单查询模型 |
| 日志存储 | ⭐⭐⭐⭐⭐ | 追加写特性匹配 |
| 范围查询 | ⭐⭐⭐⭐ | SSTable有序支持 |
| 点查随机读 | ⭐⭐⭐ | 需多层查找 |
| 事务处理 | ⭐⭐ | 需上层封装 |
| 复杂查询 | ⭐ | 需配合索引 |

---

## 二、技术细节

### 2.1 写入流程

```
┌─────────────────────────────────────────────────────────────┐
│                    完整写入流程                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  1. 写入WAL（Write Ahead Log）                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Log Record:                                           │ │
│  │ ├─ CRC32 Checksum                                    │ │
│  │ ├─ Length                                            │ │
│  │ ├─ Type (PUT/DELETE/MERGE)                           │ │
│  │ └─ Key-Value Data                                    │ │
│  └───────────────────────────────────────────────────────┘ │
│  → fsync确保持久化（可配置sync间隔）                         │
│                                                            │
│  2. 写入MemTable                                          │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ InternalKey:                                          │ │
│  │ ├─ User Key                                          │ │
│  │ ├─ Sequence Number (7 bytes, 全局递增)                │ │
│  │ └─ Value Type (1 byte: TypeValue/TypeDeletion)       │ │
│  │                                                       │ │
│  │ MemTable 格式: InternalKey → Value (跳表存储)          │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  3. MemTable Flush（后台线程）                               │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ 触发条件：                                              │ │
│  │ ├─ MemTable大小超过write_buffer_size (默认64MB)       │ │
│  │ ├─ WAL日志过大需截断                                    │ │
│  │ └─ 手动触发(flush)                                     │ │
│  │                                                       │ │
│  │ 转换过程：                                              │ │
│  │ ├─ 冻结当前MemTable → Immutable MemTable              │ │
│  │ ├─ 创建新MemTable接收写入                               │ │
│  │ └─ 后台线程将Immutable转为L0 SSTable                   │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Compaction机制

```
┌─────────────────────────────────────────────────────────────┐
│                    Compaction 策略与流程                     │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Level结构（Leveled Compaction）：                           │
│                                                            │
│  L0: ┌───┐┌───┐┌───┐┌───┐        ← 可能重叠                │
│      │ 1 ││ 2 ││ 3 ││ 4 │ (最多4个文件)                      │
│      └───┘└───┘└───┘└───┘                                  │
│        ↓ 当文件数超过阈值，触发Compaction                   │
│  L1: ┌─────────────────────────────────────────────────┐    │
│      │  总大小 ≤ 10MB                                  │    │
│      │  数据有序且不重叠                                │    │
│      └─────────────────────────────────────────────────┘    │
│        ↓ L1满后，与L2重叠部分合并                           │
│  L2: ┌─────────────────────────────────────────────────┐    │
│      │  总大小 ≤ 100MB (10×L1)                         │    │
│      └─────────────────────────────────────────────────┘    │
│        ↓ ...                                               │
│  LN: 每层容量是上层的10倍                                   │
│                                                            │
│  Compaction触发条件：                                       │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ L0→L1: L0文件数 > level0_file_num_compaction_trigger  │ │
│  │ LN→LN+1: 层大小 > level_max_bytes                     │ │
│  │ 手动触发: CompactRange()                              │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  Compaction过程：                                           │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ 1. 选择输入文件（根据分数或大小优先级）                   │ │
│  │ 2. 确定与下层重叠的文件范围                              │ │
│  │ 3. 多路归并排序合并                                      │ │
│  │ 4. 生成新的SSTable文件                                   │ │
│  │ 5. 原子替换元数据（Manifest更新）                        │ │
│  │ 6. 删除旧文件（延迟删除，确保无读引用）                   │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

#### Compaction策略对比

| 策略 | 写放大 | 读放大 | 空间放大 | 适用场景 |
|------|--------|--------|----------|----------|
| **Leveled** | 高 | 低 | 低 | 读多写少 |
| **Tiered** | 低 | 高 | 高 | 写多读少 |
| **Leveled-N** | 中 | 中 | 中 | 混合负载 |
| **FIFO** | 最低 | 中 | 最高 | 缓存场景 |

### 2.3 读取流程

```
┌─────────────────────────────────────────────────────────────┐
│                    完整读取流程                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  查询Key = "user:1001"                                     │
│       ↓                                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Step 1: 检查MemTable                                  │ │
│  │ ├─ 在跳表中查找InternalKey                            │ │
│  │ ├─ 找到：返回Value（含删除标记检查）                   │ │
│  │ └─ 未找到：继续下一步                                  │ │
│  └───────────────────────────────────────────────────────┘ │
│       ↓                                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Step 2: 检查Immutable MemTable                        │ │
│  │ 逻辑同Step 1                                            │ │
│  └───────────────────────────────────────────────────────┘ │
│       ↓                                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Step 3: 检查Block Cache（可选的页缓存）                 │ │
│  │ ├─ 缓存命中：直接返回                                   │ │
│  │ └─ 未命中：继续下一步                                   │ │
│  └───────────────────────────────────────────────────────┘ │
│       ↓                                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Step 4: 遍历各层SSTable                                │ │
│  │                                                       │ │
│  │ For each Level (L0 → L1 → L2 ...):                    │ │
│  │   For each SSTable in Level (按文件号倒序):            │ │
│  │     1. 检查Bloom Filter                               │ │
│  │        ├─ Filter返回肯定不存在 → 跳过该文件             │ │
│  │        └─ Filter返回可能存在 → 继续                    │ │
│  │     2. 加载Index Block                                │ │
│  │     3. 二分查找定位Data Block                         │ │
│  │     4. 加载Data Block（加入Block Cache）               │ │
│  │     5. 在Block内二分查找Key                           │ │
│  │     6. 找到 → 返回Value                               │ │
│  │     7. 未找到 → 继续下一文件/下一层                    │ │
│  └───────────────────────────────────────────────────────┘ │
│       ↓                                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ Step 5: 遍历完所有层仍未找到                           │ │
│  │ └─ 返回Key Not Found                                   │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、系统对比

### 3.1 主流LSM-Tree实现对比

| 维度 | LevelDB | RocksDB | TiKV | ScyllaDB |
|------|---------|---------|------|----------|
| **开发方** | Google | Facebook/Meta | PingCAP | ScyllaDB |
| **语言** | C++ | C++ | Rust (TiKV) | C++ |
| **特点** | 轻量、嵌入式 | 功能丰富、生产级 | 分布式 | C++重写Cassandra |
| **Compaction** | Leveled | Leveled/Tiered/Universal | Leveled | Size-Tiered |
| **事务** | 快照隔离 | 悲观/乐观事务 | Percolator | LWT |
| **压缩** | Snappy | 多算法可选 | Snappy/LZ4 | LZ4 |
| **适用** | 单节点应用 | 大规模生产 | 分布式系统 | 高吞吐写入 |

### 3.2 RocksDB高级特性

```
RocksDB架构增强：
┌─────────────────────────────────────────────────────────────┐
│                    RocksDB 特性矩阵                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Column Family（列族）：                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Default CF │ Metadata CF │ Data CF                   │ │
│  │  独立WAL    │ 独立MemTable │ 独立SST文件               │ │
│  │  共享块缓存和线程池                                      │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  高级功能：                                                  │
│  ├─ TransactionDB: 支持ACID事务                            │
│  ├─ BlobDB: 大值分离存储（Key-Value分离）                   │
│  ├─ PlainTable: 内存映射优化（全内存场景）                   │
│  ├─ Merge Operator: 增量合并操作                           │
│  ├─ Checkpoints: 快速快照备份                              │
│  └─ BackupEngine: 热备份支持                               │
│                                                            │
│  调优选项：                                                  │
│  ├─ Compaction优先级算法                                   │
│  ├─ 分级压缩策略                                           │
│  ├─ 动态Compaction线程数                                   │
│  └─ 前缀布隆过滤器                                         │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 3.3 性能基准

| 指标 | LevelDB | RocksDB (默认) | RocksDB (调优) |
|------|---------|----------------|----------------|
| 随机写OPS | 80,000 | 150,000 | 400,000 |
| 随机读OPS | 100,000 | 180,000 | 300,000 |
| 顺序写MB/s | 200 | 350 | 500 |
| 范围查询 | 中等 | 良好 | 优秀 |
| 内存占用 | 低 | 中 | 可调 |

---

## 四、实践指南

### 4.1 RocksDB部署配置

```cpp
// RocksDB 基础配置示例
#include "rocksdb/db.h"
#include "rocksdb/options.h"

using namespace rocksdb;

Options CreateOptimizedOptions() {
    Options options;

    // ========== 基础配置 ==========
    options.create_if_missing = true;
    options.compression = kLZ4Compression;  // 压缩算法

    // ========== MemTable配置 ==========
    options.write_buffer_size = 64 * 1024 * 1024;  // 64MB
    options.max_write_buffer_number = 3;
    options.min_write_buffer_number_to_merge = 1;

    // 使用跳表（默认）或哈希跳表（prefix keys）
    options.memtable_factory.reset(
        NewHashSkipListRepFactory(1000000));

    // ========== SSTable配置 ==========
    options.target_file_size_base = 64 * 1024 * 1024;  // 64MB
    options.target_file_size_multiplier = 2;

    // Block大小和缓存
    BlockBasedTableOptions table_options;
    table_options.block_size = 16 * 1024;  // 16KB
    table_options.block_cache = NewLRUCache(8 * 1024 * 1024 * 1024LL);  // 8GB
    table_options.filter_policy.reset(NewBloomFilterPolicy(10));  // 10bits/key
    options.table_factory.reset(NewBlockBasedTableFactory(table_options));

    // ========== Compaction配置 ==========
    options.compaction_style = kCompactionStyleLevel;
    options.level0_file_num_compaction_trigger = 4;
    options.level0_slowdown_writes_trigger = 20;
    options.level0_stop_writes_trigger = 36;
    options.max_bytes_for_level_base = 256 * 1024 * 1024;  // 256MB
    options.max_bytes_for_level_multiplier = 10;

    // ========== 并行配置 ==========
    options.max_background_jobs = 8;
    options.max_subcompactions = 4;  // 子Compaction并行度

    // ========== WAL配置 ==========
    options.max_total_wal_size = 1 * 1024 * 1024 * 1024;  // 1GB

    // ========== 布隆过滤器配置 ==========
    // 使用前缀布隆过滤器
    options.prefix_extractor.reset(NewFixedPrefixTransform(8));

    return options;
}
```

### 4.2 最佳实践

#### 1. 写优化

```cpp
// 批量写入
WriteBatch batch;
batch.Put("key1", "value1");
batch.Put("key2", "value2");
batch.Delete("key3");
db->Write(WriteOptions(), &batch);

// 异步WAL（权衡持久性）
WriteOptions write_options;
write_options.sync = false;  // 不立即fsync
write_options.disableWAL = false;  // 但不禁用WAL
db->Put(write_options, "key", "value");

// 使用WriteBufferManager限制内存
std::shared_ptr<WriteBufferManager> wbm(
    new WriteBufferManager(1 * 1024 * 1024 * 1024));  // 1GB上限
options.write_buffer_manager = wbm;
```

#### 2. 读优化

```cpp
// 使用Snapshot实现一致性读
ReadOptions read_options;
read_options.snapshot = db->GetSnapshot();
// ... 读取操作 ...
db->ReleaseSnapshot(read_options.snapshot);

// 前缀迭代器
ReadOptions prefix_opts;
prefix_opts.prefix_same_as_start = true;
auto iter = db->NewIterator(prefix_opts);
iter->Seek("prefix:");

// 布隆过滤器减少I/O
// 配置已在前面示例中展示
```

#### 3. Compaction调优

| 场景 | 推荐策略 | 关键参数 |
|------|----------|----------|
| 写密集 | Universal | compaction_style=kCompactionStyleUniversal |
| 读密集 | Leveled | compaction_style=kCompactionStyleLevel |
| 混合负载 | Leveled-N | level_compaction_dynamic_level_bytes=true |
| 时序数据 | FIFO | compaction_style=kCompactionStyleFIFO |

### 4.3 常见问题

**Q1: 写放大如何计算？**
A: 写放大 = 实际写入磁盘的数据量 / 应用写入的数据量。LSM-Tree写放大通常在10-30倍，可通过Tiered Compaction降低。

**Q2: 空间放大如何处理？**
A: 空间放大 = 数据库实际占用空间 / 数据逻辑大小。通过及时Compaction、删除过期版本、压缩策略优化来降低。

**Q3: 读取为什么会"越读越慢"？**
A: 通常由于：1) L0文件堆积；2) 未命中Block Cache；3) 范围查询扫描大量过期版本。需监控Compaction状态和缓存命中率。

**Q4: 如何估算内存使用？**
A: 内存 ≈ MemTable(64MB × 3) + BlockCache(配置值) + Index/Filter(约10%数据量) + 其他开销。

---

## 五、形式化分析

### 5.1 复杂度分析

| 操作 | 时间复杂度 | 说明 |
|------|------------|------|
| 写入 | O(log n) | 跳表插入 + 可能触发flush |
| 点查 | O(log n) | 最多查找L0到Ln各层 |
| 范围查 | O(log n + k) | k为返回条数 |
| Compaction | O(n) | 全量重写该层数据 |

### 5.2 放大因子分析

```
Leveled Compaction放大因子：
- 层数 L = log_T(N/S)
  T: 放大倍数(默认10), N: 数据总量, S: L1大小

- 读放大(R) = L（最多读取每层一个SSTable）
  最坏情况: R = T-1（L0层文件全部重叠）

- 写放大(W) ≈ T × (L-1) = O(T × log_T(N/S))
  每层数据会被向下Compaction T次

- 空间放大(S) ≈ 1/(T-1) = O(1/T)
  每层最多保留T倍冗余

调优方向：
- 增大T → 降低写放大，增加读放大
- 减小T → 降低读放大，增加写放大
- 使用Tiered → 大幅降低写放大，增加读放大和空间放大
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [数据复制](./主从复制原理.md)
- [分布式事务](../08-transactions/分布式事务.md)

### 6.2 下游应用

- [TiKV架构](../07-architecture/TiKV架构.md)
- [CockroachDB架构](../07-architecture/CockroachDB架构.md)

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| B+树 | 对比 | 读优化vs写优化 |
| 日志存储 | 应用 | LSM天然适合日志 |
| 分布式KV | 基础 | TiKV、FoundationDB底层 |

---

## 七、参考资源

### 7.1 学术论文

1. [The Log-Structured Merge-Tree](https://www.cs.umb.edu/~poneil/lsmtree.pdf) - O'Neil et al., 1996
2. [WiscKey: Separating Keys from Values in SSD-conscious Storage](https://www.usenix.org/system/files/conference/fast16/fast16-papers-lu.pdf) - Lu et al., 2016

### 7.2 开源项目

1. [LevelDB](https://github.com/google/leveldb) - Google官方实现
2. [RocksDB](https://github.com/facebook/rocksdb) - Facebook增强版
3. [TiKV](https://github.com/tikv/tikv) - 分布式LSM实现

### 7.3 学习资料

1. [RocksDB Tuning Guide](https://github.com/facebook/rocksdb/wiki/RocksDB-Tuning-Guide)
2. [LSM-Tree原理详解](https://segmentfault.com/a/1190000040230493)
3. 《Designing Data-Intensive Applications》Chapter 3

### 7.4 相关文档

- [B-Tree存储引擎](./B-Tree存储引擎.md)
- [存储引擎对比](./存储引擎对比.md)

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年


---

## 相关主题

- [B-Tree存储引擎](./B-Tree存储引擎.md)
- [存储引擎对比](./存储引擎对比.md)
- [RocksDB官方文档](https://rocksdb.org/)

## 参考资源

- [LevelDB](https://github.com/google/leveldb)
- [RocksDB](https://rocksdb.org/)
