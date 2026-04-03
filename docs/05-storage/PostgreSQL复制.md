# PostgreSQL复制专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

PostgreSQL提供强大的复制功能，包括物理流复制（Streaming Replication）和逻辑复制（Logical Replication）两大体系。物理复制用于高可用和读扩展，逻辑复制用于数据集成和版本升级。本文档详细阐述两种复制机制的原理、配置和最佳实践。

---

## 一、核心概念

### 1.1 复制类型对比

```
┌─────────────────────────────────────────────────────────────┐
│                PostgreSQL 复制类型对比                       │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  物理复制 (Physical Replication)                      │ │
│  │                                                       │ │
│  │  原理：                                                │ │
│  │  ├─ 基于WAL (Write-Ahead Log) 物理日志                 │ │
│  │  ├─ 主库写入WAL → 从库接收并重放                        │ │
│  │  └─ 块级别复制，完全一致                               │ │
│  │                                                       │ │
│  │  Master                Standby                        │ │
│  │  ┌─────────┐          ┌─────────┐                     │ │
│  │  │ INSERT  │──WAL───→ │ 重放    │                     │ │
│  │  │ UPDATE  │──WAL───→ │ 重放    │                     │ │
│  │  │ DELETE  │──WAL───→ │ 重放    │                     │ │
│  │  └─────────┘          └─────────┘                     │ │
│  │                                                       │ │
│  │  特点：                                                │ │
│  │  ├─ 完全一致（包括索引、统计信息）                      │ │
│  │  ├─ 低延迟（异步/同步可选）                            │ │
│  │  ├─ 支持级联复制                                       │ │
│  │  ├─ 支持热备（Hot Standby）                            │ │
│  │  └─ 不能选择性复制                                     │ │
│  │                                                       │ │
│  │  适用：高可用、读写分离                                │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  逻辑复制 (Logical Replication)                       │ │
│  │                                                       │ │
│  │  原理：                                                │ │
│  │  ├─ 基于逻辑解码（Logical Decoding）                   │ │
│  │  ├─ 将WAL解析为逻辑变更（INSERT/UPDATE/DELETE）         │ │
│  │  └─ 行级别复制，可跨版本、跨平台                       │ │
│  │                                                       │ │
│  │  Publisher             Subscriber                     │ │
│  │  ┌─────────┐          ┌─────────┐                     │ │
│  │  │ Table A │──逻辑变更─→│ Table A │                     │ │
│  │  │ Table B │──X───────→│ (不复制)│                     │ │
│  │  │ Table C │──逻辑变更─→│ Table C │                     │ │
│  │  └─────────┘          └─────────┘                     │ │
│  │       ↑                      ↑                        │ │
│  │   可过滤                   可转换                      │ │
│  │   行/列                    数据类型                    │ │
│  │                                                       │ │
│  │  特点：                                                │ │
│  │  ├─ 可选择性复制（表级、行级、列级）                     │ │
│  │  ├─ 可跨版本、跨平台                                   │ │
│  │  ├─ 支持多主（Multi-master）                           │ │
│  │  ├─ 支持冲突检测                                       │ │
│  │  └─ 复制延迟较物理复制大                               │ │
│  │                                                       │ │
│  │  适用：数据集成、ETL、版本升级、多活架构                 │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 复制模式对比

| 特性 | 物理流复制 | 逻辑复制 |
|------|------------|----------|
| **复制粒度** | 实例级 | 表级 |
| **数据一致性** | 完全一致 | 逻辑一致 |
| **DDL复制** | 自动 | 手动/触发器 |
| **跨版本** | 不支持 | 支持（有限） |
| **冲突处理** | 无冲突 | 需配置 |
| **写入延迟** | 极低 | 较低 |
| **资源消耗** | 低 | 较高 |

---

## 二、技术细节

### 2.1 物理流复制原理

```
┌─────────────────────────────────────────────────────────────┐
│                  物理流复制架构                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  WAL文件结构：                                               │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  WAL Segment (16MB默认)                               │ │
│  │  ┌────────┬────────┬────────┬────────┬─────────────┐  │ │
│  │  │Header  │Record 1│Record 2│  ...   │  Record N   │  │ │
│  │  │(24B)   │        │        │        │             │  │ │
│  │  └────────┴────────┴────────┴────────┴─────────────┘  │ │
│  │                                                       │ │
│  │  WAL Record:                                          │ │
│  │  ├─ xl_prev: 前一记录位置                             │ │
│  │  ├─ xl_xid: 事务ID                                    │ │
│  │  ├─ xl_rmid: 资源管理器ID                             │ │
│  │  ├─ xl_info: 标志位                                   │ │
│  │  ├─ xl_crc: 校验和                                    │ │
│  │  └─ data: 变更数据（页级别）                          │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  复制流程：                                                  │
│  ┌─────────────┐                  ┌─────────────┐          │
│  │   Primary   │                  │   Standby   │          │
│  │             │  1. START_REPLICATION              │          │
│  │             │←─────────────────│             │          │
│  │             │                  │             │          │
│  │  ┌───────┐  │  2. WAL Records  │  ┌───────┐  │          │
│  │  │ WAL   │──┼─────────────────→│  │ WAL   │  │          │
│  │  │Buffer │  │                  │  │ Rcv   │  │          │
│  │  └───┬───┘  │                  │  └───┬───┘  │          │
│  │      │     │                  │      │     │          │
│  │  ┌───▼───┐  │                  │  ┌───▼───┐  │          │
│  │  │ Page  │  │                  │  │ Page  │  │          │
│  │  │ Cache │  │                  │  │ Cache │  │          │
│  │  └───────┘  │                  │  └───────┘  │          │
│  │             │                  │             │          │
│  └─────────────┘                  └─────────────┘          │
│                                                            │
│  同步模式：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  async (默认)                                         │ │
│  │  ├─ 主库不等待从库确认                                 │ │
│  │  └─ 最小延迟，可能丢数据                               │ │
│  │                                                       │ │
│  │  synchronous_commit = on                              │ │
│  │  ├─ 等待本地刷盘                                       │ │
│  │  └─ 不等待从库                                         │ │
│  │                                                       │ │
│  │  synchronous_commit = remote_write                    │ │
│  │  ├─ 等待从库接收并写入OS缓存                           │ │
│  │  └─ 较低延迟，较小概率丢数据                           │ │
│  │                                                       │ │
│  │  synchronous_commit = remote_apply                    │ │
│  │  ├─ 等待从库重放完成                                   │ │
│  │  └─ 可读取，RPO=0                                      │ │
│  │                                                       │ │
│  │  synchronous_commit = on + synchronous_standby_names  │ │
│  │  ├─ 等待指定从库确认                                   │ │
│  │  └─ FIRST 1 (sync1, sync2): 任一确认                  │ │
│  │     ANY 2 (sync1, sync2, sync3): 多数确认              │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 逻辑复制原理

```
┌─────────────────────────────────────────────────────────────┐
│                  逻辑复制架构                                │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  逻辑解码流程：                                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                                                       │ │
│  │  WAL Records (物理)                                   │ │
│  │  ├─ Page 1234: 变更前镜像 (TupleData)                 │ │
│  │  └─ Page 1234: 变更后镜像 (TupleData)                 │ │
│  │            ↓                                          │ │
│  │  Output Plugin (解码插件)                             │ │
│  │  ├─ pgoutput (内置，逻辑复制默认)                     │ │
│  │  ├─ decoderbufs (protobuf格式)                        │ │
│  │  └─ wal2json (JSON格式)                               │ │
│  │            ↓                                          │ │
│  │  Logical Change Record                                │ │
│  │  {                                                    │ │
│  │    "change": [                                        │ │
│  │      {                                                │ │
│  │        "kind": "insert",                              │ │
│  │        "schema": "public",                            │ │
│  │        "table": "users",                              │ │
│  │        "columnnames": ["id", "name"],                 │ │
│  │        "columntypes": ["integer", "text"],            │ │
│  │        "columnvalues": [1, "Alice"]                   │ │
│  │      }                                                │ │
│  │    ]                                                  │ │
│  │  }                                                    │ │
│  │            ↓                                          │ │
│  │  Publication → Slot → Network → Subscription          │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  核心组件：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Publication (发布)                                   │ │
│  │  ├─ 定义要复制的表集合                                 │ │
│  │  ├─ 支持行过滤（WHERE子句）                            │ │
│  │  └─ 支持列过滤（指定列）                               │ │
│  │                                                       │ │
│  │  Replication Slot (复制槽)                            │ │
│  │  ├─ 跟踪订阅者的消费位置                               │ │
│  │  ├─ 防止WAL被过早清理                                  │ │
│  │  └─ 保证断线续传                                       │ │
│  │                                                       │ │
│  │  Subscription (订阅)                                  │ │
│  │  ├─ 连接发布者的配置                                   │ │
│  │  ├─ 应用逻辑变更到本地表                               │ │
│  │  └─ 维护复制状态                                       │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、实践指南

### 3.1 物理流复制配置

```bash
# ========== Primary节点配置 ==========

# postgresql.conf
wal_level = replica                # minimal, replica, logical
max_wal_senders = 10               # 最大复制连接数
wal_keep_size = 1GB                # 保留WAL大小
max_replication_slots = 10         # 最大复制槽数
hot_standby = on                   # 允许standby查询

# 同步复制配置（可选）
synchronous_commit = remote_apply  # 同步级别
synchronous_standby_names = 'FIRST 1 (s1, s2)'  # 同步备库

# pg_hba.conf
# 允许复制连接
host    replication     replicator    192.168.1.0/24    scram-sha-256

# 创建复制用户
CREATE ROLE replicator WITH REPLICATION LOGIN PASSWORD 'xxx';

# ========== Standby节点配置 ==========

# 使用pg_basebackup克隆
pg_basebackup -h primary -D /var/lib/postgresql/data -U replicator -P -v -R

# recovery.conf (PG12前) 或 postgresql.conf (PG12+)
# 自动生成的 standby.signal 标识为备库

# postgresql.conf
primary_conninfo = 'host=primary port=5432 user=replicator password=xxx'
recovery_target_timeline = 'latest'
hot_standby = on

# 查看复制状态
SELECT * FROM pg_stat_replication;      -- 主库查看
SELECT * FROM pg_stat_wal_receiver;     -- 备库查看
```

### 3.2 逻辑复制配置

```sql
-- ========== Publisher节点 ==========

-- 创建发布（所有表）
CREATE PUBLICATION pub_all FOR ALL TABLES;

-- 创建发布（指定表）
CREATE PUBLICATION pub_users FOR TABLE users, orders;

-- 带过滤的发布
CREATE PUBLICATION pub_active_users 
FOR TABLE users WHERE (active = true);

-- 查看发布
SELECT * FROM pg_publication;

-- 创建复制槽
SELECT * FROM pg_create_logical_replication_slot('sub1_slot', 'pgoutput');

-- ========== Subscriber节点 ==========

-- 创建订阅
CREATE SUBSCRIPTION sub1
CONNECTION 'host=publisher port=5432 dbname=mydb user=replicator password=xxx'
PUBLICATION pub_users
WITH (copy_data = true, create_slot = true, slot_name = 'sub1_slot');

-- 查看订阅状态
SELECT * FROM pg_subscription;
SELECT * FROM pg_stat_subscription;

-- 暂停/恢复复制
ALTER SUBSCRIPTION sub1 DISABLE;
ALTER SUBSCRIPTION sub1 ENABLE;
```

### 3.3 最佳实践

```
┌─────────────────────────────────────────────────────────────┐
│                    PostgreSQL复制最佳实践                    │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  物理复制最佳实践：                                          │
│  ├─ 使用专用网络（万兆网卡）                                 │ │
│  ├─ 备库开启hot_standby_feedback防止vacuum冲突               │ │
│  ├─ 配置多个备库分担读压力                                   │ │
│  ├─ 监控复制延迟 (pg_stat_replication.replay_lag)            │ │
│  └─ 设置合理的wal_keep_size防止备库落后过多                  │ │
│                                                            │
│  逻辑复制最佳实践：                                          │
│  ├─ 主键或复制标识是必须的                                   │ │
│  │   ALTER TABLE tbl REPLICA IDENTITY FULL;                │ │
│  ├─ 大事务可能卡住复制槽                                     │ │
│  ├─ 定期监控复制槽状态                                       │ │
│  └─ DDL需手动同步（逻辑复制不复制DDL）                        │ │
│                                                            │
│  高可用方案（Patroni）：                                      │ │
│  ├─ 基于DCS（etcd/ZooKeeper）的故障检测和Leader选举          │ │
│  ├─ 自动failover（<30秒）                                   │ │
│  ├─ 支持同步/异步模式动态切换                                │ │
│  └─ REST API管理集群                                        │ │
│                                                            │
│  监控指标：                                                  │ │
│  ├─ replication_lag: 复制延迟（字节/时间）                    │ │
│  ├─ pg_stat_replication.sent_lsn - replay_lsn              │ │
│  ├─ replication_slot.active: 槽是否活跃                     │ │
│  └─ replication_slot.restart_lsn: 消费位置                  │ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、常见问题

**Q1: 如何选择物理复制还是逻辑复制？**
A: 高可用、读写分离用物理复制；数据集成、选择性复制、跨版本用逻辑复制。

**Q2: 复制延迟大如何排查？**
A: 1) 检查网络带宽和延迟；2) 检查备库I/O性能；3) 检查大事务；4) 检查复制槽是否阻塞WAL清理。

**Q3: 逻辑复制主键变更如何处理？**
A: 先确保有复制标识（REPLICA IDENTITY FULL），然后使用UPDATE修改，避免DELETE+INSERT。

**Q4: 如何平滑升级PostgreSQL版本？**
A: 使用逻辑复制：1) 新版本部署为订阅者；2) 全量同步后追增量；3) 切换流量；4) 老版本退役。

---

## 五、与其他主题的关联

### 5.1 上游依赖

- [B-Tree存储引擎](./B-Tree存储引擎.md)
- [主从复制原理](./主从复制原理.md)

### 5.2 相关文档

- [逻辑复制冲突解决](./冲突解决策略.md)

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
