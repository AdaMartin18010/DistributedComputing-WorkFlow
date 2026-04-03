# MVCC多版本并发控制

## 概述

MVCC（Multi-Version Concurrency Control，多版本并发控制）是现代数据库系统中广泛使用的一种并发控制技术。它通过为每个数据项维护多个版本，使得读写操作可以并发执行而不互相阻塞，从而在保证事务隔离性的同时，大幅提升数据库的并发性能。

MVCC被广泛应用于PostgreSQL、MySQL InnoDB、Oracle、SQL Server等主流数据库系统中，是实现高并发事务处理的核心技术之一。

---

## 一、MVCC的基本概念

### 1.1 核心思想

传统并发控制使用锁机制，读操作需要获取共享锁，写操作需要获取排他锁，读写之间会相互阻塞。而MVCC通过维护数据的多个版本，使得：
- 读操作可以读取历史版本（快照），不需要等待写操作
- 写操作创建新版本，不影响正在进行的读操作
- 每个事务看到的数据版本由事务开始时的快照决定

### 1.2 基本术语

| 术语 | 说明 |
|-----|------|
| **版本链** | 同一数据项的多个版本按时间顺序组成的链表 |
| **事务ID** | 唯一标识事务的单调递增数字 |
| **ReadView** | 事务的快照视图，决定可见哪些数据版本 |
| **Undo Log** | 记录旧版本数据的日志，用于构建历史版本 |
| **快照读** | 基于ReadView的一致性读取 |
| **当前读** | 读取最新版本数据并加锁 |

---

## 二、MVCC的实现机制

### 2.1 数据行结构（MySQL InnoDB）

InnoDB的每行数据包含两个隐藏字段：
- **DB_TRX_ID**（6字节）：最后修改该记录的事务ID
- **DB_ROLL_PTR**（7字节）：回滚指针，指向Undo Log中的历史版本

示例行结构：
```
| TRX_ID | ROLL_PTR |  id  |  name  |  balance |
|  100   |  0x7f... |  1   |  Alice |   1000   |
```

Undo Log版本链：
```
当前行 (TRX_ID=100, balance=800)
    |
    v
历史版本 (TRX_ID=99, balance=1000)
    |
    v
更早版本 ...
```

### 2.2 ReadView机制

ReadView是事务的快照视图，包含以下信息：
- **creator_trx_id**：创建该ReadView的事务ID
- **m_ids**：生成ReadView时活跃的读写事务ID列表
- **min_trx_id**：m_ids中的最小值
- **max_trx_id**：生成ReadView时系统分配的下一个事务ID

**可见性判断算法**：

1. **TRX_ID == creator_trx_id**：可见（当前事务自己的修改）
2. **TRX_ID < min_trx_id**：可见（在ReadView创建前已提交）
3. **TRX_ID >= max_trx_id**：不可见（在ReadView创建后启动的事务）
4. **min_trx_id <= TRX_ID < max_trx_id**：
   - TRX_ID在m_ids中：不可见（事务未提交）
   - TRX_ID不在m_ids中：可见（事务已提交）

---

## 三、MVCC在不同隔离级别下的表现

| 隔离级别 | 实现方式 | ReadView生成时机 |
|---------|----------|----------------|
| READ UNCOMMITTED | 直接读取最新版本 | 不使用ReadView |
| READ COMMITTED | 每次查询生成新ReadView | 语句开始时 |
| REPEATABLE READ | 事务开始时生成ReadView | 事务开始时 |
| SERIALIZABLE | 锁机制 | 不使用MVCC |

### 3.1 REPEATABLE READ实现

在RR级别下，事务从开始到结束都使用同一个ReadView，保证：
- 事务内多次读取同一数据结果相同
- 不可重复读问题被解决
- MySQL InnoDB默认使用此级别

### 3.2 READ COMMITTED实现

在RC级别下，每次查询都生成新的ReadView：
- 能看到其他事务已提交的最新修改
- 会出现不可重复读
- Oracle、PostgreSQL默认使用此级别

---

## 四、MVCC的Java代码示例

### 4.1 模拟MVCC实现

```java
/**
 * MVCC模拟实现
 */
public class MVCCSimulator {
    
    // 事务ID生成器
    private final AtomicLong transactionIdGenerator = new AtomicLong(1);
    
    // 活跃事务集合
    private final Set<Long> activeTransactions = ConcurrentHashMap.newKeySet();
    
    // 数据存储（模拟数据库表）
    private final Map<String, DataRow> dataStore = new ConcurrentHashMap<>();
    
    /**
     * 数据行（包含版本链）
     */
    @Data
    public static class DataRow {
        private String key;
        private VersionChain currentVersion;
        
        public DataRow(String key, String value) {
            this.key = key;
            this.currentVersion = new VersionChain(0, value, null);
        }
    }
    
    /**
     * 版本链节点
     */
    @Data
    public static class VersionChain {
        private final long trxId;           // 创建该版本的事务ID
        private final String value;         // 数据值
        private final VersionChain prev;    // 指向前一个版本
        
        public VersionChain(long trxId, String value, VersionChain prev) {
            this.trxId = trxId;
            this.value = value;
            this.prev = prev;
        }
    }
    
    /**
     * ReadView
     */
    @Data
    public static class ReadView {
        private final long creatorTrxId;    // 创建者事务ID
        private final Set<Long> mIds;       // 活跃事务ID列表
        private final long minTrxId;        // 最小活跃事务ID
        private final long maxTrxId;        // 下一个事务ID
        
        public ReadView(long creatorTrxId, Set<Long> activeTransactions, 
                       long nextTrxId) {
            this.creatorTrxId = creatorTrxId;
            this.mIds = new HashSet<>(activeTransactions);
            this.minTrxId = mIds.isEmpty() ? nextTrxId : Collections.min(mIds);
            this.maxTrxId = nextTrxId;
        }
        
        /**
         * 判断版本是否可见
         */
        public boolean isVisible(long trxId) {
            // 1. 当前事务自己的修改总是可见
            if (trxId == creatorTrxId) {
                return true;
            }
            
            // 2. TRX_ID < min_trx_id，已提交，可见
            if (trxId < minTrxId) {
                return true;
            }
            
            // 3. TRX_ID >= max_trx_id，未来事务，不可见
            if (trxId >= maxTrxId) {
                return false;
            }
            
            // 4. 在min和max之间，检查是否在活跃列表
            return !mIds.contains(trxId);
        }
    }
    
    /**
     * 事务上下文
     */
    public class Transaction {
        private final long trxId;
        private final ReadView readView;
        private final Map<String, String> modifiedData = new HashMap<>();
        
        public Transaction() {
            this.trxId = transactionIdGenerator.getAndIncrement();
            activeTransactions.add(trxId);
            this.readView = new ReadView(trxId, activeTransactions, 
                                        transactionIdGenerator.get());
        }
        
        /**
         * 读取数据（快照读）
         */
        public String read(String key) {
            DataRow row = dataStore.get(key);
            if (row == null) {
                return null;
            }
            
            // 沿着版本链查找可见版本
            VersionChain version = row.getCurrentVersion();
            while (version != null) {
                if (readView.isVisible(version.getTrxId())) {
                    return version.getValue();
                }
                version = version.getPrev();
            }
            
            return null;
        }
        
        /**
         * 写入数据
         */
        public void write(String key, String value) {
            modifiedData.put(key, value);
        }
        
        /**
         * 提交事务
         */
        public void commit() {
            for (Map.Entry<String, String> entry : modifiedData.entrySet()) {
                String key = entry.getKey();
                String value = entry.getValue();
                
                DataRow row = dataStore.get(key);
                if (row == null) {
                    row = new DataRow(key, value);
                    dataStore.put(key, row);
                } else {
                    // 创建新版本
                    VersionChain newVersion = new VersionChain(
                        trxId, value, row.getCurrentVersion()
                    );
                    row.setCurrentVersion(newVersion);
                }
            }
            
            activeTransactions.remove(trxId);
        }
        
        /**
         * 回滚事务
         */
        public void rollback() {
            activeTransactions.remove(trxId);
        }
    }
    
    /**
     * 开始新事务
     */
    public Transaction beginTransaction() {
        return new Transaction();
    }
}
```

### 4.2 MVCC演示

```java
public class MVCCDemo {
    
    public static void main(String[] args) {
        MVCCSimulator simulator = new MVCCSimulator();
        
        // 初始数据
        MVCCSimulator.Transaction initTx = simulator.beginTransaction();
        initTx.write("account:1", "{balance: 1000}");
        initTx.commit();
        
        System.out.println("=== 初始状态 ===");
        System.out.println("account:1 = {balance: 1000}");
        
        // 场景：可重复读演示
        System.out.println("\n=== RR隔离级别演示 ===");
        
        MVCCSimulator.Transaction txA = simulator.beginTransaction();
        System.out.println("事务A开始，trxId=" + txA.trxId);
        
        String value1 = txA.read("account:1");
        System.out.println("事务A第1次读取: " + value1);
        
        // 事务B修改并提交
        MVCCSimulator.Transaction txB = simulator.beginTransaction();
        System.out.println("事务B开始，trxId=" + txB.trxId);
        txB.write("account:1", "{balance: 800}");
        txB.commit();
        System.out.println("事务B修改并提交: balance = 800");
        
        // 事务A再次读取（RR级别）
        String value2 = txA.read("account:1");
        System.out.println("事务A第2次读取: " + value2);
        System.out.println("两次读取结果相同? " + value1.equals(value2));
        System.out.println("可重复读保证！");
        
        txA.commit();
    }
}
```

---

## 五、MVCC的优缺点

### 5.1 优点

| 优点 | 说明 |
|-----|------|
| **读写不阻塞** | 读操作不需要加锁，不会阻塞写操作，反之亦然 |
| **无锁读** | 快照读不需要任何锁，性能极高 |
| **一致性非锁定读** | 可以在不加锁的情况下读取一致性快照 |
| **支持时间旅行** | 可以查询历史版本（如Flashback Query） |

### 5.2 缺点

| 缺点 | 说明 |
|-----|------|
| **存储开销** | 需要存储多个版本，增加存储空间 |
| **版本链遍历** | 长事务可能导致版本链过长，查询变慢 |
| **写放大** | 每次更新都要写入Undo Log |
| **垃圾回收** | 需要定期清理过期版本（Purge） |

### 5.3 版本清理（Purge）

MVCC需要定期清理不再需要的旧版本：
- 找出系统中最早的活跃ReadView（min_trx_id）
- TRX_ID < min_trx_id 的版本可以被清理
- 长事务会阻塞清理，导致版本积累

---

## 六、总结

MVCC是一种优雅的并发控制机制，通过维护数据的多版本实现读写分离，在保证事务隔离性的同时大幅提升并发性能。

**核心要点**：
1. 每行数据包含隐藏的事务ID和回滚指针
2. Undo Log构成版本链
3. ReadView决定可见性
4. 不同隔离级别通过ReadView生成时机区分

**最佳实践**：
- 避免长事务，防止版本积累
- 合理使用索引，减少版本链遍历
- 定期监控Purge进度
- 根据业务需求选择合适的隔离级别

---

## 参考资料

1. MySQL Internals Manual: "InnoDB Multi-Versioning"
2. PostgreSQL Documentation: "Concurrency Control"
3. "High Performance MySQL" by Baron Schwartz
4. "Transaction Processing" by Jim Gray
