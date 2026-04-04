# ACID与BASE理论

## 概述

在分布式系统和数据库领域，事务处理是确保数据一致性和可靠性的核心机制。ACID和BASE是两种截然不同的事务处理理论，分别代表了传统关系型数据库和分布式NoSQL系统的两种设计哲学。理解这两种理论对于设计高可靠、高性能的分布式系统至关重要。

---

## 一、ACID理论详解

### 1.1 ACID的定义与起源

ACID是由Jim Gray在20世纪70年代提出的数据库事务处理标准，它代表了事务的四个核心特性：

- **Atomicity（原子性）**：事务是不可分割的最小执行单位
- **Consistency（一致性）**：事务执行前后，数据库必须处于一致性状态
- **Isolation（隔离性）**：并发事务之间互不干扰
- **Durability（持久性）**：事务一旦提交，其结果就是永久性的

### 1.2 原子性（Atomicity）

#### 1.2.1 核心概念

原子性要求事务中的所有操作要么全部成功，要么全部失败回滚。这一特性通过事务日志（Transaction Log）和回滚机制实现。

```
┌─────────────────────────────────────────────────────────┐
│                      原子性示意图                         │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   开始事务 ──→ 操作A ──→ 操作B ──→ 操作C ──→ 提交事务     │
│      │                                           │      │
│      │         (全部成功，正常提交)                │      │
│      ↓                                           ↓      │
│   回滚点 ←────── 操作失败 ────────────────────── 失败    │
│      │                                                 │
│      └──→ 撤销操作C ──→ 撤销操作B ──→ 撤销操作A          │
│           (回滚到初始状态)                               │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

#### 1.2.2 实现机制

**Undo日志（回滚日志）**：

```sql
-- 事务开始前的数据状态记录到Undo日志
BEGIN TRANSACTION;

-- 假设账户A有1000元，账户B有500元
-- 执行转账操作：A向B转账200元
UPDATE accounts SET balance = 800 WHERE id = 'A';  -- 新值
UPDATE accounts SET balance = 700 WHERE id = 'B';  -- 新值

-- 如果事务失败，根据Undo日志恢复
-- Undo日志内容：
-- <T1, A, 1000>  -- 事务T1，对象A，原值1000
-- <T1, B, 500>   -- 事务T1，对象B，原值500
```

**Redo日志（重做日志）**：

```sql
-- Redo日志确保已提交事务的持久性
-- 即使系统崩溃，也能通过Redo日志恢复

-- Redo日志内容：
-- <T1, COMMIT>     -- 事务T1提交标记
-- <T1, A, 800>     -- 事务T1，对象A，新值800
-- <T1, B, 700>     -- 事务T1，对象B，新值700
```

#### 1.2.3 Java代码示例

```java
public class AtomicityDemo {

    private Connection connection;

    public void transferMoney(String fromAccount, String toAccount, double amount)
            throws SQLException {
        boolean autoCommit = connection.getAutoCommit();
        Savepoint savepoint = null;

        try {
            // 关闭自动提交，开启事务
            connection.setAutoCommit(false);
            savepoint = connection.setSavepoint("transfer_start");

            // 扣减转出账户余额
            String deductSql = "UPDATE accounts SET balance = balance - ? WHERE id = ?";
            try (PreparedStatement stmt = connection.prepareStatement(deductSql)) {
                stmt.setDouble(1, amount);
                stmt.setString(2, fromAccount);
                int affected = stmt.executeUpdate();
                if (affected != 1) {
                    throw new SQLException("转出账户不存在或余额不足");
                }
            }

            // 模拟中间操作可能出现的异常
            if (amount < 0) {
                throw new IllegalArgumentException("转账金额不能为负数");
            }

            // 增加转入账户余额
            String addSql = "UPDATE accounts SET balance = balance + ? WHERE id = ?";
            try (PreparedStatement stmt = connection.prepareStatement(addSql)) {
                stmt.setDouble(1, amount);
                stmt.setString(2, toAccount);
                int affected = stmt.executeUpdate();
                if (affected != 1) {
                    throw new SQLException("转入账户不存在");
                }
            }

            // 所有操作成功，提交事务
            connection.commit();
            System.out.println("转账成功: " + fromAccount + " → " + toAccount + ", 金额: " + amount);

        } catch (Exception e) {
            // 发生异常，回滚事务
            if (savepoint != null) {
                connection.rollback(savepoint);
            } else {
                connection.rollback();
            }
            System.err.println("转账失败，已回滚: " + e.getMessage());
            throw e;
        } finally {
            // 恢复自动提交设置
            connection.setAutoCommit(autoCommit);
        }
    }
}
```

### 1.3 一致性（Consistency）

#### 1.3.1 核心概念

一致性确保事务将数据库从一个有效状态转换到另一个有效状态，不违反任何完整性约束。这里的"一致性"与CAP定理中的"一致性"有所不同，更侧重于数据约束和业务规则。

```
┌────────────────────────────────────────────────────────────┐
│                      一致性状态转换                          │
├────────────────────────────────────────────────────────────┤
│                                                            │
│   初始状态                    中间状态（不允许）              最终状态   │
│   ┌──────────┐              ┌──────────┐               ┌──────────┐  │
│   │ A: 1000  │   ────┐      │ A: 800   │   ╳           │ A: 800   │  │
│   │ B: 500   │       │      │ B: 500   │   (无效)       │ B: 700   │  │
│   │ 总计:1500│       └──→   │ 总计:1300│               │ 总计:1500│  │
│   └──────────┘              └──────────┘               └──────────┘  │
│                                                            │
│   约束条件：                                                 │
│   1. 账户余额 >= 0                                         │
│   2. 所有账户余额总和保持不变                                  │
│                                                            │
└────────────────────────────────────────────────────────────┘
```

#### 1.3.2 约束类型

**实体完整性**：

```sql
-- 主键约束确保实体完整性
CREATE TABLE accounts (
    account_id VARCHAR(20) PRIMARY KEY,  -- 主键约束
    balance DECIMAL(18,2) NOT NULL CHECK (balance >= 0),  -- 检查约束
    customer_id VARCHAR(20) NOT NULL,
    FOREIGN KEY (customer_id) REFERENCES customers(id)  -- 外键约束
);
```

**业务规则一致性**：

```java
public class ConsistencyValidator {

    /**
     * 验证转账业务规则
     */
    public void validateTransfer(TransferRequest request) {
        // 规则1：金额必须为正数
        if (request.getAmount() <= 0) {
            throw new BusinessException("TRANSFER_AMOUNT_INVALID", "转账金额必须大于0");
        }

        // 规则2：单笔转账限额
        if (request.getAmount() > 50000) {
            throw new BusinessException("TRANSFER_LIMIT_EXCEEDED", "单笔转账不能超过5万元");
        }

        // 规则3：日累计限额检查
        double dailyTotal = getDailyTransferTotal(request.getFromAccount());
        if (dailyTotal + request.getAmount() > 200000) {
            throw new BusinessException("DAILY_LIMIT_EXCEEDED", "日累计转账不能超过20万元");
        }

        // 规则4：账户状态检查
        AccountStatus status = getAccountStatus(request.getFromAccount());
        if (status != AccountStatus.ACTIVE) {
            throw new BusinessException("ACCOUNT_NOT_ACTIVE", "账户状态异常，无法转账");
        }
    }

    /**
     * 验证数据一致性约束
     */
    public void validateDataConsistency(Connection conn) throws SQLException {
        // 检查：所有账户余额之和应等于系统总资金
        String sql = "SELECT SUM(balance) as total FROM accounts";
        try (Statement stmt = conn.createStatement();
             ResultSet rs = stmt.executeQuery(sql)) {
            if (rs.next()) {
                double totalBalance = rs.getDouble("total");
                double systemFund = getSystemTotalFund();
                if (Math.abs(totalBalance - systemFund) > 0.01) {
                    throw new ConsistencyException(
                        "数据不一致：账户总余额(" + totalBalance +
                        ") ≠ 系统总资金(" + systemFund + ")"
                    );
                }
            }
        }
    }
}
```

### 1.4 隔离性（Isolation）

#### 1.4.1 核心概念

隔离性确保并发执行的事务互不干扰。数据库通过锁机制和多版本并发控制（MVCC）实现不同程度的隔离。

```
┌─────────────────────────────────────────────────────────────┐
│                      隔离性示意图                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   事务T1                      事务T2                         │
│   ────────                    ────────                       │
│   BEGIN;                      BEGIN;                         │
│      │                           │                          │
│      │  ┌───────────────────┐    │                          │
│      ├──→│   隔离屏障         │←───┤                          │
│      │  │  (事务相互不可见)   │    │                          │
│      │  └───────────────────┘    │                          │
│      │                           │                          │
│   SELECT *                      SELECT *                    │
│   FROM accounts;                FROM accounts;              │
│      │                           │                          │
│   UPDATE                        UPDATE                      │
│   accounts...                   accounts...                 │
│      │                           │                          │
│   COMMIT;                       COMMIT;                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 1.4.2 隔离级别

| 隔离级别 | 脏读 | 不可重复读 | 幻读 |
|---------|------|-----------|------|
| READ UNCOMMITTED | ✓ | ✓ | ✓ |
| READ COMMITTED | ✗ | ✓ | ✓ |
| REPEATABLE READ | ✗ | ✗ | ✓ |
| SERIALIZABLE | ✗ | ✗ | ✗ |

```java
public class IsolationLevelDemo {

    public void demonstrateIsolationLevels() throws SQLException {
        Connection conn = dataSource.getConnection();

        // 设置不同隔离级别
        // 1. 读未提交 - 最低隔离级别，性能最好但问题最多
        conn.setTransactionIsolation(Connection.TRANSACTION_READ_UNCOMMITTED);

        // 2. 读已提交 - Oracle默认级别
        conn.setTransactionIsolation(Connection.TRANSACTION_READ_COMMITTED);

        // 3. 可重复读 - MySQL默认级别
        conn.setTransactionIsolation(Connection.TRANSACTION_REPEATABLE_READ);

        // 4. 串行化 - 最高隔离级别，性能最差但最安全
        conn.setTransactionIsolation(Connection.TRANSACTION_SERIALIZABLE);
    }

    /**
     * 可重复读示例 - 解决不可重复读问题
     */
    public void repeatableReadDemo() throws SQLException {
        Connection conn = dataSource.getConnection();
        conn.setTransactionIsolation(Connection.TRANSACTION_REPEATABLE_READ);
        conn.setAutoCommit(false);

        try {
            // 第一次查询
            double balance1 = queryBalance(conn, "account_001");
            System.out.println("第一次查询余额: " + balance1);

            // 此时其他事务修改了该账户余额并提交
            // 模拟其他事务操作...
            simulateOtherTransaction();

            // 第二次查询（在同一事务中）
            double balance2 = queryBalance(conn, "account_001");
            System.out.println("第二次查询余额: " + balance2);

            // 在REPEATABLE READ级别下，balance1 == balance2
            assert balance1 == balance2 : "可重复读保证同一事务内数据一致";

            conn.commit();
        } catch (Exception e) {
            conn.rollback();
            throw e;
        }
    }
}
```

### 1.5 持久性（Durability）

#### 1.5.1 核心概念

持久性确保一旦事务提交，其对数据库的修改就是永久性的，即使系统发生故障也不会丢失。

```
┌─────────────────────────────────────────────────────────────┐
│                      持久性保证机制                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   事务提交流程：                                              │
│                                                             │
│   1. 写入Redo日志 ─────→ 2. 刷盘(fsync) ────→ 3. 返回成功    │
│         │                      │                   │        │
│         │                      │                   │        │
│         ↓                      ↓                   ↓        │
│   ┌──────────┐           ┌──────────┐        ┌──────────┐  │
│   │ 内存缓冲区 │           │ 磁盘日志  │        │ 客户端确认 │  │
│   │ (Log Buffer)│  ────→  │ (WAL文件)│        │          │  │
│   └──────────┘           └──────────┘        └──────────┘  │
│                                                             │
│   故障恢复流程：                                              │
│                                                             │
│   系统崩溃 ──→ 重启 ──→ 读取Redo日志 ──→ 重做未落盘的操作     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 1.5.2 WAL（Write-Ahead Logging）机制

```java
public class DurabilityMechanism {

    /**
     * 模拟WAL机制
     */
    public class WriteAheadLog {
        private FileChannel logChannel;
        private ByteBuffer logBuffer;

        public void appendLog(LogEntry entry) throws IOException {
            // 1. 序列化日志记录
            byte[] data = serialize(entry);

            // 2. 写入缓冲区
            logBuffer.put(data);

            // 3. 强制刷盘（fsync）保证持久性
            if (entry.isCommit()) {
                logBuffer.flip();
                logChannel.write(logBuffer);
                logChannel.force(true);  // 强制同步到磁盘
                logBuffer.clear();
            }
        }

        /**
         * 故障恢复
         */
        public List<LogEntry> recover() throws IOException {
            List<LogEntry> entries = new ArrayList<>();
            ByteBuffer buffer = ByteBuffer.allocate(4096);

            logChannel.position(0);
            while (logChannel.read(buffer) > 0) {
                buffer.flip();
                while (buffer.hasRemaining()) {
                    LogEntry entry = deserialize(buffer);
                    entries.add(entry);
                }
                buffer.clear();
            }

            // 重做已提交但可能未落盘的事务
            return redoCommittedTransactions(entries);
        }
    }
}
```

---

## 二、BASE理论详解

### 2.1 BASE的定义与背景

BASE理论是相对于ACID而言的另一种设计哲学，主要用于分布式系统和NoSQL数据库：

- **Basically Available（基本可用）**：系统在出现故障时允许损失部分可用性
- **Soft state（软状态）**：允许系统中的数据存在中间状态
- **Eventually consistent（最终一致性）**：不保证实时一致性，但保证最终达到一致状态

### 2.2 基本可用（Basically Available）

#### 2.2.1 核心概念

分布式系统在出现故障时，允许损失部分功能或性能，但核心功能仍然可用。

```
┌─────────────────────────────────────────────────────────────┐
│                     基本可用性策略                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   正常情况：                                                 │
│   ┌─────────┐     ┌─────────┐     ┌─────────┐              │
│   │ 节点A   │←───→│ 节点B   │←───→│ 节点C   │              │
│   │ (100ms) │     │ (100ms) │     │ (100ms) │              │
│   └─────────┘     └─────────┘     └─────────┘              │
│        ↑                                            ↑       │
│        └───────────── 响应时间 < 200ms ─────────────┘       │
│                                                             │
│   故障情况（节点B不可用）：                                   │
│   ┌─────────┐     ╔═════════╗     ┌─────────┐              │
│   │ 节点A   │ ←X→ ║ 节点B   ║ ←X→ │ 节点C   │              │
│   │ (100ms) │     ║ (超时)   ║     │ (100ms) │              │
│   └─────────┘     ╚═════════╝     └─────────┘              │
│        ↑              ↓                      ↑              │
│        └──────── 降级服务 ──────────────────┘               │
│                   返回缓存数据或默认值                         │
│                   响应时间 < 50ms                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.2.2 降级策略实现

```java
@Service
public class AvailabilityService {

    @Autowired
    private RecommendationClient recommendationClient;

    @Autowired
    private CacheManager cacheManager;

    /**
     * 带降级策略的推荐服务
     */
    @HystrixCommand(
        fallbackMethod = "getFallbackRecommendations",
        commandProperties = {
            @HystrixProperty(name = "execution.isolation.thread.timeoutInMilliseconds", value = "500"),
            @HystrixProperty(name = "circuitBreaker.requestVolumeThreshold", value = "10"),
            @HystrixProperty(name = "circuitBreaker.errorThresholdPercentage", value = "50")
        }
    )
    public List<Product> getRecommendations(String userId) {
        // 正常调用推荐服务
        return recommendationClient.getRecommendations(userId);
    }

    /**
     * 降级方法 - 返回缓存或默认推荐
     */
    public List<Product> getFallbackRecommendations(String userId) {
        // 1. 尝试从本地缓存获取
        Cache cache = cacheManager.getCache("recommendations");
        List<Product> cached = cache.get(userId, List.class);
        if (cached != null) {
            return cached;
        }

        // 2. 返回默认热门推荐
        return getDefaultHotProducts();
    }

    /**
     * 超时控制示例
     */
    public ProductDetails getProductDetails(String productId) {
        try {
            // 设置2秒超时
            return CompletableFuture
                .supplyAsync(() -> fetchFromRemote(productId))
                .orTimeout(2000, TimeUnit.MILLISECONDS)
                .exceptionally(ex -> fetchFromCache(productId))
                .get();
        } catch (Exception e) {
            // 超时或异常，返回基础信息
            return ProductDetails.basic(productId);
        }
    }
}
```

### 2.3 软状态（Soft State）

#### 2.3.1 核心概念

软状态允许系统中的数据在一段时间内处于不一致的中间状态，这种状态会随着时间的推移而最终消失。

```
┌─────────────────────────────────────────────────────────────┐
│                      软状态示意                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   时间轴 ───────────────────────────────────────────────→   │
│                                                             │
│   T0: 订单创建                                               │
│   ┌─────────┐                                               │
│   │ 订单状态 │ = PENDING (待支付)                             │
│   └─────────┘                                               │
│        │                                                    │
│        ↓ 异步处理                                            │
│   T1: 库存扣减中 ←── 软状态：库存已预留但未确认扣减            │
│   ┌─────────┐    ┌─────────┐                               │
│   │ 订单状态 │    │ 库存状态 │                                │
│   │ PENDING │    │ SOFT_RESERVED │ ← 软状态                  │
│   └─────────┘    └─────────┘                               │
│        │              │                                     │
│        ↓              ↓                                     │
│   T2: 支付完成                                               │
│   ┌─────────┐    ┌─────────┐                               │
│   │ 订单状态 │    │ 库存状态 │                                │
│   │ PAID    │    │ CONFIRMED │                              │
│   └─────────┘    └─────────┘                               │
│                                                             │
│   如果支付超时：                                              │
│   T3: 订单取消                                               │
│   ┌─────────┐    ┌─────────┐                               │
│   │ 订单状态 │    │ 库存状态 │                                │
│   │ CANCELLED│   │ RELEASED │                               │
│   └─────────┘    └─────────┘                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.3.2 状态机实现

```java
public class SoftStateManager {

    /**
     * 订单状态机
     */
    public enum OrderState {
        PENDING,           // 待支付
        SOFT_RESERVED,     // 软状态：库存预留
        PAID,              // 已支付
        CONFIRMED,         // 已确认
        CANCELLED,         // 已取消
        REFUNDED           // 已退款
    }

    /**
     * 状态转换规则
     */
    private static final Map<OrderState, Set<OrderState>> TRANSITIONS = Map.of(
        OrderState.PENDING, Set.of(OrderState.SOFT_RESERVED, OrderState.CANCELLED),
        OrderState.SOFT_RESERVED, Set.of(OrderState.PAID, OrderState.CANCELLED),
        OrderState.PAID, Set.of(OrderState.CONFIRMED, OrderState.REFUNDED),
        OrderState.CONFIRMED, Set.of(OrderState.REFUNDED),
        OrderState.CANCELLED, Set.of(),  // 终态
        OrderState.REFUNDED, Set.of()    // 终态
    );

    /**
     * 创建订单（进入软状态）
     */
    public Order createOrder(OrderRequest request) {
        Order order = new Order();
        order.setId(generateOrderId());
        order.setState(OrderState.PENDING);
        order.setCreateTime(Instant.now());

        // 1. 保存订单
        orderRepository.save(order);

        // 2. 异步预留库存（进入软状态）
        inventoryService.softReserve(request.getItems())
            .thenAccept(success -> {
                if (success) {
                    transitionState(order.getId(), OrderState.SOFT_RESERVED);
                } else {
                    transitionState(order.getId(), OrderState.CANCELLED);
                }
            });

        // 3. 设置超时检查
        scheduleTimeoutCheck(order.getId(), Duration.ofMinutes(30));

        return order;
    }

    /**
     * 支付完成，确认订单
     */
    @Transactional
    public void confirmPayment(String orderId) {
        Order order = orderRepository.findById(orderId)
            .orElseThrow(() -> new OrderNotFoundException(orderId));

        // 验证当前状态
        if (order.getState() != OrderState.SOFT_RESERVED) {
            throw new InvalidStateException("订单状态无效: " + order.getState());
        }

        // 1. 更新订单状态
        order.setState(OrderState.PAID);
        orderRepository.save(order);

        // 2. 确认库存扣减
        inventoryService.confirmDeduction(orderId)
            .thenRun(() -> transitionState(orderId, OrderState.CONFIRMED));
    }

    /**
     * 定时清理软状态
     */
    @Scheduled(fixedRate = 60000)  // 每分钟执行
    public void cleanupSoftStates() {
        // 查找超时的软状态订单
        List<Order> expiredOrders = orderRepository
            .findByStateAndCreateTimeBefore(
                OrderState.SOFT_RESERVED,
                Instant.now().minus(Duration.ofMinutes(30))
            );

        for (Order order : expiredOrders) {
            // 释放库存
            inventoryService.releaseReservation(order.getId());
            // 取消订单
            transitionState(order.getId(), OrderState.CANCELLED);
        }
    }
}
```

### 2.4 最终一致性（Eventually Consistency）

#### 2.4.1 核心概念

最终一致性不保证读取操作能立即看到最新的写入，但保证在没有新的更新操作后，最终所有副本都会达到一致状态。

```
┌─────────────────────────────────────────────────────────────┐
│                    最终一致性示意                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   写入节点                    复制延迟                       │
│   ┌─────────┐   Write(X=10)   ┌─────────┐                   │
│   │ Node A  │ ──────────────→ │ Node B  │                   │
│   │ X = 10  │                 │ X = ?   │                   │
│   └─────────┘                 └─────────┘                   │
│        │                           │                        │
│        │  同步中...                 │                        │
│        │──────────────────────────→│                        │
│        │                           ↓                        │
│        │                      Read(X)                       │
│        │                      返回旧值或空                   │
│        │                           │                        │
│        ↓                           ↓                        │
│   ┌─────────┐                 ┌─────────┐                   │
│   │ X = 10  │ ←────────────── │ X = 10  │ 最终一致           │
│   └─────────┘   同步完成       └─────────┘                   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.4.2 实现模式

**1. 异步复制模式**：

```java
@Service
public class EventualConsistencyService {

    @Autowired
    private KafkaTemplate<String, OrderEvent> kafkaTemplate;

    /**
     * 订单创建 - 写入主库并异步同步
     */
    @Transactional("primaryTransactionManager")
    public Order createOrder(OrderRequest request) {
        // 1. 写入主库
        Order order = orderRepository.save(toOrder(request));

        // 2. 发送同步事件（异步）
        OrderEvent event = OrderEvent.builder()
            .type(EventType.ORDER_CREATED)
            .orderId(order.getId())
            .timestamp(Instant.now())
            .payload(toJson(order))
            .build();

        kafkaTemplate.send("order-sync-topic", order.getId(), event)
            .whenComplete((result, ex) -> {
                if (ex != null) {
                    // 记录失败，等待补偿
                    logSyncFailure(event, ex);
                }
            });

        return order;
    }

    /**
     * 消费者 - 同步到从库
     */
    @KafkaListener(topics = "order-sync-topic", groupId = "sync-consumer")
    public void syncToReplica(OrderEvent event) {
        try {
            Order order = parseOrder(event.getPayload());
            replicaOrderRepository.save(order);

            // 记录同步完成
            syncLogRepository.markSynced(event.getOrderId(), event.getTimestamp());
        } catch (Exception e) {
            // 进入死信队列，人工干预
            throw new SyncException("同步失败: " + event.getOrderId(), e);
        }
    }
}
```

**2. 读修复模式**：

```java
public class ReadRepairStrategy {

    /**
     * 带读修复的查询
     */
    public Product readWithRepair(String productId) {
        // 并行读取多个副本
        List<CompletableFuture<Product>> futures = replicas.stream()
            .map(replica -> CompletableFuture.supplyAsync(
                () -> replica.read(productId)
            ))
            .collect(Collectors.toList());

        // 等待所有响应（带超时）
        List<Product> results = futures.stream()
            .map(f -> {
                try {
                    return f.get(100, TimeUnit.MILLISECONDS);
                } catch (Exception e) {
                    return null;
                }
            })
            .filter(Objects::nonNull)
            .collect(Collectors.toList());

        if (results.isEmpty()) {
            throw new NotFoundException("Product not found: " + productId);
        }

        // 找出最新版本
        Product latest = results.stream()
            .max(Comparator.comparing(Product::getVersion))
            .orElseThrow();

        // 读修复：更新过时副本
        for (Product product : results) {
            if (product.getVersion() < latest.getVersion()) {
                asyncRepair(productId, latest);
            }
        }

        return latest;
    }
}
```

---

## 三、ACID vs BASE 对比分析

### 3.1 核心差异

```
┌─────────────────┬────────────────────────┬────────────────────────┐
│     特性        │         ACID           │         BASE           │
├─────────────────┼────────────────────────┼────────────────────────┤
│ 一致性模型      │ 强一致性               │ 最终一致性             │
│ 可用性          │ 部分可用（分区时需妥协）│ 基本可用               │
│ 性能            │ 相对较低（锁、同步开销）│ 较高（异步、无锁）      │
│ 扩展性          │ 垂直扩展为主           │ 水平扩展友好           │
│ 故障恢复        │ 复杂（2PC/3PC等）      │ 简单（异步补偿）        │
│ 数据模型        │ 关系型为主             │ 多样化（KV/文档/列式）  │
│ 典型应用        │ 银行转账、库存扣减      │ 社交Feed、日志记录      │
└─────────────────┴────────────────────────┴────────────────────────┘
```

### 3.2 适用场景选择

**选择ACID的场景**：

- 金融交易系统（银行、证券、支付）
- 库存管理系统（超卖零容忍）
- 订单核心系统（状态转换严格）
- 配置管理系统（一致性优先）

**选择BASE的场景**：

- 社交网络（Feed流、点赞数）
- 日志收集系统（允许少量丢失）
- 商品展示（库存展示可短暂延迟）
- 用户行为追踪（高吞吐优先）

### 3.3 混合架构实践

```
┌─────────────────────────────────────────────────────────────┐
│                    混合架构示例                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────────────────────────────────────────────┐  │
│   │                    应用层                            │  │
│   └─────────────────────────────────────────────────────┘  │
│                            │                                │
│          ┌─────────────────┼─────────────────┐              │
│          ↓                 ↓                 ↓              │
│   ┌────────────┐    ┌────────────┐    ┌────────────┐       │
│   │  订单服务   │    │  商品服务   │    │  用户服务   │       │
│   │  (ACID)    │    │  (BASE)    │    │  (BASE)    │       │
│   └─────┬──────┘    └─────┬──────┘    └─────┬──────┘       │
│         │                 │                 │               │
│   ┌─────▼──────┐    ┌─────▼──────┐    ┌─────▼──────┐       │
│   │ MySQL Cluster│   │  Cassandra │    │   Redis    │       │
│   │  强一致性   │    │  最终一致  │    │  缓存层    │       │
│   └────────────┘    └────────────┘    └────────────┘       │
│                                                             │
│   核心交易数据使用ACID保证，非核心数据使用BASE提升性能          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 四、总结

ACID和BASE代表了两种不同的事务处理哲学：

1. **ACID** 追求强一致性和数据可靠性，适合对数据准确性要求极高的场景。通过锁机制、日志和两阶段提交等技术实现，但会牺牲一定的可用性和性能。

2. **BASE** 追求高可用性和水平扩展能力，适合大规模分布式系统。通过异步复制、最终一致性和降级策略实现，允许短暂的不一致以换取系统弹性。

在现代分布式系统设计中，往往需要根据业务特点灵活运用这两种理论。核心数据使用ACID保证可靠性，非核心数据使用BASE提升性能和可用性，这才是最务实的架构选择。

---

## 参考资料

1. Jim Gray, "The Transaction Concept: Virtues and Limitations", 1981
2. Eric Brewer, "CAP Twelve Years Later", 2012
3. Daniel J. Abadi, "Consistency Tradeoffs in Modern Distributed Database System Design", 2012
4. Martin Kleppmann, "Designing Data-Intensive Applications", O'Reilly, 2017


---

## 相关主题

- [事务隔离级别详解](./事务隔离级别详解.md)
- [分布式事务选型指南](../分布式事务选型指南.md)
- [CAP定理](../../02-theory/distributed-systems/CAP定理专题文档.md)

## 参考资源

- [ACID vs BASE](https://www.mongodb.com/resources/basics/databases/acid-vs-base)
