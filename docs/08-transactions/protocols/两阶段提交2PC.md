# 两阶段提交 2PC（Two-Phase Commit）

## 概述

两阶段提交（Two-Phase Commit，2PC）是一种经典的分布式事务协议，用于确保分布式系统中多个节点上的操作要么全部成功，要么全部失败。2PC由Jim Gray于1978年提出，是实现分布式原子提交的基础算法，广泛应用于数据库分布式事务、消息队列事务等场景。

---

## 一、2PC的基本概念

### 1.1 参与角色

```
┌─────────────────────────────────────────────────────────────┐
│                    2PC参与角色架构                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                      ┌─────────────┐                        │
│                      │   协调者    │                        │
│                      │ Coordinator │                        │
│                      │             │                        │
│                      │ - 事务管理   │                        │
│                      │ - 决策制定   │                        │
│                      │ - 状态同步   │                        │
│                      └──────┬──────┘                        │
│                             │                               │
│           ┌─────────────────┼─────────────────┐             │
│           │                 │                 │             │
│           ▼                 ▼                 ▼             │
│      ┌─────────┐      ┌─────────┐      ┌─────────┐         │
│      │ 参与者A │      │ 参与者B │      │ 参与者C │         │
│      │         │      │         │      │         │         │
│      │ - 本地事务│      │ - 本地事务│      │ - 本地事务│         │
│      │ - 资源管理│      │ - 资源管理│      │ - 资源管理│         │
│      │ - 投票   │      │ - 投票   │      │ - 投票   │         │
│      └─────────┘      └─────────┘      └─────────┘         │
│                                                             │
│   协调者（Coordinator）：负责事务的协调和决策                │
│   参与者（Participants）：执行本地事务并响应协调者指令        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 核心思想

2PC将事务提交过程分为两个阶段：

1. **投票阶段（Vote Phase / Prepare Phase）**：协调者询问所有参与者是否可以提交事务
2. **提交阶段（Commit Phase）**：根据参与者的投票结果，协调者决定提交或回滚

---

## 二、2PC详细流程

### 2.1 正常提交流程

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        2PC正常提交流程                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   协调者                    参与者A                    参与者B           │
│     │                         │                         │              │
│     │──── 1. Prepare ────────→│                         │              │
│     │    (询问是否可以提交)     │                         │              │
│     │                         │                         │              │
│     │──── 1. Prepare ───────────────────────────────────→│              │
│     │                         │                         │              │
│     │←─── 2. Yes/No ─────────│                         │              │
│     │    (本地事务执行成功)    │                         │              │
│     │                         │                         │              │
│     │←──────────────────────── 2. Yes/No ────────────────│              │
│     │                                                   (本地事务执行成功)│
│     │                         │                         │              │
│     │    [所有参与者返回Yes]   │                         │              │
│     │         │               │                         │              │
│     ▼         ▼               ▼                         ▼              │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                     阶段1：投票阶段结束                          │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│     │                         │                         │              │
│     │──── 3. Commit ─────────→│                         │              │
│     │    (正式提交事务)        │                         │              │
│     │                         │                         │              │
│     │──── 3. Commit ────────────────────────────────────→│              │
│     │                         │                         │              │
│     │←─── 4. ACK ────────────│                         │              │
│     │    (提交完成确认)        │                         │              │
│     │                         │                         │              │
│     │←──────────────────────── 4. ACK ──────────────────│              │
│     │                                                   (提交完成确认)  │
│     │                         │                         │              │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                     阶段2：提交阶段结束                          │  │
│   │                     事务完成                                    │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 回滚流程

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        2PC回滚流程                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   协调者                    参与者A                    参与者B           │
│     │                         │                         │              │
│     │──── 1. Prepare ────────→│                         │              │
│     │                         │                         │              │
│     │──── 1. Prepare ───────────────────────────────────→│              │
│     │                         │                         │              │
│     │←─── 2. Yes ────────────│                         │              │
│     │    (本地事务执行成功)    │                         │              │
│     │                         │                         │              │
│     │←──────────────────────── 2. No ───────────────────│              │
│     │                                                   (本地事务失败)  │
│     │                         │                         │              │
│     │    [至少一个参与者返回No] │                         │              │
│     │         │               │                         │              │
│     ▼         ▼               ▼                         ▼              │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                     阶段1：投票阶段                              │  │
│   │                     发现无法提交                                 │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│     │                         │                         │              │
│     │──── 3. Rollback ───────→│                         │              │
│     │    (回滚事务)            │                         │              │
│     │                         │                         │              │
│     │──── 3. Rollback ──────────────────────────────────→│              │
│     │                         │                         │              │
│     │←─── 4. ACK ────────────│                         │              │
│     │    (回滚完成确认)        │                         │              │
│     │                         │                         │              │
│     │←──────────────────────── 4. ACK ──────────────────│              │
│     │                                                   (回滚完成确认)  │
│     │                         │                         │              │
│   ┌─────────────────────────────────────────────────────────────────┐  │
│   │                     阶段2：回滚阶段结束                          │  │
│   │                     事务回滚完成                                 │  │
│   └─────────────────────────────────────────────────────────────────┘  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.3 状态转换图

```
┌─────────────────────────────────────────────────────────────┐
│                  2PC协调者状态转换图                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                         初始状态                             │
│                            │                                │
│                            ▼                                │
│                    ┌───────────────┐                        │
│                    │   WAITING    │  ← 发送Prepare，等待投票 │
│                    │   (等待中)    │                        │
│                    └───────┬───────┘                        │
│                            │                                │
│           ┌────────────────┼────────────────┐              │
│           │                │                │               │
│           ▼                ▼                ▼               │
│    ┌───────────┐    ┌───────────┐    ┌───────────┐         │
│    │ PREPARING │    │ PREPARING │    │ PREPARING │         │
│    │  (部分Yes) │    │  (全部Yes) │    │  (收到No) │         │
│    └─────┬─────┘    └─────┬─────┘    └─────┬─────┘         │
│          │                │                │                │
│          │                ▼                ▼                │
│          │         ┌───────────┐    ┌───────────┐          │
│          │         │ COMMITTING│    │ ABORTING  │          │
│          │         │  (提交中) │    │  (回滚中) │          │
│          │         └─────┬─────┘    └─────┬─────┘          │
│          │               │                │                 │
│          │               ▼                ▼                 │
│          │         ┌───────────┐    ┌───────────┐          │
│          └────────→│ COMMITTED │    │  ABORTED  │          │
│                    │  (已提交) │    │  (已回滚) │          │
│                    └───────────┘    └───────────┘          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、2PC的Java实现

### 3.1 基础架构实现

```java
/**
 * 2PC协调者接口
 */
public interface TwoPhaseCommitCoordinator {

    /**
     * 开启一个新事务
     */
    TransactionContext beginTransaction() throws XAException;

    /**
     * 执行两阶段提交
     */
    boolean commit(TransactionContext context) throws XAException;

    /**
     * 回滚事务
     */
    void rollback(TransactionContext context) throws XAException;
}

/**
 * 参与者接口
 */
public interface TwoPhaseCommitParticipant {

    /**
     * 准备阶段：执行本地事务，但不提交
     * @return true表示可以提交，false表示需要回滚
     */
    boolean prepare(Xid xid) throws XAException;

    /**
     * 提交阶段：正式提交本地事务
     */
    void commit(Xid xid, boolean onePhase) throws XAException;

    /**
     * 回滚本地事务
     */
    void rollback(Xid xid) throws XAException;

    /**
     * 忘记事务（清理资源）
     */
    void forget(Xid xid) throws XAException;
}
```

### 3.2 完整实现代码

```java
import javax.transaction.xa.XAException;
import javax.transaction.xa.XAResource;
import javax.transaction.xa.Xid;
import java.sql.Connection;
import java.sql.SQLException;
import java.util.*;
import java.util.concurrent.*;
import java.util.logging.Logger;

/**
 * 2PC协调者实现
 */
public class TwoPhaseCommitCoordinatorImpl implements TwoPhaseCommitCoordinator {

    private static final Logger logger = Logger.getLogger(TwoPhaseCommitCoordinatorImpl.class.getName());

    private final List<TwoPhaseCommitParticipant> participants;
    private final ExecutorService executor;
    private final long timeoutMillis;

    public TwoPhaseCommitCoordinatorImpl(long timeoutMillis) {
        this.participants = new ArrayList<>();
        this.executor = Executors.newCachedThreadPool();
        this.timeoutMillis = timeoutMillis;
    }

    public void registerParticipant(TwoPhaseCommitParticipant participant) {
        participants.add(participant);
    }

    @Override
    public TransactionContext beginTransaction() {
        String transactionId = UUID.randomUUID().toString();
        Xid xid = new CustomXid(0, transactionId.getBytes(),
                                UUID.randomUUID().toString().getBytes());
        return new TransactionContext(xid, new ArrayList<>());
    }

    @Override
    public boolean commit(TransactionContext context) throws XAException {
        Xid xid = context.getXid();
        logger.info("Starting 2PC commit for transaction: " + xid);

        // ========== 阶段1：投票阶段 ==========
        logger.info("Phase 1: Prepare phase");
        List<TwoPhaseCommitParticipant> preparedParticipants = new ArrayList<>();
        List<Future<Boolean>> prepareFutures = new ArrayList<>();

        // 并发发送Prepare请求
        for (TwoPhaseCommitParticipant participant : participants) {
            Future<Boolean> future = executor.submit(() -> {
                try {
                    return participant.prepare(xid);
                } catch (XAException e) {
                    logger.warning("Prepare failed for participant: " + e.getMessage());
                    return false;
                }
            });
            prepareFutures.add(future);
        }

        // 收集投票结果
        boolean allPrepared = true;
        for (int i = 0; i < prepareFutures.size(); i++) {
            try {
                Boolean result = prepareFutures.get(i).get(timeoutMillis, TimeUnit.MILLISECONDS);
                if (result) {
                    preparedParticipants.add(participants.get(i));
                } else {
                    allPrepared = false;
                    logger.warning("Participant " + i + " voted NO");
                }
            } catch (Exception e) {
                allPrepared = false;
                logger.severe("Prepare timeout or error: " + e.getMessage());
            }
        }

        // ========== 阶段2：提交/回滚阶段 ==========
        if (allPrepared && preparedParticipants.size() == participants.size()) {
            // 所有参与者都同意，执行提交
            logger.info("Phase 2: All participants prepared, committing");
            return executeCommit(xid, preparedParticipants);
        } else {
            // 至少一个参与者不同意或失败，执行回滚
            logger.warning("Phase 2: Some participants failed, rolling back");
            executeRollback(xid, preparedParticipants);
            return false;
        }
    }

    private boolean executeCommit(Xid xid, List<TwoPhaseCommitParticipant> participants) {
        List<Future<Void>> commitFutures = new ArrayList<>();

        for (TwoPhaseCommitParticipant participant : participants) {
            Future<Void> future = executor.submit(() -> {
                try {
                    participant.commit(xid, false);
                    logger.info("Participant committed: " + participant);
                } catch (XAException e) {
                    // 提交失败，记录日志，需要人工干预
                    logger.severe("Commit failed for participant: " + e.getMessage());
                    // TODO: 记录到事务日志，启动恢复流程
                }
                return null;
            });
            commitFutures.add(future);
        }

        // 等待所有提交完成
        for (Future<Void> future : commitFutures) {
            try {
                future.get(timeoutMillis, TimeUnit.MILLISECONDS);
            } catch (Exception e) {
                logger.severe("Commit timeout: " + e.getMessage());
            }
        }

        return true;
    }

    private void executeRollback(Xid xid, List<TwoPhaseCommitParticipant> participants) {
        // 回滚所有已准备的参与者
        for (TwoPhaseCommitParticipant participant : participants) {
            executor.submit(() -> {
                try {
                    participant.rollback(xid);
                    logger.info("Participant rolled back: " + participant);
                } catch (XAException e) {
                    logger.severe("Rollback failed: " + e.getMessage());
                    // TODO: 记录到事务日志，启动恢复流程
                }
                return null;
            });
        }
    }

    @Override
    public void rollback(TransactionContext context) throws XAException {
        executeRollback(context.getXid(), participants);
    }

    public void shutdown() {
        executor.shutdown();
    }
}

/**
 * 数据库参与者实现
 */
public class DatabaseParticipant implements TwoPhaseCommitParticipant {

    private final DataSource dataSource;
    private final Map<Xid, Connection> connectionMap;

    public DatabaseParticipant(DataSource dataSource) {
        this.dataSource = dataSource;
        this.connectionMap = new ConcurrentHashMap<>();
    }

    @Override
    public boolean prepare(Xid xid) throws XAException {
        try {
            Connection conn = dataSource.getConnection();
            conn.setAutoCommit(false);
            connectionMap.put(xid, conn);

            // 执行本地事务操作（这里省略具体业务逻辑）
            // executeBusinessLogic(conn);

            // 准备完成，返回true
            return true;
        } catch (SQLException e) {
            throw new XAException(XAException.XAER_RMERR);
        }
    }

    @Override
    public void commit(Xid xid, boolean onePhase) throws XAException {
        Connection conn = connectionMap.remove(xid);
        if (conn != null) {
            try {
                conn.commit();
                conn.close();
            } catch (SQLException e) {
                throw new XAException(XAException.XAER_RMERR);
            }
        }
    }

    @Override
    public void rollback(Xid xid) throws XAException {
        Connection conn = connectionMap.remove(xid);
        if (conn != null) {
            try {
                conn.rollback();
                conn.close();
            } catch (SQLException e) {
                throw new XAException(XAException.XAER_RMERR);
            }
        }
    }

    @Override
    public void forget(Xid xid) throws XAException {
        connectionMap.remove(xid);
    }
}
```

### 3.3 使用示例

```java
public class TwoPhaseCommitExample {

    public void distributedTransfer() {
        // 创建协调者
        TwoPhaseCommitCoordinatorImpl coordinator =
            new TwoPhaseCommitCoordinatorImpl(30000);  // 30秒超时

        // 创建参与者（模拟跨库转账）
        DatabaseParticipant bankA = new DatabaseParticipant(dataSourceA);
        DatabaseParticipant bankB = new DatabaseParticipant(dataSourceB);

        coordinator.registerParticipant(bankA);
        coordinator.registerParticipant(bankB);

        // 开始事务
        TransactionContext tx = coordinator.beginTransaction();

        try {
            // 执行业务操作（在prepare阶段完成）
            boolean success = coordinator.commit(tx);

            if (success) {
                System.out.println("分布式事务提交成功");
            } else {
                System.out.println("分布式事务回滚");
            }
        } catch (XAException e) {
            System.err.println("事务异常: " + e.getMessage());
            try {
                coordinator.rollback(tx);
            } catch (XAException re) {
                System.err.println("回滚也失败了: " + re.getMessage());
            }
        } finally {
            coordinator.shutdown();
        }
    }
}
```

---

## 四、2PC的故障恢复

### 4.1 故障场景分析

```
┌─────────────────────────────────────────────────────────────┐
│                    2PC可能的故障点                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   故障点1: 协调者宕机（投票阶段）                             │
│   ┌─────────┐         ┌─────────┐                          │
│   │ 协调者  │    X    │ 参与者  │                          │
│   │ 宕机    │ ←──────→│ 等待    │                          │
│   └─────────┘         └─────────┘                          │
│        参与者等待超时后回滚本地事务                          │
│                                                             │
│   故障点2: 协调者宕机（提交阶段）                             │
│   ┌─────────┐         ┌─────────┐                          │
│   │ 协调者  │    X    │ 参与者  │                          │
│   │ 宕机    │ ←──────→│ 已准备  │                          │
│   └─────────┘         │ 等待指令 │                          │
│                       └─────────┘                          │
│        参与者进入"不确定"状态，阻塞等待                       │
│        需要协调者恢复或使用超时机制                           │
│                                                             │
│   故障点3: 参与者宕机                                        │
│   ┌─────────┐         ┌─────────┐                          │
│   │ 协调者  │ ───────→│ 参与者  │                          │
│   │         │    X    │ 宕机    │                          │
│   └─────────┘         └─────────┘                          │
│        协调者等待超时后决定回滚整个事务                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 恢复机制实现

```java
/**
 * 2PC事务日志管理器
 */
public class TransactionLogManager {

    private final Map<Xid, TransactionLog> logStore;
    private final File logFile;

    public enum TransactionState {
        STARTED,        // 事务开始
        PREPARING,      // 准备阶段
        PREPARED,       // 所有参与者已准备
        COMMITTING,     // 提交阶段
        COMMITTED,      // 已提交
        ABORTING,       // 回滚阶段
        ABORTED         // 已回滚
    }

    @Data
    public static class TransactionLog {
        private Xid xid;
        private TransactionState state;
        private List<String> participants;
        private long timestamp;
        private Map<String, Boolean> participantVotes;
    }

    /**
     * 记录事务状态
     */
    public void logTransactionState(Xid xid, TransactionState state,
                                    List<String> participants) {
        TransactionLog log = new TransactionLog();
        log.setXid(xid);
        log.setState(state);
        log.setParticipants(participants);
        log.setTimestamp(System.currentTimeMillis());

        logStore.put(xid, log);
        persistLog(log);  // 持久化到磁盘
    }

    /**
     * 恢复未完成的事务
     */
    public void recoverUnfinishedTransactions(
            TwoPhaseCommitCoordinator coordinator) {

        List<TransactionLog> unfinishedLogs = logStore.values().stream()
            .filter(log -> log.getState() != TransactionState.COMMITTED
                      && log.getState() != TransactionState.ABORTED)
            .collect(Collectors.toList());

        for (TransactionLog log : unfinishedLogs) {
            recoverTransaction(log, coordinator);
        }
    }

    private void recoverTransaction(TransactionLog log,
                                    TwoPhaseCommitCoordinator coordinator) {
        switch (log.getState()) {
            case STARTED:
            case PREPARING:
                // 事务尚未完成准备阶段，直接回滚
                coordinator.rollback(new TransactionContext(log.getXid(), null));
                break;

            case PREPARED:
                // 所有参与者已准备，但协调者宕机
                // 需要查询参与者状态决定提交或回滚
                checkParticipantsAndDecide(log, coordinator);
                break;

            case COMMITTING:
                // 已经开始提交，继续完成提交
                coordinator.commit(new TransactionContext(log.getXid(), null));
                break;

            case ABORTING:
                // 已经开始回滚，继续完成回滚
                coordinator.rollback(new TransactionContext(log.getXid(), null));
                break;
        }
    }
}
```

---

## 五、2PC的优缺点分析

### 5.1 优点

| 优点 | 说明 |
|-----|------|
| **强一致性** | 保证分布式事务的原子性，要么全提交，要么全回滚 |
| **实现简单** | 概念清晰，只有两个阶段，容易理解和实现 |
| **广泛应用** | 主流数据库（MySQL、Oracle、PostgreSQL）都支持XA/2PC |
| **标准化** | XA协议是工业标准，跨平台兼容性好 |

### 5.2 缺点

| 缺点 | 说明 |
|-----|------|
| **同步阻塞** | 参与者需要锁定资源等待协调者指令，性能开销大 |
| **单点故障** | 协调者宕机可能导致参与者长时间阻塞 |
| **数据不一致风险** | 协调者在Commit后宕机，部分参与者可能未收到指令 |
| **性能较低** | 两次网络往返，事务执行时间较长 |
| **脑裂问题** | 网络分区时可能出现部分提交、部分回滚的情况 |

### 5.3 同步阻塞问题详解

```
┌─────────────────────────────────────────────────────────────┐
│                   2PC同步阻塞问题                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   时间 ───────────────────────────────────────────────→    │
│                                                             │
│   事务A                      事务B                          │
│   ─────                      ─────                          │
│   BEGIN;                                                    │
│   UPDATE stock                                              │
│   SET count = 90                                            │
│   WHERE id = 'P001';  ────→  锁定记录P001                   │
│                              (排他锁)                        │
│   Prepare...                                                │
│     │                          │                            │
│     │ 等待协调者指令...         │                            │
│     │                          │                            │
│     │                          ▼                            │
│     │                       BEGIN;                          │
│     │                       SELECT count                    │
│     │                       FROM stock                      │
│     │                       WHERE id = 'P001';              │
│     │                       阻塞等待！                       │
│     │                          │                            │
│     ▼                          ▼                            │
│   Commit                     继续阻塞                       │
│     │                          │                            │
│     ▼                          ▼                            │
│   释放锁                     获取锁，继续执行                 │
│                                                             │
│   问题：事务A在Prepare到Commit期间一直持有锁，               │
│         阻塞其他事务访问相同数据                              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 六、2PC的适用场景

### 6.1 适用场景

1. **强一致性要求**：金融交易、库存扣减等不能容忍数据不一致的场景
2. **短事务**：执行时间短的分布式操作，减少阻塞时间
3. **同构系统**：参与者使用相同的数据库类型，便于协调
4. **低并发场景**：并发量不高，可以承受同步阻塞的开销

### 6.2 不适用场景

1. **高并发系统**：同步阻塞会严重影响吞吐量
2. **长事务**：持有锁时间过长，导致系统性能急剧下降
3. **异构系统**：多种不同类型的存储系统，难以统一协调
4. **跨公网场景**：网络延迟高，两阶段通信成本大

---

## 七、总结

两阶段提交（2PC）是实现分布式事务的经典协议，它通过投票和提交两个阶段保证了分布式环境下的原子性。虽然2PC存在同步阻塞、单点故障等缺陷，但其简单可靠的特性使其在分布式事务领域有着广泛的应用。

在实际应用中，需要根据业务场景权衡是否使用2PC：

- 对一致性要求极高的金融场景，2PC仍然是可靠的选择
- 对性能要求高的互联网应用，可以考虑Saga、TCC等最终一致性方案
- 现代分布式数据库（如TiDB、CockroachDB）通过改进的共识算法（如Raft）优化了分布式事务的实现

理解2PC的原理和限制，对于设计高可靠的分布式系统具有重要意义。

---

## 参考资料

1. Jim Gray, "Notes on Data Base Operating Systems", 1978
2. Mohan C. et al., "Transaction Processing: Concepts and Techniques", 1992
3. X/Open CAE Specification, "Distributed Transaction Processing: The XA Specification", 1991
4. "Designing Data-Intensive Applications" by Martin Kleppmann, Chapter 9


---

## 相关主题

- [三阶段提交3PC](./三阶段提交3PC.md)
- [Saga模式详解](./Saga模式详解.md)
- [分布式事务选型指南](../分布式事务选型指南.md)

## 参考资源

- [2PC协议维基](https://en.wikipedia.org/wiki/Two-phase_commit_protocol)
