# TCC事务模式详解

## 概述

TCC（Try-Confirm-Cancel）是一种柔性分布式事务解决方案，由Pat Helland在2007年提出。它将每个业务操作拆分为三个阶段：Try（预留资源）、Confirm（确认执行）和Cancel（取消回滚）。TCC模式在保留最终一致性的同时，通过业务层面的资源预留和补偿机制，提供了比Saga更精细的事务控制能力。

TCC模式在电商、金融等高并发分布式系统中得到了广泛应用，是目前主流的分布式事务解决方案之一。

---

## 一、TCC的核心概念

### 1.1 三阶段定义

```
┌─────────────────────────────────────────────────────────────┐
│                    TCC三阶段说明                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌─────────────┐    ┌─────────────┐    ┌─────────────┐    │
│   │    Try      │ → │   Confirm   │ → │   Cancel    │    │
│   │   (预留)    │    │   (确认)    │    │   (取消)    │    │
│   └─────────────┘    └─────────────┘    └─────────────┘    │
│                                                             │
│   Try阶段：                                                  │
│   - 完成业务检查                                             │
│   - 预留业务资源                                             │
│   - 执行业务逻辑（但不提交）                                  │
│                                                             │
│   Confirm阶段：                                              │
│   - 正式执行业务                                             │
│   - 使用Try阶段预留的资源                                    │
│   - 操作幂等，可能重试                                       │
│                                                             │
│   Cancel阶段：                                               │
│   - 释放Try阶段预留的资源                                    │
│   - 执行业务回滚                                             │
│   - 操作幂等，可能重试                                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 执行流程

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        TCC正常执行流程                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   协调者                    服务A                        服务B           │
│     │                         │                         │              │
│     │    ╔═══════════════════════════════════════════════════════╗    │
│     │    ║                   Try 阶段                           ║    │
│     │    ╚═══════════════════════════════════════════════════════╝    │
│     │                         │                         │              │
│     │──── Try(A) ─────────────→│                         │              │
│     │    预留资源A              │ 预留资源                │              │
│     │                         │ (如：冻结金额)           │              │
│     │←─── OK ─────────────────│                         │              │
│     │                         │                         │              │
│     │──── Try(B) ────────────────────────────────────────→│              │
│     │                         │                         │ 预留资源      │
│     │                         │                         │ (如：预占库存)│
│     │←──────────────────────── OK ────────────────────────│              │
│     │                                                   (都成功)       │
│     │                         │                         │              │
│     │    ╔═══════════════════════════════════════════════════════╗    │
│     │    ║                 Confirm 阶段                         ║    │
│     │    ╚═══════════════════════════════════════════════════════╝    │
│     │                         │                         │              │
│     │──── Confirm(A) ─────────→│                         │              │
│     │    确认执行               │ 使用预留资源            │              │
│     │                         │ 正式扣减金额             │              │
│     │←─── OK ─────────────────│                         │              │
│     │                         │                         │              │
│     │──── Confirm(B) ────────────────────────────────────→│              │
│     │                         │                         │ 使用预留资源  │
│     │                         │                         │ 正式扣减库存  │
│     │←──────────────────────── OK ────────────────────────│              │
│     │                                                   (都成功)       │
│     │                         │                         │              │
│   完成                          完成                      完成          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        TCC回滚流程                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   协调者                    服务A                        服务B           │
│     │                         │                         │              │
│     │──── Try(A) ─────────────→│                         │              │
│     │                         │ 预留资源A成功            │              │
│     │←─── OK ─────────────────│                         │              │
│     │                         │                         │              │
│     │──── Try(B) ────────────────────────────────────────→│              │
│     │                         │                         │ 预留资源B失败 │
│     │←──────────────────────── FAIL ─────────────────────│              │
│     │                                                   (服务B失败)     │
│     │                         │                         │              │
│     │    ╔═══════════════════════════════════════════════════════╗    │
│     │    ║                  Cancel 阶段                         ║    │
│     │    ╚═══════════════════════════════════════════════════════╝    │
│     │                         │                         │              │
│     │──── Cancel(A) ──────────→│                         │              │
│     │    释放资源               │ 释放预留资源A           │              │
│     │                         │ 解冻金额                 │              │
│     │←─── OK ─────────────────│                         │              │
│     │                         │                         │              │
│   回滚完成                       回滚完成                   (无需回滚)   │
│                                                                         │
│   注意：Cancel阶段按照Try成功的逆序执行                                  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 二、TCC的设计要点

### 2.1 业务模型设计

```
┌─────────────────────────────────────────────────────────────┐
│                 TCC业务模型示例                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   示例：账户余额扣减                                          │
│                                                             │
│   原模型（非TCC）：                                           │
│   ┌─────────────┐                                           │
│   │ account     │                                           │
│   │─────────────│                                           │
│   │ id          │                                           │
│   │ balance     │ ← 直接扣减                                 │
│   │ ...         │                                           │
│   └─────────────┘                                           │
│                                                             │
│   TCC模型：                                                   │
│   ┌─────────────┐    ┌─────────────┐                       │
│   │   account   │    │ frozen_record│                       │
│   │─────────────│    │─────────────│                       │
│   │ id          │    │ id          │                       │
│   │ balance     │    │ account_id  │ ← 关联账户             │
│   │             │    │ amount      │ ← 冻结金额             │
│   │             │    │ status      │ ← FROZEN/CONFIRMED/    │
│   │             │    │             │    CANCELLED           │
│   │             │    │ create_time │                       │
│   └─────────────┘    └─────────────┘                       │
│                                                             │
│   Try:   INSERT frozen_record + UPDATE account SET          │
│          balance = balance - amount                          │
│                                                             │
│   Confirm: UPDATE frozen_record SET status = CONFIRMED      │
│                                                             │
│   Cancel: UPDATE account SET balance = balance + amount     │
│           DELETE/UPDATE frozen_record                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 状态机设计

```
┌─────────────────────────────────────────────────────────────┐
│                   TCC事务状态机                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                         初始状态                             │
│                            │                                │
│                            ▼                                │
│                    ┌───────────────┐                        │
│                    │  TRYING       │                        │
│                    │  Try阶段执行中 │                        │
│                    └───────┬───────┘                        │
│                            │                                │
│           ┌────────────────┼────────────────┐              │
│           │                │                │               │
│           ▼                ▼                ▼               │
│    ┌───────────┐    ┌───────────┐    ┌───────────┐         │
│    │ TRY_FAILED│    │ TRY_SUCCESS│    │ TRY_TIMEOUT│         │
│    │ Try失败    │    │ Try成功    │    │ Try超时    │         │
│    └─────┬─────┘    └─────┬─────┘    └─────┬─────┘         │
│          │                │                │                │
│          ▼                ▼                ▼                │
│    ┌───────────┐    ┌───────────┐    ┌───────────┐         │
│    │ CANCELLING│    │ CONFIRMING│    │ CANCELLING│         │
│    │ Cancel执行 │    │ Confirm执行│    │ Cancel执行 │         │
│    └─────┬─────┘    └─────┬─────┘    └─────┬─────┘         │
│          │                │                │                │
│          ▼                ▼                ▼                │
│    ┌───────────┐    ┌───────────┐    ┌───────────┐         │
│    │ CANCELLED │    │ CONFIRMED │    │ CANCELLED │         │
│    │ 已取消     │    │ 已确认     │    │ 已取消     │         │
│    └───────────┘    └───────────┘    └───────────┘         │
│                                                             │
│   注意：                                                      │
│   - CONFIRMING失败会重试                                     │
│   - CANCELLING失败会重试                                     │
│   - 需要持久化事务日志支持恢复                                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、TCC的Java实现

### 3.1 基础接口定义

```java
/**
 * TCC参与者接口
 */
public interface TCCParticipant {

    /**
     * Try阶段：预留资源
     * @param context 事务上下文
     * @return 是否成功
     */
    boolean tryReserve(TransactionContext context);

    /**
     * Confirm阶段：确认执行
     * @param context 事务上下文
     * @return 是否成功
     */
    boolean confirm(TransactionContext context);

    /**
     * Cancel阶段：取消回滚
     * @param context 事务上下文
     * @return 是否成功
     */
    boolean cancel(TransactionContext context);

    /**
     * 获取参与者名称
     */
    String getName();
}

/**
 * TCC事务管理器
 */
public interface TCCTransactionManager {

    /**
     * 开始TCC事务
     */
    TCCTransaction begin();

    /**
     * 注册参与者
     */
    void registerParticipant(TCCTransaction transaction, TCCParticipant participant);

    /**
     * 提交事务
     */
    boolean commit(TCCTransaction transaction);

    /**
     * 回滚事务
     */
    boolean rollback(TCCTransaction transaction);
}
```

### 3.2 完整实现代码

```java
/**
 * TCC事务管理器实现
 */
@Component
public class TCCTransactionManagerImpl implements TCCTransactionManager {

    private static final Logger logger = LoggerFactory.getLogger(TCCTransactionManagerImpl.class);

    @Autowired
    private TCCTransactionRepository transactionRepository;

    @Autowired
    private TCCLogRepository logRepository;

    private final ExecutorService executor = Executors.newFixedThreadPool(10);

    @Override
    public TCCTransaction begin() {
        TCCTransaction transaction = new TCCTransaction();
        transaction.setId(UUID.randomUUID().toString());
        transaction.setStatus(TransactionStatus.TRYING);
        transaction.setCreateTime(LocalDateTime.now());
        transaction.setParticipants(new ArrayList<>());

        transactionRepository.save(transaction);
        logger.info("TCC事务开始: {}", transaction.getId());

        return transaction;
    }

    @Override
    public void registerParticipant(TCCTransaction transaction, TCCParticipant participant) {
        transaction.getParticipants().add(participant);
        logger.info("注册参与者: transactionId={}, participant={}",
            transaction.getId(), participant.getName());
    }

    @Override
    public boolean commit(TCCTransaction transaction) {
        logger.info("开始提交TCC事务: {}", transaction.getId());
        transaction.setStatus(TransactionStatus.CONFIRMING);
        transactionRepository.save(transaction);

        // 执行所有参与者的Confirm
        List<TCCParticipant> participants = transaction.getParticipants();

        for (TCCParticipant participant : participants) {
            boolean success = executeConfirmWithRetry(participant, transaction);
            if (!success) {
                logger.error("Confirm失败: transactionId={}, participant={}",
                    transaction.getId(), participant.getName());
                // Confirm失败需要人工介入或进入死信队列
                transaction.setStatus(TransactionStatus.CONFIRM_FAILED);
                transactionRepository.save(transaction);
                return false;
            }
        }

        transaction.setStatus(TransactionStatus.CONFIRMED);
        transaction.setCompleteTime(LocalDateTime.now());
        transactionRepository.save(transaction);

        logger.info("TCC事务提交成功: {}", transaction.getId());
        return true;
    }

    @Override
    public boolean rollback(TCCTransaction transaction) {
        logger.info("开始回滚TCC事务: {}", transaction.getId());
        transaction.setStatus(TransactionStatus.CANCELLING);
        transactionRepository.save(transaction);

        // 按照Try的逆序执行Cancel
        List<TCCParticipant> participants = transaction.getParticipants();
        List<TCCParticipant> reverseParticipants = new ArrayList<>(participants);
        Collections.reverse(reverseParticipants);

        for (TCCParticipant participant : reverseParticipants) {
            boolean success = executeCancelWithRetry(participant, transaction);
            if (!success) {
                logger.error("Cancel失败: transactionId={}, participant={}",
                    transaction.getId(), participant.getName());
                transaction.setStatus(TransactionStatus.CANCEL_FAILED);
                transactionRepository.save(transaction);
                return false;
            }
        }

        transaction.setStatus(TransactionStatus.CANCELLED);
        transaction.setCompleteTime(LocalDateTime.now());
        transactionRepository.save(transaction);

        logger.info("TCC事务回滚成功: {}", transaction.getId());
        return true;
    }

    /**
     * 带重试的Confirm执行
     */
    private boolean executeConfirmWithRetry(TCCParticipant participant,
                                           TCCTransaction transaction) {
        int maxRetries = 3;
        for (int i = 0; i < maxRetries; i++) {
            try {
                // 幂等性检查
                if (isAlreadyConfirmed(transaction.getId(), participant.getName())) {
                    return true;
                }

                boolean success = participant.confirm(
                    new TransactionContext(transaction.getId())
                );

                if (success) {
                    logRepository.saveConfirmLog(transaction.getId(), participant.getName());
                    return true;
                }
            } catch (Exception e) {
                logger.error("Confirm异常: {}, 重试次数: {}", e.getMessage(), i + 1);
            }

            // 指数退避
            try {
                Thread.sleep((long) (Math.pow(2, i) * 100));
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        return false;
    }

    /**
     * 带重试的Cancel执行
     */
    private boolean executeCancelWithRetry(TCCParticipant participant,
                                          TCCTransaction transaction) {
        int maxRetries = 3;
        for (int i = 0; i < maxRetries; i++) {
            try {
                // 幂等性检查
                if (isAlreadyCancelled(transaction.getId(), participant.getName())) {
                    return true;
                }

                boolean success = participant.cancel(
                    new TransactionContext(transaction.getId())
                );

                if (success) {
                    logRepository.saveCancelLog(transaction.getId(), participant.getName());
                    return true;
                }
            } catch (Exception e) {
                logger.error("Cancel异常: {}, 重试次数: {}", e.getMessage(), i + 1);
            }

            try {
                Thread.sleep((long) (Math.pow(2, i) * 100));
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        return false;
    }
}

/**
 * 账户服务TCC实现示例
 */
@Service
public class AccountTCCService implements TCCParticipant {

    @Autowired
    private AccountRepository accountRepository;

    @Autowired
    private FrozenRecordRepository frozenRecordRepository;

    private static final String PARTICIPANT_NAME = "account-service";

    @Override
    public String getName() {
        return PARTICIPANT_NAME;
    }

    /**
     * Try阶段：冻结金额
     */
    @Override
    @Transactional
    public boolean tryReserve(TransactionContext context) {
        String txId = context.getTransactionId();
        DeductRequest request = context.getDeductRequest();

        logger.info("Try阶段开始: txId={}, accountId={}, amount={}",
            txId, request.getAccountId(), request.getAmount());

        // 幂等性检查
        if (frozenRecordRepository.existsByTransactionId(txId)) {
            logger.info("Try已执行过，幂等返回: {}", txId);
            return true;
        }

        // 1. 查询账户
        Account account = accountRepository.findByIdForUpdate(request.getAccountId());
        if (account == null) {
            throw new AccountNotFoundException(request.getAccountId());
        }

        // 2. 检查余额
        if (account.getBalance().compareTo(request.getAmount()) < 0) {
            throw new InsufficientBalanceException("余额不足");
        }

        // 3. 扣减余额
        account.setBalance(account.getBalance().subtract(request.getAmount()));
        account.setFrozenAmount(account.getFrozenAmount().add(request.getAmount()));
        accountRepository.save(account);

        // 4. 创建冻结记录
        FrozenRecord record = new FrozenRecord();
        record.setId(UUID.randomUUID().toString());
        record.setTransactionId(txId);
        record.setAccountId(request.getAccountId());
        record.setAmount(request.getAmount());
        record.setStatus(FrozenStatus.FROZEN);
        record.setCreateTime(LocalDateTime.now());
        frozenRecordRepository.save(record);

        logger.info("Try阶段成功: txId={}, frozenRecordId={}", txId, record.getId());
        return true;
    }

    /**
     * Confirm阶段：确认扣款
     */
    @Override
    @Transactional
    public boolean confirm(TransactionContext context) {
        String txId = context.getTransactionId();

        logger.info("Confirm阶段开始: {}", txId);

        // 1. 查询冻结记录
        FrozenRecord record = frozenRecordRepository.findByTransactionId(txId);
        if (record == null) {
            logger.warn("冻结记录不存在: {}", txId);
            return true;  // 可能已经处理过
        }

        // 幂等性检查
        if (record.getStatus() == FrozenStatus.CONFIRMED) {
            logger.info("Confirm已执行过，幂等返回: {}", txId);
            return true;
        }

        // 2. 更新账户
        Account account = accountRepository.findById(record.getAccountId());
        account.setFrozenAmount(account.getFrozenAmount().subtract(record.getAmount()));
        accountRepository.save(account);

        // 3. 更新冻结记录状态
        record.setStatus(FrozenStatus.CONFIRMED);
        record.setConfirmTime(LocalDateTime.now());
        frozenRecordRepository.save(record);

        logger.info("Confirm阶段成功: {}", txId);
        return true;
    }

    /**
     * Cancel阶段：解冻金额
     */
    @Override
    @Transactional
    public boolean cancel(TransactionContext context) {
        String txId = context.getTransactionId();

        logger.info("Cancel阶段开始: {}", txId);

        // 1. 查询冻结记录
        FrozenRecord record = frozenRecordRepository.findByTransactionId(txId);
        if (record == null) {
            logger.warn("冻结记录不存在，可能已Cancel: {}", txId);
            return true;
        }

        // 幂等性检查
        if (record.getStatus() == FrozenStatus.CANCELLED) {
            logger.info("Cancel已执行过，幂等返回: {}", txId);
            return true;
        }

        // 2. 恢复账户余额
        Account account = accountRepository.findById(record.getAccountId());
        account.setBalance(account.getBalance().add(record.getAmount()));
        account.setFrozenAmount(account.getFrozenAmount().subtract(record.getAmount()));
        accountRepository.save(account);

        // 3. 更新冻结记录状态
        record.setStatus(FrozenStatus.CANCELLED);
        record.setCancelTime(LocalDateTime.now());
        frozenRecordRepository.save(record);

        logger.info("Cancel阶段成功: {}", txId);
        return true;
    }
}
```

### 3.3 使用示例

```java
/**
 * TCC使用示例：转账服务
 */
@Service
public class TransferService {

    @Autowired
    private TCCTransactionManager transactionManager;

    @Autowired
    private AccountTCCService fromAccountService;

    @Autowired
    private AccountTCCService toAccountService;

    @Autowired
    private InventoryTCCService inventoryService;

    /**
     * TCC转账
     */
    public TransferResult transfer(TransferRequest request) {
        // 1. 开始TCC事务
        TCCTransaction transaction = transactionManager.begin();

        try {
            // 2. 构建参与者上下文
            TransactionContext fromContext = new TransactionContext(
                transaction.getId(),
                new DeductRequest(request.getFromAccountId(), request.getAmount())
            );

            TransactionContext toContext = new TransactionContext(
                transaction.getId(),
                new AddRequest(request.getToAccountId(), request.getAmount())
            );

            // 3. Try阶段
            boolean fromTry = fromAccountService.tryReserve(fromContext);
            if (!fromTry) {
                throw new TCCException("转出账户Try失败");
            }
            transactionManager.registerParticipant(transaction, fromAccountService);

            boolean toTry = toAccountService.tryReserve(toContext);
            if (!toTry) {
                // 回滚已执行的Try
                fromAccountService.cancel(fromContext);
                throw new TCCException("转入账户Try失败");
            }
            transactionManager.registerParticipant(transaction, toAccountService);

            // 4. Confirm阶段
            boolean success = transactionManager.commit(transaction);

            if (success) {
                return TransferResult.success(transaction.getId());
            } else {
                return TransferResult.failure(transaction.getId(), "提交失败");
            }

        } catch (Exception e) {
            // 回滚事务
            transactionManager.rollback(transaction);
            return TransferResult.failure(transaction.getId(), e.getMessage());
        }
    }
}
```

---

## 四、TCC vs 其他事务模式

### 4.1 对比分析

```
┌─────────────────┬────────────────────────┬────────────────────────┬────────────────────────┐
│     特性        │         2PC            │         Saga           │         TCC            │
├─────────────────┼────────────────────────┼────────────────────────┼────────────────────────┤
│ 一致性级别      │ 强一致性               │ 最终一致性             │ 最终一致性             │
│ 业务侵入性      │ 低                     │ 中                     │ 高                     │
│ 并发性能        │ 低（锁阻塞）            │ 高                     │ 高                     │
│ 回滚机制        │ 自动回滚               │ 补偿操作               │ 预留资源释放           │
│ 实现复杂度      │ 低                     │ 中                     │ 高                     │
│ 适用场景        │ 短事务/强一致性         │ 长事务/业务流程         │ 高并发/资源预留         │
│ 隔离性          │ 好                     │ 需额外处理              │ 较好（资源预留）        │
└─────────────────┴────────────────────────┴────────────────────────┴────────────────────────┘
```

### 4.2 选型建议

```
┌─────────────────────────────────────────────────────────────┐
│                   分布式事务选型决策树                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   是否需要强一致性？                                         │
│        │                                                    │
│   是 ──┼──→ 使用2PC/XA                                     │
│        │                                                    │
│   否 ──┘                                                    │
│        │                                                    │
│        ▼                                                    │
│   事务执行时间是否较长？                                      │
│        │                                                    │
│   是 ──┼──→ 使用Saga模式                                    │
│        │    - 业务流程复杂                                  │
│        │    - 跨多个服务                                    │
│        │    - 需要状态追踪                                  │
│        │                                                    │
│   否 ──┘                                                    │
│        │                                                    │
│        ▼                                                    │
│   并发量是否很高？                                           │
│        │                                                    │
│   是 ──┼──→ 使用TCC                                         │
│        │    - 资源预留模式                                  │
│        │    - 高并发性能                                    │
│        │    - 需要业务改造                                  │
│        │                                                    │
│   否 ──┘                                                    │
│        │                                                    │
│        └──→ 使用Saga或本地消息表                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 五、TCC的最佳实践

### 5.1 幂等性保证

```java
/**
 * TCC幂等性保证
 */
@Component
public class TCCIdempotencyManager {

    @Autowired
    private StringRedisTemplate redisTemplate;

    private static final String TRY_KEY_PREFIX = "tcc:try:";
    private static final String CONFIRM_KEY_PREFIX = "tcc:confirm:";
    private static final String CANCEL_KEY_PREFIX = "tcc:cancel:";

    /**
     * Try幂等性检查
     */
    public boolean isTryProcessed(String txId) {
        String key = TRY_KEY_PREFIX + txId;
        Boolean exists = redisTemplate.hasKey(key);
        return Boolean.TRUE.equals(exists);
    }

    /**
     * 标记Try已处理
     */
    public void markTryProcessed(String txId, long expireHours) {
        String key = TRY_KEY_PREFIX + txId;
        redisTemplate.opsValue().set(key, "1", expireHours, TimeUnit.HOURS);
    }

    /**
     * Confirm幂等性检查
     */
    public boolean isConfirmProcessed(String txId) {
        String key = CONFIRM_KEY_PREFIX + txId;
        return Boolean.TRUE.equals(redisTemplate.hasKey(key));
    }

    /**
     * 标记Confirm已处理
     */
    public void markConfirmProcessed(String txId) {
        String key = CONFIRM_KEY_PREFIX + txId;
        redisTemplate.opsValue().set(key, "1", 7, TimeUnit.DAYS);
    }
}
```

### 5.2 悬挂与空回滚处理

```java
/**
 * TCC悬挂问题处理
 */
@Service
public class TCCHangingResolver {

    /**
     * 悬挂问题：Cancel比Try先执行
     * 场景：Try超时，协调者触发Cancel，随后Try到达
     *
     * 解决方案：记录Cancel已执行，拒绝后续的Try
     */
    @Transactional
    public boolean tryWithHangingCheck(String txId, TryExecutor executor) {
        // 1. 检查是否已经Cancel
        if (isCancelled(txId)) {
            logger.warn("事务已Cancel，拒绝Try: {}", txId);
            return false;  // 拒绝Try
        }

        // 2. 执行Try
        return executor.execute();
    }

    /**
     * 空回滚问题：Cancel时Try未执行
     * 场景：Try超时但还未执行，协调者触发Cancel
     *
     * 解决方案：Cancel时如果Try未执行，记录空回滚
     */
    @Transactional
    public boolean cancelWithEmptyCheck(String txId, CancelExecutor executor) {
        // 1. 检查Try是否执行
        boolean tryExecuted = isTryExecuted(txId);

        if (!tryExecuted) {
            // 2. 记录空回滚
            recordEmptyCancel(txId);
            logger.info("空回滚处理: {}", txId);
            return true;
        }

        // 3. 执行正常Cancel
        return executor.execute();
    }
}
```

---

## 六、总结

TCC模式是一种强大的分布式事务解决方案，通过将业务操作拆分为Try-Confirm-Cancel三个阶段，实现了高性能的柔性事务。

**核心优势**：

- 无全局锁，高并发性能
- 资源预留提供较好的隔离性
- 确认和取消操作幂等可重试

**主要挑战**：

- 业务侵入性强，需要修改业务代码
- 开发复杂度高，需要设计冻结/预留模型
- 悬挂、空回滚等边界情况需要处理

在实际应用中，TCC常与Saga、本地消息表等方案配合使用，根据业务场景选择最合适的事务处理策略。

---

## 参考资料

1. Pat Helland, "Life beyond Distributed Transactions: an Apostate's Opinion", CIDR 2007
2. Apache Seata Documentation: TCC Mode
3. "Microservices Patterns" by Chris Richardson
4. DTM Documentation: TCC Transaction


---

## 相关主题

- [Saga模式详解](./Saga模式详解.md)
- [2PC两阶段提交](./两阶段提交2PC.md)
- [AT模式详解](../AT模式详解.md)

## 参考资源

- [TCC模式](https://www.byteslounge.com/tutorials/tcc-transactions-pattern)
