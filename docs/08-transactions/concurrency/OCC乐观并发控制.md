# 乐观并发控制 OCC（Optimistic Concurrency Control）

## 概述

乐观并发控制（Optimistic Concurrency Control，OCC）是一种用于管理并发数据访问的并发控制策略。与悲观并发控制（Pessimistic Concurrency Control，PCC）不同，OCC假设事务之间发生冲突的概率较低，因此允许事务在不加锁的情况下执行，仅在提交时检查是否存在冲突。

OCC由H.T. Kung和John T. Robinson于1981年提出，特别适用于读多写少、冲突概率较低的场景，如Web应用、内容管理系统等。

---

## 一、OCC的基本概念

### 1.1 核心思想

```
┌─────────────────────────────────────────────────────────────┐
│                   OCC核心思想                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   悲观并发控制（PCC）：                                        │
│   ┌─────────┐                   ┌─────────┐                │
│   │ 事务A   │ ───── 加锁 ──────→│  数据X   │                │
│   │ (读写)  │                   │         │                │
│   └─────────┘                   └────┬────┘                │
│                                      │                      │
│   ┌─────────┐                   ┌────┘                      │
│   │ 事务B   │ ←──── 阻塞 ────────┘                         │
│   │ (读写)  │    等待锁释放                                   │
│   └─────────┘                                               │
│                                                             │
│   特点：先加锁，后操作，冲突时阻塞                             │
│                                                             │
│   ───────────────────────────────────────────────────────── │
│                                                             │
│   乐观并发控制（OCC）：                                        │
│   ┌─────────┐                   ┌─────────┐                │
│   │ 事务A   │ ─── 读取数据 ────→│  数据X   │                │
│   │         │    version=100    │         │                │
│   │ 本地计算 │                   └─────────┘                │
│   │ 修改值   │                                              │
│   │         │                   ┌─────────┐                │
│   │ 提交时   │ ─── 验证版本 ────→│ version │                │
│   │ 检查版本 │    仍为100?       │ =100?   │                │
│   │         │                   └────┬────┘                │
│   │         │    ┌── Yes ───→ 更新成功                     │
│   │         │    └── No ────→ 冲突！回滚重试                │
│   └─────────┘                                               │
│                                                             │
│   特点：先操作，提交时验证，冲突时回滚                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 三阶段模型

```
┌─────────────────────────────────────────────────────────────┐
│                   OCC三阶段模型                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   阶段1：读取阶段（Read Phase）                               │
│   ─────────────────────────────                             │
│   - 读取所需数据到私有工作区                                  │
│   - 记录数据的版本号或时间戳                                  │
│   - 不加任何锁                                               │
│                                                             │
│   ┌─────────────┐                                           │
│   │  数据库      │                                           │
│   │  Data: X=10 │                                           │
│   │  Ver:  100  │                                           │
│   └──────┬──────┘                                           │
│          │ 读取X=10, Ver=100                                 │
│          ▼                                                  │
│   ┌─────────────┐                                           │
│   │  事务私有空间 │                                           │
│   │  X=10 (本地) │                                           │
│   │  Ver=100    │                                           │
│   └─────────────┘                                           │
│                                                             │
│   阶段2：验证阶段（Validation Phase）                         │
│   ─────────────────────────────────                         │
│   - 检查数据是否被其他事务修改                                │
│   - 比较记录的版本号/时间戳                                   │
│   - 决定提交或回滚                                           │
│                                                             │
│   阶段3：写入阶段（Write Phase）                              │
│   ──────────────────────────────                            │
│   - 验证通过：更新数据，版本号+1                              │
│   - 验证失败：回滚事务，可选择重试                            │
│                                                             │
│   成功提交：                                                 │
│   ┌─────────────┐                                           │
│   │  数据库      │                                           │
│   │  Data: X=15 │ ← 新值                                     │
│   │  Ver:  101  │ ← 版本+1                                   │
│   └─────────────┘                                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、OCC的实现机制

### 2.1 版本号机制

```
┌─────────────────────────────────────────────────────────────┐
│                 版本号机制实现                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   数据表结构：                                               │
│   ┌─────────────────────────────────────────┐              │
│   │  id  │  data  │  version  │  update_time │             │
│   │  1   │  ...   │    100    │  2024-01-01 │             │
│   └─────────────────────────────────────────┘              │
│                                                             │
│   读取阶段：                                                 │
│   SELECT id, data, version FROM table WHERE id = 1;        │
│   → 得到: data=..., version=100                            │
│                                                             │
│   业务处理（本地计算）...                                     │
│                                                             │
│   提交阶段：                                                 │
│   UPDATE table                                              │
│   SET data = 'new_value',                                   │
│       version = version + 1,                                │
│       update_time = NOW()                                   │
│   WHERE id = 1 AND version = 100;  ← 关键：带上版本号        │
│                                                             │
│   结果判断：                                                 │
│   - 影响行数 = 1：更新成功，无冲突                           │
│   - 影响行数 = 0：更新失败，版本已变，发生冲突                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 时间戳机制

```
┌─────────────────────────────────────────────────────────────┐
│                 时间戳机制实现                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   数据表结构：                                               │
│   ┌─────────────────────────────────────────┐              │
│   │  id  │  data  │  last_modified          │             │
│   │  1   │  ...   │  1704067200000          │             │
│   └─────────────────────────────────────────┘              │
│                                                             │
│   读取阶段：                                                 │
│   SELECT id, data, last_modified FROM table WHERE id = 1;  │
│   → 得到: last_modified = 1704067200000                    │
│                                                             │
│   提交阶段：                                                 │
│   UPDATE table                                              │
│   SET data = 'new_value',                                   │
│       last_modified = 1704153600000  ← 当前时间戳           │
│   WHERE id = 1                                              │
│     AND last_modified = 1704067200000;  ← 读取时的时间戳     │
│                                                             │
│   特点：                                                     │
│   - 使用物理时间戳                                           │
│   - 需要注意时钟同步问题                                     │
│   - 可精确到毫秒或微秒                                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.3 验证策略

```
┌─────────────────────────────────────────────────────────────┐
│                 OCC验证策略对比                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   策略1：向后验证（Backward Validation）                      │
│   ─────────────────────────────────────                     │
│   检查本事务读取的数据是否被其他已提交事务修改过               │
│                                                             │
│   事务A读取[X=10, Y=20]                                      │
│        │                                                    │
│        │ 事务B提交，修改X=15                                 │
│        ▼                                                    │
│   事务A提交前检查：                                          │
│   - X的版本是否变化？是！→ 冲突！                            │
│                                                             │
│   优点：可以立即发现冲突                                     │
│   缺点：需要维护读集合                                       │
│                                                             │
│   ───────────────────────────────────────────────────────── │
│                                                             │
│   策略2：向前验证（Forward Validation）                       │
│   ────────────────────────────────────                      │
│   检查本事务修改的数据是否被其他活跃事务读取过                 │
│                                                             │
│   事务A读取[X=10]，准备修改为X=15                            │
│        │                                                    │
│        │ 事务B读取X=10（活跃中）                              │
│        ▼                                                    │
│   事务A提交前检查：                                          │
│   - 是否有活跃事务读取了X？是！→ 冲突！                      │
│                                                             │
│   优点：延迟冲突发现，可能提高并发度                          │
│   缺点：冲突处理复杂                                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、OCC的Java实现

### 3.1 基础实现

```java
/**
 * OCC乐观锁基础实现
 */
@Component
public class OptimisticLockManager {
    
    @Autowired
    private JdbcTemplate jdbcTemplate;
    
    /**
     * 带乐观锁的更新操作
     */
    public boolean updateWithOptimisticLock(String sql, Object[] params, 
                                           int versionIndex, long expectedVersion) {
        // 构造带版本号的SQL
        String optimisticSql = sql + " AND version = ?";
        
        // 添加版本号参数
        Object[] newParams = Arrays.copyOf(params, params.length + 1);
        newParams[params.length] = expectedVersion;
        
        // 执行更新
        int affectedRows = jdbcTemplate.update(optimisticSql, newParams);
        
        // 判断结果
        return affectedRows > 0;
    }
    
    /**
     * 带重试的乐观锁更新
     */
    public <T> T executeWithRetry(RetryableOperation<T> operation, 
                                  int maxRetries) {
        int attempts = 0;
        while (attempts < maxRetries) {
            try {
                return operation.execute();
            } catch (OptimisticLockException e) {
                attempts++;
                if (attempts >= maxRetries) {
                    throw new OptimisticLockException(
                        "Max retries exceeded: " + maxRetries, e);
                }
                
                // 指数退避
                long backoff = (long) (Math.pow(2, attempts) * 100);
                try {
                    Thread.sleep(backoff);
                } catch (InterruptedException ie) {
                    Thread.currentThread().interrupt();
                    throw new RuntimeException(ie);
                }
            }
        }
        throw new IllegalStateException("Should not reach here");
    }
    
    @FunctionalInterface
    public interface RetryableOperation<T> {
        T execute();
    }
}

/**
 * 乐观锁异常
 */
public class OptimisticLockException extends RuntimeException {
    public OptimisticLockException(String message) {
        super(message);
    }
    
    public OptimisticLockException(String message, Throwable cause) {
        super(message, cause);
    }
}
```

### 3.2 完整业务实现

```java
/**
 * 账户服务 - OCC实现
 */
@Service
public class AccountServiceWithOCC {
    
    @Autowired
    private AccountRepository accountRepository;
    
    @Autowired
    private OptimisticLockManager lockManager;
    
    /**
     * 查询账户（返回包含版本号的实体）
     */
    @Transactional(readOnly = true)
    public Account getAccountWithVersion(String accountId) {
        return accountRepository.findById(accountId)
            .orElseThrow(() -> new AccountNotFoundException(accountId));
    }
    
    /**
     * 更新余额 - 基础OCC
     */
    @Transactional
    public boolean updateBalance(String accountId, BigDecimal amount, long version) {
        int affected = accountRepository.updateBalance(accountId, amount, version);
        
        if (affected == 0) {
            // 版本冲突，更新失败
            throw new OptimisticLockException(
                "Account " + accountId + " was modified by another transaction"
            );
        }
        
        return true;
    }
    
    /**
     * 转账 - 带重试的OCC
     */
    public void transferWithRetry(String fromAccountId, String toAccountId, 
                                  BigDecimal amount) {
        lockManager.executeWithRetry(() -> {
            doTransfer(fromAccountId, toAccountId, amount);
            return null;
        }, 3);  // 最多重试3次
    }
    
    /**
     * 执行转账
     */
    @Transactional
    protected void doTransfer(String fromAccountId, String toAccountId, 
                             BigDecimal amount) {
        // 1. 读取两个账户（带版本号）
        Account fromAccount = getAccountWithVersion(fromAccountId);
        Account toAccount = getAccountWithVersion(toAccountId);
        
        // 2. 业务检查
        if (fromAccount.getBalance().compareTo(amount) < 0) {
            throw new InsufficientBalanceException("余额不足");
        }
        
        // 3. 计算新余额
        BigDecimal newFromBalance = fromAccount.getBalance().subtract(amount);
        BigDecimal newToBalance = toAccount.getBalance().add(amount);
        
        // 4. 更新转出账户（带版本检查）
        int fromUpdated = accountRepository.updateBalanceAndVersion(
            fromAccountId, 
            newFromBalance, 
            fromAccount.getVersion()
        );
        
        if (fromUpdated == 0) {
            throw new OptimisticLockException("转出账户已被修改");
        }
        
        // 5. 更新转入账户（带版本检查）
        int toUpdated = accountRepository.updateBalanceAndVersion(
            toAccountId,
            newToBalance,
            toAccount.getVersion()
        );
        
        if (toUpdated == 0) {
            // 这里会产生不一致！实际应用中需要补偿处理
            throw new OptimisticLockException("转入账户已被修改，需要补偿");
        }
        
        // 6. 记录转账日志
        recordTransferLog(fromAccountId, toAccountId, amount);
    }
}

/**
 * 账户实体
 */
@Entity
@Table(name = "account")
@Data
public class Account {
    @Id
    private String id;
    
    private BigDecimal balance;
    
    @Version  // JPA乐观锁注解
    private Long version;
    
    private LocalDateTime updateTime;
}

/**
 * 账户Repository
 */
@Repository
public interface AccountRepository extends JpaRepository<Account, String> {
    
    /**
     * 带版本检查的更新
     */
    @Modifying
    @Query("UPDATE Account a SET a.balance = :balance, " +
           "a.version = a.version + 1, " +
           "a.updateTime = CURRENT_TIMESTAMP " +
           "WHERE a.id = :id AND a.version = :version")
    int updateBalanceAndVersion(@Param("id") String id,
                                @Param("balance") BigDecimal balance,
                                @Param("version") Long version);
}
```

### 3.3 JPA注解实现

```java
/**
 * JPA @Version 注解实现乐观锁
 */
@Service
public class JPAVerOptimisticLockService {
    
    @Autowired
    private ProductRepository productRepository;
    
    /**
     * 扣减库存 - JPA自动乐观锁
     */
    @Transactional
    public void deductStock(Long productId, int quantity) {
        try {
            // 1. 读取商品（自动获取version）
            Product product = productRepository.findById(productId)
                .orElseThrow(() -> new ProductNotFoundException(productId));
            
            // 2. 检查库存
            if (product.getStock() < quantity) {
                throw new InsufficientStockException("库存不足");
            }
            
            // 3. 扣减库存
            product.setStock(product.getStock() - quantity);
            
            // 4. 保存（JPA自动检查version，冲突时抛异常）
            productRepository.save(product);
            
        } catch (OptimisticLockingFailureException e) {
            // JPA乐观锁冲突异常
            throw new OptimisticLockException("商品库存已被其他事务修改", e);
        }
    }
}

/**
 * 商品实体
 */
@Entity
@Table(name = "product")
@Data
public class Product {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private Long id;
    
    private String name;
    
    private Integer stock;
    
    /**
     * @Version注解标记乐观锁字段
     * - 每次更新自动+1
     * - 更新时自动检查version是否匹配
     */
    @Version
    private Long version;
}
```

### 3.4 MyBatis实现

```java
/**
 * MyBatis乐观锁实现
 */
@Mapper
public interface OrderMapper {
    
    /**
     * 根据ID和版本号查询订单
     */
    @Select("SELECT * FROM orders WHERE id = #{id}")
    Order selectById(@Param("id") Long id);
    
    /**
     * 带乐观锁的更新
     */
    @Update("UPDATE orders " +
            "SET status = #{status}, " +
            "    version = version + 1, " +
            "    update_time = NOW() " +
            "WHERE id = #{id} " +
            "  AND version = #{version}")
    int updateWithVersion(@Param("id") Long id,
                         @Param("status") Integer status,
                         @Param("version") Long version);
}

/**
 * 订单服务
 */
@Service
public class OrderService {
    
    @Autowired
    private OrderMapper orderMapper;
    
    /**
     * 更新订单状态 - 带乐观锁
     */
    public void updateOrderStatus(Long orderId, Integer newStatus) {
        // 重试逻辑
        int maxRetries = 3;
        for (int i = 0; i < maxRetries; i++) {
            // 1. 读取当前订单
            Order order = orderMapper.selectById(orderId);
            if (order == null) {
                throw new OrderNotFoundException(orderId);
            }
            
            // 2. 状态机检查
            if (!isValidStatusTransition(order.getStatus(), newStatus)) {
                throw new InvalidStatusException("非法状态转换");
            }
            
            // 3. 尝试更新
            int affected = orderMapper.updateWithVersion(
                orderId, newStatus, order.getVersion()
            );
            
            if (affected > 0) {
                // 更新成功
                return;
            }
            
            // 更新失败，版本冲突，重试
            if (i < maxRetries - 1) {
                try {
                    Thread.sleep(50 * (i + 1));  // 退避
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                }
            }
        }
        
        throw new OptimisticLockException("更新订单状态失败，重试次数耗尽");
    }
}
```

---

## 四、OCC的优缺点

### 4.1 优点

| 优点 | 说明 |
|-----|------|
| **无锁等待** | 读操作不需要加锁，不会阻塞其他事务 |
| **高读性能** | 适合读多写少的场景 |
| **无死锁** | 不涉及锁等待，不会出现死锁 |
| **简单易实现** | 只需增加版本号字段 |

### 4.2 缺点

| 缺点 | 说明 |
|-----|------|
| **写冲突频繁时性能差** | 冲突重试开销大 |
| **长事务问题** | 事务越长，冲突概率越高 |
| **回滚成本高** | 冲突时需要回滚已完成的计算 |
| **无法保证可重复读** | 读取后数据可能被修改 |

### 4.3 适用场景

```
┌─────────────────────────────────────────────────────────────┐
│                   OCC适用场景分析                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   推荐使用OCC的场景：                                        │
│   ✓ 读多写少（读比例 > 80%）                                 │
│   ✓ 冲突概率低                                              │
│   ✓ 短事务                                                  │
│   ✓ 互联网应用（如CMS、博客系统）                             │
│                                                             │
│   不推荐OCC的场景：                                          │
│   ✗ 写多读少                                               │
│   ✗ 冲突概率高（如热点数据频繁更新）                          │
│   ✗ 长事务                                                  │
│   ✗ 金融交易系统                                            │
│                                                             │
│   OCC vs 悲观锁选择：                                         │
│                                                             │
│   冲突概率低 ────────────────────────────────→ 冲突概率高    │
│        │                                          │         │
│        ▼                                          ▼         │
│      使用OCC                                   使用悲观锁    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 五、OCC的最佳实践

### 5.1 重试策略

```java
/**
 * 指数退避重试策略
 */
@Component
public class ExponentialBackoffRetry {
    
    private static final int MAX_RETRIES = 5;
    private static final long INITIAL_BACKOFF = 50;  // ms
    
    public <T> T executeWithExponentialBackoff(RetryableTask<T> task) {
        int attempt = 0;
        while (attempt < MAX_RETRIES) {
            try {
                return task.execute();
            } catch (OptimisticLockException e) {
                attempt++;
                if (attempt >= MAX_RETRIES) {
                    throw new OptimisticLockException(
                        "Max retries exceeded after " + MAX_RETRIES + " attempts", e);
                }
                
                // 指数退避 + 随机抖动
                long backoff = (long) (INITIAL_BACKOFF * Math.pow(2, attempt));
                long jitter = (long) (Math.random() * 10);
                
                try {
                    Thread.sleep(backoff + jitter);
                } catch (InterruptedException ie) {
                    Thread.currentThread().interrupt();
                    throw new RuntimeException(ie);
                }
            }
        }
        throw new IllegalStateException("Unexpected state");
    }
}
```

### 5.2 批量更新优化

```java
/**
 * 批量更新使用OCC
 */
@Service
public class BatchUpdateService {
    
    /**
     * 批量更新使用乐观锁
     * 策略：先查询所有记录，批量验证版本，然后批量更新
     */
    @Transactional
    public BatchUpdateResult batchUpdate(List<UpdateRequest> requests) {
        // 1. 批量查询
        List<Long> ids = requests.stream()
            .map(UpdateRequest::getId)
            .collect(Collectors.toList());
        
        List<Product> products = productRepository.findAllById(ids);
        Map<Long, Product> productMap = products.stream()
            .collect(Collectors.toMap(Product::getId, p -> p));
        
        // 2. 验证版本并准备更新
        List<Product> toUpdate = new ArrayList<>();
        List<Long> conflictIds = new ArrayList<>();
        
        for (UpdateRequest request : requests) {
            Product product = productMap.get(request.getId());
            
            if (product == null) {
                conflictIds.add(request.getId());
                continue;
            }
            
            if (!product.getVersion().equals(request.getExpectedVersion())) {
                conflictIds.add(request.getId());
                continue;
            }
            
            // 应用更新
            product.setPrice(request.getNewPrice());
            toUpdate.add(product);
        }
        
        // 3. 批量保存（JPA会自动处理version）
        if (!toUpdate.isEmpty()) {
            productRepository.saveAll(toUpdate);
        }
        
        return BatchUpdateResult.builder()
            .successCount(toUpdate.size())
            .conflictIds(conflictIds)
            .build();
    }
}
```

---

## 六、总结

乐观并发控制（OCC）是一种有效的并发控制策略，特别适合读多写少、冲突概率低的场景。通过版本号或时间戳机制，OCC实现了无锁的并发控制，避免了死锁问题，在读密集场景下性能优异。

**关键要点**：
1. 三阶段模型：读取、验证、写入
2. 版本号机制是最常用的实现方式
3. 需要配合重试策略处理冲突
4. 不适合高冲突、长事务场景

**最佳实践**：
- 选择合适的重试次数和退避策略
- 监控冲突率，必要时切换到悲观锁
- 保持事务简短，减少冲突窗口
- 批量操作时考虑批量验证

---

## 参考资料

1. H.T. Kung, John T. Robinson, "On Optimistic Methods for Concurrency Control", ACM TODS, 1981
2. "Database Internals" by Alex Petrov, Chapter 7
3. JPA Specification: "Optimistic Locking"
4. MySQL Documentation: "Optimistic Locking"
