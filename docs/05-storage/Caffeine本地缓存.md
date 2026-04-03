# Caffeine本地缓存专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

Caffeine是Java生态中高性能的本地缓存库，采用W-TinyLFU淘汰策略，提供优异的读写性能和命中率。作为多级缓存架构中的L1层，Caffeine能有效降低分布式缓存的访问压力，提升应用响应速度。

---

## 一、核心概念

### 1.1 Caffeine简介

```
┌─────────────────────────────────────────────────────────────┐
│                    Caffeine 特性概览                         │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  Caffeine 是什么？                                          │
│  ├─ Java 8+ 高性能本地缓存库                                 │
│  ├─ 由Ben Manes开发（Guava Cache原作者）                     │
│  ├─ 采用W-TinyLFU淘汰策略                                   │
│  └─ 性能比Guava Cache提升约6倍                               │
│                                                            │
│  核心优势：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │ ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │ │
│  │ │   高性能    │  │  高命中率   │  │   易用性    │     │ │
│  │ │  读写操作   │  │  W-TinyLFU │  │  Builder模式│     │ │
│  │ │  O(1)时间   │  │  频率统计   │  │  丰富配置   │     │ │
│  │ │  无锁设计   │  │  窗口缓存   │  │  兼容Guava  │     │ │
│  │ └─────────────┘  └─────────────┘  └─────────────┘     │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  适用场景：                                                  │
│  ├─ 读多写少的热点数据缓存                                   │
│  ├─ 计算成本高的结果缓存                                     │
│  ├─ 配置信息、字典数据缓存                                   │
│  └─ 分布式缓存的L1层                                        │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 淘汰策略对比

```
┌─────────────────────────────────────────────────────────────┐
│                    缓存淘汰策略对比                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  LRU (Least Recently Used):                                │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  思想: 淘汰最久未使用的                                 │ │
│  │  问题: 对突发流量敏感，可能淘汰热点数据                  │ │
│  │                                                       │ │
│  │  示例: A-B-C-D-E (容量4)                              │ │
│  │        访问A, A移到头部                                │ │
│  │        新访问F, 淘汰B (B可能仍是热点)                   │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  LFU (Least Frequently Used):                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  思想: 淘汰访问频率最低的                               │ │
│  │  问题: 历史数据累积，新数据难以存活                      │ │
│  │                                                       │ │
│  │  示例: A(访问100次), B(访问1次)                        │ │
│  │        新数据C, 即使C是热点，因频率低被淘汰              │ │
│  │        需要定期衰减频率计数                              │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  W-TinyLFU (Window Tiny LFU):                              │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  Caffeine采用的策略，结合LRU和LFU优点                   │ │
│  │                                                       │ │
│  │  结构:                                                │ │
│  │  ┌─────────────────────────────────────────────────┐  │ │
│  │  │  Window Cache (1%)                              │  │ │
│  │  │  LRU结构，新数据先进入                             │  │ │
│  │  │  保护新数据不被快速淘汰                            │  │ │
│  │  └──────────────────┬──────────────────────────────┘  │ │
│  │                     ↓ 竞争进入                         │ │
│  │  ┌─────────────────────────────────────────────────┐  │ │
│  │  │  Main Cache (99%)                               │  │ │
│  │  │  SLRU (Segmented LRU)                           │  │ │
│  │  │  ├─ Protected (80%): 长期存活的热点数据          │  │ │
│  │  │  └─ Probation (20%): 候选区，竞争进入Protected   │  │ │
│  │  └─────────────────────────────────────────────────┘  │ │
│  │                                                       │ │
│  │  频率统计: 4-bit Count-Min Sketch                     │ │
│  │  ├─ 近似统计访问频率                                   │ │
│  │  ├─ 内存占用极低                                       │ │
│  │  └─ 定期衰减，避免历史热点长期占用                     │ │
│  │                                                       │ │
│  │  淘汰流程:                                            │ │
│  │  1. 新数据 → Window Cache                            │ │
│  │  2. Window满 → 与Main Cache Probation区竞争          │ │
│  │  3. 频率高者进入/保留Probation，低者淘汰               │ │
│  │  4. Probation区满 → 与Protected区竞争                 │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、技术细节

### 2.1 核心组件架构

```
┌─────────────────────────────────────────────────────────────┐
│                  Caffeine 内部架构                           │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │                  Caffeine<K, V>                        │ │
│  │                  (缓存主体)                             │ │
│  └──────────────────┬────────────────────────────────────┘ │
│                     │                                      │
│      ┌──────────────┼──────────────┐                      │
│      ↓              ↓              ↓                      │
│  ┌────────┐    ┌────────┐    ┌────────┐                  │
│  │ Policy │    │ Buffer │    │ Expire │                  │
│  │ (淘汰) │    │ (缓冲) │    │ (过期) │                  │
│  └───┬────┘    └───┬────┘    └───┬────┘                  │
│      │             │             │                        │
│  ┌───┴────┐   ┌───┴────┐   ┌───┴────┐                    │
│  │W-TinyLFU│   │ReadBuf │   │WriteBuf│   Scheduler       │
│  │ ├─Window│   │(读缓冲) │   │(写缓冲) │   (定时清理)      │
│  │ ├─SLRU  │   │RingBuffer│  │MPSC队列│                    │
│  │ └─Sketch│   │批量淘汰 │   │异步刷新 │                    │
│  └─────────┘   └─────────┘   └─────────┘                   │
│                                                            │
│  无锁设计：                                                  │
│  ├─ 读操作：完全无锁，使用ThreadLocal读取副本                 │
│  ├─ 写操作：批量合并，使用MPSC队列异步处理                     │
│  └─ 状态更新：CAS操作，避免锁竞争                              │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 读写缓冲机制

```
┌─────────────────────────────────────────────────────────────┐
│                    读写缓冲优化                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  读缓冲 (Read Buffer):                                      │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  问题: 每次读都更新LRU链表（写操作），并发下竞争激烈      │ │
│  │                                                       │ │
│  │  解决: Ring Buffer缓冲读操作                           │ │
│  │                                                       │ │
│  │  Thread-1 ──→┌────────────────┐                     │ │
│  │  Thread-2 ──→│  Ring Buffer   │──→ 批量处理         │ │
│  │  Thread-3 ──→│  (每个线程独立) │    更新访问记录      │ │
│  │  Thread-4 ──→└────────────────┘                     │ │
│  │                                                       │ │
│  │  效果: 将频繁的读操作合并为批量写，减少锁竞争           │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  写缓冲 (Write Buffer):                                     │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  MPSC (Multi-Producer Single-Consumer) 队列           │ │
│  │                                                       │ │
│  │  生产者 ──┐                                          │ │
│  │  生产者 ──┼──→ ┌─────────────┐ ──→ 消费者(单线程)     │ │
│  │  生产者 ──┘    │ Write Buffer│      批量处理写操作     │ │
│  │                │ (MPSC Queue)│                        │ │
│  │  效果: 写操作异步化，主流程快速返回                     │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

---

## 三、实践指南

### 3.1 基础配置

```java
@Configuration
public class CaffeineConfig {

    /**
     * 基础缓存配置
     */
    @Bean
    public Cache<String, User> userCache() {
        return Caffeine.newBuilder()
            // 最大容量10000条
            .maximumSize(10000)
            // 写入后30分钟过期
            .expireAfterWrite(Duration.ofMinutes(30))
            // 访问后10分钟过期（续期）
            .expireAfterAccess(Duration.ofMinutes(10))
            // 刷新时间（异步刷新，不阻塞读）
            .refreshAfterWrite(Duration.ofMinutes(5))
            // 启用统计
            .recordStats()
            // 淘汰监听器
            .removalListener((key, value, cause) ->
                log.info("Key {} removed due to {}", key, cause))
            // 构建缓存
            .build();
    }

    /**
     * 带权重的缓存（不同条目占用不同空间）
     */
    @Bean
    public Cache<String, List<Order>> orderCache() {
        return Caffeine.newBuilder()
            // 最大权重100万
            .maximumWeight(1000000)
            // 权重计算函数（按列表大小）
            .weigher((String key, List<Order> orders) ->
                orders.size() * 100)
            .expireAfterWrite(Duration.ofHours(1))
            .recordStats()
            .build();
    }

    /**
     * 异步加载缓存
     */
    @Bean
    public AsyncLoadingCache<String, User> asyncUserCache() {
        return Caffeine.newBuilder()
            .maximumSize(10000)
            .expireAfterWrite(Duration.ofMinutes(30))
            // 异步加载器
            .buildAsync((key, executor) ->
                CompletableFuture.supplyAsync(
                    () -> loadUserFromDb(key), executor));
    }
}
```

### 3.2 加载策略

```java
@Service
public class CacheLoadingService {

    @Autowired
    private UserRepository userRepository;

    private LoadingCache<String, User> userCache;

    @PostConstruct
    public void init() {
        userCache = Caffeine.newBuilder()
            .maximumSize(10000)
            .expireAfterWrite(Duration.ofMinutes(30))
            // 自动加载器
            .build(new CacheLoader<String, User>() {
                @Override
                public User load(String key) {
                    // 缓存未命中时自动加载
                    Long userId = Long.valueOf(key.replace("user:", ""));
                    return userRepository.findById(userId)
                        .orElseThrow(() -> new RuntimeException("User not found"));
                }

                @Override
                public List<User> loadAll(Iterable<? extends String> keys) {
                    // 批量加载优化
                    List<Long> ids = StreamSupport.stream(keys.spliterator(), false)
                        .map(k -> Long.valueOf(k.replace("user:", "")))
                        .collect(Collectors.toList());
                    return userRepository.findAllById(ids);
                }

                @Override
                public User reload(String key, User oldValue) {
                    // 异步刷新时调用
                    return load(key);
                }
            });
    }

    public User getUser(String key) {
        // 自动处理加载
        return userCache.get(key);
    }

    public Map<String, User> getUsers(List<String> keys) {
        // 批量获取，自动批量加载
        return userCache.getAll(keys);
    }
}
```

### 3.3 与Spring Cache集成

```java
@Configuration
@EnableCaching
public class SpringCacheConfig {

    @Bean
    public CacheManager cacheManager() {
        CaffeineCacheManager manager = new CaffeineCacheManager();
        manager.setCaffeine(Caffeine.newBuilder()
            .maximumSize(10000)
            .expireAfterWrite(Duration.ofMinutes(30)));
        return manager;
    }

    // 多缓存配置
    @Bean("caffeineCacheManager")
    public CacheManager caffeineCacheManager() {
        CaffeineCacheManager manager = new CaffeineCacheManager();
        // 默认配置
        manager.setCaffeine(defaultCaffeine());

        // 为特定缓存定制
        Map<String, Caffeine<Object, Object>> cacheConfigs = new HashMap<>();
        cacheConfigs.put("users", userCaffeine());
        cacheConfigs.put("orders", orderCaffeine());

        manager.setCacheNames(cacheConfigs.keySet());
        return manager;
    }

    private Caffeine<Object, Object> defaultCaffeine() {
        return Caffeine.newBuilder()
            .maximumSize(1000)
            .expireAfterWrite(Duration.ofMinutes(10));
    }

    private Caffeine<Object, Object> userCaffeine() {
        return Caffeine.newBuilder()
            .maximumSize(10000)
            .expireAfterWrite(Duration.ofMinutes(30))
            .recordStats();
    }

    private Caffeine<Object, Object> orderCaffeine() {
        return Caffeine.newBuilder()
            .maximumSize(5000)
            .expireAfterWrite(Duration.ofHours(1));
    }
}

// 使用示例
@Service
public class UserService {

    @Cacheable(value = "users", key = "#userId")
    public User getUser(Long userId) {
        return userRepository.findById(userId).orElse(null);
    }

    @CacheEvict(value = "users", key = "#user.id")
    public void updateUser(User user) {
        userRepository.save(user);
    }

    @CachePut(value = "users", key = "#user.id")
    public User updateAndRefresh(User user) {
        return userRepository.save(user);
    }
}
```

### 3.4 多级缓存实现

```java
@Component
public class TieredCache {

    @Autowired
    private Cache<String, Object> localCache; // Caffeine

    @Autowired
    private RedisTemplate<String, Object> redisCache; // Redis

    @Autowired
    private UserRepository db; // DB

    /**
     * 多级缓存查询
     */
    public Object get(String key) {
        // L1: Caffeine
        Object value = localCache.getIfPresent(key);
        if (value != null) {
            return value;
        }

        // L2: Redis
        value = redisCache.opsForValue().get(key);
        if (value != null) {
            // 回填L1
            localCache.put(key, value);
            return value;
        }

        // L3: DB
        value = loadFromDb(key);
        if (value != null) {
            // 回填L2和L1
            redisCache.opsForValue().set(key, value, 30, TimeUnit.MINUTES);
            localCache.put(key, value);
        }

        return value;
    }

    /**
     * 多级缓存更新（延迟双删）
     */
    public void update(String key, Object value) {
        // 1. 更新DB
        saveToDb(key, value);

        // 2. 删L2
        redisCache.delete(key);

        // 3. 删L1
        localCache.invalidate(key);

        // 4. 延迟再次删（异步）
        CompletableFuture.delayedExecutor(500, TimeUnit.MILLISECONDS)
            .execute(() -> {
                redisCache.delete(key);
                localCache.invalidate(key);
            });
    }
}
```

---

## 四、系统对比

### 4.1 性能对比

```
┌─────────────────────────────────────────────────────────────┐
│                本地缓存性能对比                              │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  读操作性能 (ops/ms):                                       │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  缓存实现      │ 单线程   │ 多线程(8核)  │ 特点        │ │
│  ├─────────────────┼──────────┼─────────────┼────────────┤ │
│  │  ConcurrentHashMap│  80     │    200      │ 无淘汰      │ │
│  │  Guava Cache    │   70     │    150      │ LRU         │ │
│  │  Caffeine       │  120     │    600      │ W-TinyLFU   │ │
│  │  EhCache 3      │   60     │    180      │ 功能丰富    │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  命中率对比（Zipf分布访问模式）：                            │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  缓存大小  │ LRU    │ LFU    │ W-TinyLFU              │ │
│  ├────────────┼────────┼────────┼────────────────────────┤ │
│  │   1%       │  15%   │  20%   │    35%                 │ │
│  │   10%      │  35%   │  45%   │    55%                 │ │
│  │   25%      │  55%   │  65%   │    72%                 │ │
│  │   50%      │  75%   │  80%   │    85%                 │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
│  内存占用：                                                  │
│  ┌───────────────────────────────────────────────────────┐ │
│  │  10000条缓存条目，每条约1KB                              │ │
│  │  ├─ 原始数据: ~10MB                                     │ │
│  │  ├─ Caffeine开销: +2MB (索引+统计)                      │ │
│  │  ├─ Guava开销: +5MB                                     │ │
│  │  └─ EhCache开销: +8MB (功能多)                          │ │
│  └───────────────────────────────────────────────────────┘ │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 功能对比

| 特性 | Caffeine | Guava | EhCache 3 | ConcurrentHashMap |
|------|----------|-------|-----------|-------------------|
| **淘汰策略** | W-TinyLFU | LRU | LRU/LFU/自定义 | 无 |
| **过期策略** | 支持 | 支持 | 支持 | 无 |
| **刷新机制** | 异步刷新 | 同步刷新 | 支持 | 无 |
| **异步加载** | 原生支持 | 不支持 | 支持 | 无 |
| **统计功能** | 详细 | 基础 | 详细 | 无 |
| **持久化** | 不支持 | 不支持 | 支持 | 无 |
| **分布式** | 不支持 | 不支持 | Terracotta | 无 |
| **内存效率** | 高 | 中 | 低 | 最高 |

---

## 五、最佳实践

### 5.1 配置建议

```
┌─────────────────────────────────────────────────────────────┐
│                    Caffeine最佳实践                          │
├─────────────────────────────────────────────────────────────┤
│                                                            │
│  1. 容量规划：                                               │
│  ├─ maximumSize: 根据JVM堆内存的10-20%估算                  │
│  │   例: 4GB堆内存 → 最大缓存条目 ~100万（假设每条1KB）       │
│  └─ 使用maximumWeight处理大小不均的数据                      │
│                                                            │
│  2. 过期策略选择：                                           │
│  ├─ expireAfterWrite: 数据不经常变化（配置、字典）            │
│  ├─ expireAfterAccess: 需要自动清理冷数据                    │
│  ├─ refreshAfterWrite: 需要保持数据新鲜，但允许短暂旧值        │
│  └─ 组合使用: refresh + expire，兼顾性能和时效性              │
│                                                            │
│  3. 加载器设计：                                             │
│  ├─ 异常处理: CacheLoader抛异常会传播给调用者                 │
│  ├─ 批量加载: 实现loadAll优化批量查询                         │
│  └─ 异步加载: 使用AsyncCache避免阻塞                         │
│                                                            │
│  4. 监控告警：                                               │
│  ├─ 命中率 < 80%: 检查缓存大小和过期策略                      │
│  ├─ 加载时间 > 100ms: 优化DB查询或加二级缓存                  │
│  └─ 淘汰率过高: 容量不足或过期时间过短                        │
│                                                            │
│  5. 常见问题：                                               │
│  ├─ 避免大对象缓存（>1MB）                                   │
│  ├─ 避免缓存频繁变化的数据                                   │
│  └─ 注意线程池隔离（刷新/过期使用ForkJoinPool）               │
│                                                            │
└─────────────────────────────────────────────────────────────┘
```

### 5.2 监控指标

```java
@Component
public class CacheMonitor {

    @Autowired
    private Cache<String, User> userCache;

    @Scheduled(fixedRate = 60000) // 每分钟输出
    public void printStats() {
        CacheStats stats = userCache.stats();

        log.info("Cache Stats: " +
            "hitRate={}, " +
            "hitCount={}, " +
            "missCount={}, " +
            "loadSuccessCount={}, " +
            "loadFailureCount={}, " +
            "totalLoadTime={}ms, " +
            "evictionCount={}",
            String.format("%.2f%%", stats.hitRate() * 100),
            stats.hitCount(),
            stats.missCount(),
            stats.loadSuccessCount(),
            stats.loadFailureCount(),
            stats.totalLoadTime() / 1000000,
            stats.evictionCount()
        );
    }
}
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [缓存设计模式](./缓存设计模式.md)
- [缓存一致性](./缓存一致性.md)

### 6.2 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| Redis | L2缓存 | Caffeine作为L1，Redis作为L2 |
| Guava | 前身 | Caffeine作者为Guava Cache作者 |
| JVM调优 | 配合 | 缓存大小需考虑GC影响 |

---

## 七、参考资源

### 7.1 官方资源

1. [Caffeine GitHub](https://github.com/ben-manes/caffeine)
2. [Caffeine Wiki](https://github.com/ben-manes/caffeine/wiki)

### 7.2 学习资料

1. [Design of a Modern Cache](http://highscalability.com/blog/2016/1/25/design-of-a-modern-cache.html)
2. [TinyLFU论文](https://dl.acm.org/doi/10.1145/3149371)

### 7.3 相关文档

- [缓存设计模式](./缓存设计模式.md)
- [Redis集群模式](./Redis集群模式.md)

---

**维护者**：分布式计算知识库团队
**最后更新**：2026年
