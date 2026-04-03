# JVM与GC调优 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：✅ 已完成

---

## 📋 执行摘要

JVM调优是Java应用性能优化的核心环节。理解JVM内存模型、选择合适的GC算法、分析GC日志、识别内存泄漏，对于保障应用稳定高效运行至关重要。

---

## 一、核心概念

### 1.1 定义与原理

**JVM（Java Virtual Machine）**：Java虚拟机，负责将字节码转换为机器码执行，提供内存管理、垃圾回收、线程管理等核心功能。

**GC（Garbage Collection）**：垃圾回收机制，自动管理堆内存的生命周期，回收不再使用的对象，防止内存泄漏。

**核心原理**：
- **自动内存管理**：程序员无需手动分配和释放内存
- **分代回收**：根据对象存活周期采用不同回收策略
- **可达性分析**：通过GC Roots判断对象是否存活
- **Stop-The-World**：部分GC阶段需要暂停应用线程

### 1.2 关键特性

- **跨平台**：一次编写，到处运行
- **自动内存管理**：降低内存泄漏风险
- **性能可调优**：丰富的参数控制运行时行为
- **完善的监控**：JMX、JVMTI等监控接口

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 大型企业应用 | ⭐⭐⭐⭐⭐ | Java生态成熟，适合复杂业务 |
| 高并发Web服务 | ⭐⭐⭐⭐⭐ | JVM调优可显著提升吞吐量 |
| 大数据处理 | ⭐⭐⭐⭐⭐ | Hadoop/Spark等基于JVM |
| 低延迟交易系统 | ⭐⭐⭐⭐ | 需要精细化GC调优 |
| 资源受限环境 | ⭐⭐⭐ | JVM本身有一定资源开销 |

---

## 二、技术细节

### 2.1 JVM内存模型

#### 2.1.1 运行时数据区

```
┌─────────────────────────────────────────────────────────────┐
│                      JVM内存结构                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                  线程私有区域                        │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │   │
│  │  │  程序计数器  │  │  虚拟机栈   │  │  本地方法栈  │ │   │
│  │  │   (PC)      │  │ (VM Stack)  │  │(Native Stack)│ │   │
│  │  │  线程执行位置 │  │  方法调用栈  │  │  JNI方法调用 │ │   │
│  │  │  无OOM      │  │  StackOverflow│  │              │ │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘ │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                  线程共享区域                        │   │
│  │                                                     │   │
│  │  ┌─────────────────────────────────────────────┐   │   │
│  │  │                  堆 (Heap)                   │   │   │
│  │  │  ┌─────────────┬─────────────┬─────────────┐ │   │   │
│  │  │  │   年轻代    │    老年代    │   元空间    │ │   │   │
│  │  │  │  (Young)    │   (Old)     │ (Metaspace) │ │   │   │
│  │  │  │  Eden       │             │  类元数据    │ │   │   │
│  │  │  │  S0/S1      │  长期存活对象 │  常量池      │ │   │   │
│  │  │  │  (Survivor) │             │  (本地内存)  │ │   │   │
│  │  │  └─────────────┴─────────────┴─────────────┘ │   │   │
│  │  │  -Xms/-Xmx                                  │   │   │
│  │  └─────────────────────────────────────────────┘   │   │
│  │                                                     │   │
│  │  ┌─────────────────────────────────────────────┐   │   │
│  │  │              直接内存 (Direct Memory)        │   │   │
│  │  │         NIO使用，不受堆大小限制               │   │   │
│  │  │            -XX:MaxDirectMemorySize           │   │   │
│  │  └─────────────────────────────────────────────┘   │   │
│  │                                                     │   │
│  │  ┌─────────────────────────────────────────────┐   │   │
│  │  │              代码缓存 (Code Cache)           │   │   │
│  │  │         JIT编译后的机器码缓存                 │   │   │
│  │  │       -XX:ReservedCodeCacheSize              │   │   │
│  │  └─────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.1.2 堆内存详细结构

```
┌─────────────────────────────────────────────────────────┐
│                      堆内存布局                           │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  年轻代 (Young Generation)                               │
│  ┌─────────────────────────────────────────────────┐   │
│  │  Eden区          │  Survivor 0  │  Survivor 1   │   │
│  │  (8/10)          │  (1/10)      │  (1/10)       │   │
│  │                  │              │               │   │
│  │  新对象分配区域   │  From Space  │  To Space     │   │
│  │                  │              │               │   │
│  │  新生代GC (Minor GC/YGC)                         │   │
│  │  - 频繁执行，速度快                              │   │
│  │  - Eden满时触发                                  │   │
│  │  - 存活对象复制到Survivor                        │   │
│  │  - 年龄计数器增加                                │   │
│  └─────────────────────────────────────────────────┘   │
│                                                         │
│  老年代 (Old Generation)                                │
│  ┌─────────────────────────────────────────────────┐   │
│  │                                                 │   │
│  │     长期存活对象 / 大对象直接进入                │   │
│  │                                                 │   │
│  │     老年代GC (Major GC/Full GC)                 │   │
│  │     - 较少执行，速度慢                           │   │
│  │     - 老年代满时触发                             │   │
│  │     - 通常伴随整个堆的回收                       │   │
│  │                                                 │   │
│  └─────────────────────────────────────────────────┘   │
│                                                         │
│  晋升规则：                                              │
│  - 年龄阈值（默认15）：-XX:MaxTenuringThreshold        │
│  - 动态年龄判断：Survivor中相同年龄对象大小总和超过      │
│    Survivor空间一半时，大于等于该年龄的对象晋升          │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

#### 2.1.3 常用内存参数

| 参数 | 说明 | 示例 |
|-----|------|------|
| `-Xms` | 堆初始大小 | `-Xms4g` |
| `-Xmx` | 堆最大大小 | `-Xmx4g` |
| `-Xmn` | 年轻代大小 | `-Xmn1.5g` |
| `-XX:NewRatio` | 老年代/年轻代比例 | `-XX:NewRatio=2` |
| `-XX:SurvivorRatio` | Eden/Survivor比例 | `-XX:SurvivorRatio=8` |
| `-XX:MetaspaceSize` | 元空间初始大小 | `-XX:MetaspaceSize=256m` |
| `-XX:MaxMetaspaceSize` | 元空间最大大小 | `-XX:MaxMetaspaceSize=512m` |
| `-Xss` | 线程栈大小 | `-Xss1m` |

### 2.2 GC算法对比

#### 2.2.1 经典垃圾收集器

```
┌─────────────────────────────────────────────────────────────┐
│                    HotSpot垃圾收集器                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  串行收集器 (Serial)                                         │
│  ├── Serial: 年轻代，单线程，复制算法                         │
│  └── Serial Old: 老年代，单线程，标记-整理                    │
│  适用：客户端/单核CPU环境                                     │
│                                                             │
│  并行收集器 (Parallel/Throughput)                            │
│  ├── Parallel Scavenge: 年轻代，多线程，复制算法              │
│  └── Parallel Old: 老年代，多线程，标记-整理                  │
│  目标：高吞吐量                                               │
│  适用：后台计算，批量处理                                     │
│                                                             │
│  CMS (Concurrent Mark Sweep)                                 │
│  ├── ParNew: 年轻代，Serial的多线程版本                       │
│  └── CMS: 老年代，并发低停顿，标记-清除                       │
│  目标：低延迟                                                 │
│  缺点：碎片问题，浮动垃圾，CPU敏感                            │
│  适用：Web应用，交互式系统                                    │
│  ⚠️ JDK14中已移除                                             │
│                                                             │
│  G1 (Garbage First)                                          │
│  └── 整堆收集器，分区模型，优先回收垃圾最多区域               │
│  目标：平衡吞吐量和延迟                                       │
│  特点：可预测的停顿时间，无碎片                               │
│  适用：大堆内存（>4GB），JDK9+默认                            │
│                                                             │
│  ZGC (Z Garbage Collector)                                   │
│  └── 整堆收集器，着色指针，读屏障，并发整理                   │
│  目标：超低延迟（<10ms），可扩展性                            │
│  特点：TB级堆，亚毫秒级停顿                                   │
│  适用：大内存，低延迟要求                                     │
│  要求：JDK11+                                                 │
│                                                             │
│  Shenandoah                                                  │
│  └── OpenJDK特性，与ZGC类似目标                              │
│  特点：并发压缩，低延迟                                       │
│  要求：JDK12+，或Red Hat OpenJDK                              │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.2.2 算法原理对比

| 收集器 | 年轻代算法 | 老年代算法 | 停顿时间 | 吞吐量 | 内存碎片 | JDK版本 |
|-------|-----------|-----------|---------|--------|---------|---------|
| Serial | 复制 | 标记-整理 | 高 | 低 | 无 | 所有 |
| Parallel | 复制 | 标记-整理 | 中 | 高 | 无 | 所有 |
| CMS | 复制 | 标记-清除 | 低 | 中 | 有 | 8-14 |
| G1 | 复制 | 标记-整理 | 低 | 高 | 无 | 7+ |
| ZGC | 复制 | 并发标记-整理 | 极低 | 中 | 无 | 11+ |
| Shenandoah | 复制 | 并发标记-整理 | 极低 | 中 | 无 | 12+ |

#### 2.2.3 收集器选择指南

```
选择决策树：

JDK版本?
├── JDK 8
│   ├── 堆 < 4GB → Parallel GC
│   ├── 需要低延迟 → CMS (JDK14前)
│   └── 堆 > 4GB → G1
│
├── JDK 9-10
│   └── G1 (默认)
│
└── JDK 11+
    ├── 超低延迟要求 (<10ms) → ZGC/Shenandoah
    ├── 大堆 (>32GB) → ZGC
    └── 一般场景 → G1

参数配置示例：

# G1收集器 (推荐用于大多数应用)
-XX:+UseG1GC
-XX:MaxGCPauseMillis=200
-XX:G1HeapRegionSize=16m
-XX:InitiatingHeapOccupancyPercent=45

# ZGC收集器 (超低延迟)
-XX:+UseZGC
-XX:ZCollectionInterval=5
-XX:ZAllocationSpikeTolerance=2

# Parallel收集器 (高吞吐量)
-XX:+UseParallelGC
-XX:+UseParallelOldGC
-XX:ParallelGCThreads=8
-XX:MaxGCPauseMillis=500
```

### 2.3 GC日志分析

#### 2.3.1 GC日志参数配置

```bash
# JDK 9+ 统一日志格式
-Xlog:gc*:file=/var/log/app/gc.log:time,uptime,level,tags:filecount=10,filesize=100m

# 详细说明：
# gc*          - 输出所有gc相关日志
# file=...     - 日志文件路径
# time         - 显示时间戳
# uptime       - 显示JVM运行时间
# level        - 显示日志级别
# tags         - 显示标签
# filecount    - 保留文件数量
# filesize     - 单个文件大小限制

# JDK 8 日志参数（已废弃但仍常用）
-XX:+PrintGCDetails
-XX:+PrintGCDateStamps
-XX:+PrintGCTimeStamps
-Xloggc:/var/log/app/gc.log
-XX:+UseGCLogFileRotation
-XX:NumberOfGCLogFiles=10
-XX:GCLogFileSize=100M
```

#### 2.3.2 G1 GC日志分析

```
示例日志：
[2026-01-15T10:23:45.123+0800][gc,start] GC(42) Pause Young (Normal) (G1 Evacuation Pause)
[2026-01-15T10:23:45.124+0800][gc,task] GC(42) Using 8 workers of 8 for evacuation
[2026-01-15T10:23:45.145+0800][gc,phases] GC(42) Pre Evacuate Collection Set: 0.2ms
[2026-01-15T10:23:45.145+0800][gc,phases] GC(42) Evacuate Collection Set: 18.5ms
[2026-01-15T10:23:45.145+0800][gc,phases] GC(42) Post Evacuate Collection Set: 2.1ms
[2026-01-15T10:23:45.145+0800][gc,heap] GC(42) Eden regions: 120->0(125)
[2026-01-15T10:23:45.145+0800][gc,heap] GC(42) Survivor regions: 15->20(20)
[2026-01-15T10:23:45.145+0800][gc,heap] GC(42) Old regions: 200->205
[2026-01-15T10:23:45.145+0800][gc,heap] GC(42) Humongous regions: 5->3
[2026-01-15T10:23:45.145+0800][gc,metaspace] GC(42) Metaspace: 120M->120M(256M)
[2026-01-15T10:23:45.145+0800][gc] GC(42) Pause Young (Normal) (G1 Evacuation Pause) 
    1024M->452M(4096M) 21.234ms
    User=0.15s Sys=0.02s Real=0.02s

关键指标解读：
┌─────────────────┬──────────────────────────────────────────┐
│ 字段            │ 含义                                      │
├─────────────────┼──────────────────────────────────────────┤
│ GC(42)          │ 第42次GC                                 │
│ Pause Young     │ 年轻代GC（还有Mixed/Full）                │
│ 8 workers       │ 使用8个GC线程                             │
│ Evacuate        │ 复制存活对象耗时18.5ms（主要耗时阶段）      │
│ Eden 120->0     │ Eden区从120个Region清空                   │
│ Survivor 15->20 │ Survivor区增加到20个Region                │
│ Old 200->205    │ 老年代增加5个Region（晋升）               │
│ 1024M->452M     │ GC前堆使用1024M，GC后452M                 │
│ 21.234ms        │ STW暂停时间                               │
│ User/Real=7.5   │ 并行效率（8核满负荷约8倍）                 │
└─────────────────┴──────────────────────────────────────────┘
```

#### 2.3.3 使用工具分析

```bash
# gceasy.io - 在线GC日志分析
# 上传gc.log文件，获取可视化报告

# GCViewer - 本地分析工具
java -jar gcviewer.jar gc.log

# 关键指标关注：
# 1. 吞吐量 = (运行时间 - GC时间) / 运行时间 > 95%
# 2. 平均GC停顿时间 < 目标值（如200ms）
# 3. 最大GC停顿时间 < 容忍值（如1s）
# 4. GC频率是否在合理范围
```

### 2.4 调优参数

#### 2.4.1 G1调优参数详解

| 参数 | 默认值 | 说明 | 调优建议 |
|-----|-------|------|---------|
| `-XX:MaxGCPauseMillis` | 200 | 目标最大停顿时间 | 根据SLA调整，不要<50ms |
| `-XX:G1HeapRegionSize` | 根据堆大小计算 | 每个Region大小 | 1-32MB，2的幂 |
| `-XX:InitiatingHeapOccupancyPercent` | 45 | 触发并发标记的堆占用率 | 降低可减少Full GC |
| `-XX:G1MixedGCCountTarget` | 8 | 混合GC的目标次数 | 增加可减少每次回收量 |
| `-XX:G1ReservePercent` | 10 | 保留内存百分比 | 防止晋升失败 |
| `-XX:MaxDirectMemorySize` | 与堆相同 | 直接内存上限 | NIO应用需关注 |

#### 2.4.2 常见问题调优

```bash
# 问题1: Full GC频繁
# 原因：老年代空间不足或晋升过快
# 解决：
-XX:G1HeapRegionSize=16m          # 增大Region
-XX:InitiatingHeapOccupancyPercent=35  # 提前触发并发标记
-Xmx适当增大                       # 增加堆大小

# 问题2: GC停顿时间过长
# 解决：
-XX:MaxGCPauseMillis=100          # 降低目标停顿
-XX:G1MixedGCCountTarget=16       # 分散混合GC压力
-XX:+UseStringDeduplication       # 开启字符串去重

# 问题3: 内存使用率高但GC正常
# 可能：存在内存泄漏或缓存过大
# 排查：
-XX:+HeapDumpOnOutOfMemoryError
-XX:HeapDumpPath=/var/log/app/
```

### 2.5 内存泄漏排查

#### 2.5.1 排查流程

```
┌─────────────────────────────────────────────────────────────┐
│                    内存泄漏排查流程                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. 确认泄漏症状                                            │
│     ├── 堆内存持续增长，GC后不回退                           │
│     ├── Old区占用率持续上升                                  │
│     └── 最终出现OOM或频繁Full GC                             │
│                                                             │
│  2. 获取内存快照                                             │
│     ├── 自动：-XX:+HeapDumpOnOutOfMemoryError               │
│     ├── 手动：jmap -dump:format=b,file=... <pid>            │
│     └── Arthas：heapdump /tmp/dump.hprof                    │
│                                                             │
│  3. 分析堆转储                                               │
│     ├── 工具：Eclipse MAT / VisualVM / JProfiler            │
│     ├── 查看Dominators Tree（支配树）                        │
│     ├── 查看Leak Suspects（泄漏嫌疑）                        │
│     └── 对比多个时间点的histogram                            │
│                                                             │
│  4. 定位问题代码                                             │
│     ├── 找到占用内存最大的对象类型                           │
│     ├── 查看引用链（GC Root路径）                            │
│     └── 结合代码分析生命周期是否合理                         │
│                                                             │
│  5. 验证修复                                                 │
│     ├── 修复代码后重新部署                                   │
│     └── 监控确认内存增长恢复正常                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.5.2 常见内存泄漏场景

| 场景 | 症状 | 解决方案 |
|-----|------|---------|
| 静态集合持有 | 类级别Map/List持续增长 | 使用WeakReference或定期清理 |
| 未关闭资源 | 文件/连接/流未关闭 | try-with-resources |
| 监听器未移除 | 观察者模式内存泄漏 | 及时removeListener |
| ThreadLocal未清理 | 线程池场景变量残留 | 用完即remove |
| 缓存无限增长 | 缓存无过期策略 | 使用Guava Cache/Caffeine |
| 大对象分配 | 老年代快速填满 | 优化对象结构，分页处理 |

#### 2.5.3 MAT分析示例

```
Eclipse MAT关键视图：

1. Histogram（直方图）
   - 按类统计实例数和占用内存
   - 可分组查看（Group by class loader）

2. Dominator Tree（支配树）
   - 显示对象的支配关系
   - 快速找到占用内存最大的对象

3. Leak Suspects Report（泄漏嫌疑报告）
   - 自动分析潜在的内存泄漏点
   - 提供Problem Suspect和简要分析

4. Path to GC Roots（到GC Root的路径）
   - 查看为什么对象没有被回收
   - 关键：exclude弱引用/软引用

分析步骤：
1. 打开hprof文件
2. 查看Leak Suspects，定位嫌疑对象
3. 在Dominator Tree中找到该对象
4. Path to GC Roots查看引用链
5. 结合代码定位问题
```

---

## 三、系统对比

### 3.1 GC收集器特性对比

| 特性 | Serial | Parallel | CMS | G1 | ZGC | Shenandoah |
|-----|--------|----------|-----|-----|-----|-----------|
| 停顿时间 | >1s | 数百ms | <100ms | <200ms | <10ms | <10ms |
| 最大堆 | 百MB级 | 几十GB | 几十GB | 几十GB | TB级 | TB级 |
| 最小JDK | 1.3 | 1.4 | 5 | 7 | 11 | 12 |
| 内存开销 | 低 | 中 | 高 | 高 | 高 | 高 |
| CPU开销 | 低 | 中 | 高 | 中 | 中 | 中 |
| 适用场景 | 客户端 | 批处理 | Web应用 | 通用 | 金融/游戏 | 金融/游戏 |

---

## 四、实践指南

### 4.1 JVM参数模板

```bash
# ============================================
# 通用生产环境JVM参数模板
# ============================================

# ----- 堆内存配置 -----
-Xms4g                          # 初始堆大小
-Xmx4g                          # 最大堆大小（与初始相同避免动态调整）
-XX:MetaspaceSize=256m          # 元空间初始
-XX:MaxMetaspaceSize=512m       # 元空间最大
-Xss512k                        # 线程栈大小

# ----- GC配置 (G1推荐) -----
-XX:+UseG1GC                    # 使用G1收集器
-XX:MaxGCPauseMillis=200        # 目标最大停顿200ms
-XX:G1HeapRegionSize=16m        # Region大小
-XX:InitiatingHeapOccupancyPercent=45  # 触发并发标记阈值

# ----- GC日志 -----
-Xlog:gc*:file=/var/log/app/gc.log:time,uptime,level,tags:filecount=10,filesize=100m

# ----- OOM处理 -----
-XX:+HeapDumpOnOutOfMemoryError
-XX:HeapDumpPath=/var/log/app/heapdump.hprof
-XX:OnOutOfMemoryError="kill -9 %p"

# ----- 性能优化 -----
-XX:+UseStringDeduplication     # 字符串去重（G1）
-XX:+AlwaysPreTouch             # 启动时分配所有内存
-XX:+DisableExplicitGC          # 禁止System.gc()

# ----- 调试 (生产环境慎用) -----
# -XX:+PrintFlagsFinal          # 打印最终参数
# -XX:+PrintCommandLineFlags    # 打印命令行参数
# -XX:NativeMemoryTracking=summary
```

### 4.2 最佳实践

1. **堆大小设置**
   - Xms = Xmx，避免运行时扩容
   - 堆大小不超过物理内存的70%
   - 容器环境考虑cgroup限制

2. **GC选择**
   - JDK8: 小堆Parallel，大堆G1
   - JDK11+: 默认G1，低延迟选ZGC
   - 避免使用已废弃的CMS

3. **监控告警**
   - GC频率和停顿时间
   - 堆内存使用趋势
   - Full GC次数（应接近0）

4. **容器化注意事项**
   ```bash
   # 识别容器限制
   -XX:+UseContainerSupport
   -XX:InitialRAMPercentage=50.0
   -XX:MaxRAMPercentage=75.0
   
   # 避免的问题
   # - 不设置Xmx导致容器OOMKilled
   # - 不识别CPU限制导致GC线程过多
   ```

### 4.3 常见问题

**Q1: 如何选择堆大小？**
A: 根据活跃数据量估算，通常活跃数据的2-4倍。通过压测和监控调整。

**Q2: G1目标停顿时间设置多少合适？**
A: 根据业务SLA，一般100-300ms。设置过低会导致GC过于频繁，影响吞吐量。

**Q3: 为什么设置了Xmx容器还是被OOMKill？**
A: JVM内存不仅包括堆，还有元空间、直接内存、线程栈等。需设置-XX:MaxRAMPercentage。

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [Java语言基础](../03-language/Java语言基础.md)
- [分布式系统基础](../01-architecture/分布式系统基础.md)

### 6.2 下游应用

- [压力测试与基准测试](./压力测试与基准测试.md)
- [性能监控与Profiling](../11-observability/性能监控与Profiling.md)
- [应用诊断与故障排查](../11-observability/应用诊断与故障排查.md)

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| 容器化 | 影响 | 容器环境需特殊配置JVM参数 |
| 微服务 | 场景 | 微服务架构下JVM进程数量增加 |
| APM | 配合 | APM工具监控JVM指标 |

---

## 七、参考资源

### 7.1 官方文档

1. [Oracle JVM Tuning Guide](https://docs.oracle.com/en/java/javase/17/gctuning/)
2. [OpenJDK GC Tuning](https://wiki.openjdk.org/display/zgc/Main)
3. [G1 GC论文](https://dl.acm.org/doi/10.1145/1028976.1028979)

### 7.2 学习资料

1. 《深入理解Java虚拟机》- 周志明
2. 《Java Performance》- Scott Oaks
3. [Plumbr GC Handbook](https://plumbr.io/handbook)

### 7.3 开源工具

1. [Eclipse MAT](https://www.eclipse.org/mat/) - 内存分析
2. [GCViewer](https://github.com/chewiebug/GCViewer) - GC日志分析
3. [Async-profiler](https://github.com/jvm-profiling-tools/async-profiler) - 性能分析
4. [Arthas](https://arthas.aliyun.com/) - 阿里巴巴Java诊断工具

### 7.4 相关文档

- [压力测试与基准测试](./压力测试与基准测试.md)
- [性能监控与Profiling](../11-observability/性能监控与Profiling.md)
- [应用诊断与故障排查](../11-observability/应用诊断与故障排查.md)

---

**维护者**：项目团队
**最后更新**：2026年
