# JVM性能调优：GC/内存/编译器

## 核心概念

### 1. JVM内存模型

JVM内存管理是Java应用性能的核心，理解内存布局有助于优化决策。

**JVM内存结构**：

```
┌─────────────────────────────────────────────────────────────┐
│                    JVM内存结构                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │                 堆内存 (Heap)                        │   │
│  │  ┌─────────────────────────────────────────────┐   │   │
│  │  │          年轻代 (Young Generation)           │   │   │
│  │  │  ┌─────────┐  ┌─────────┐  ┌─────────┐     │   │   │
│  │  │  │  Eden   │  │ S0/S1   │  │ S0/S1   │     │   │   │
│  │  │  │  (8/10) │  │  (1/10) │  │  (1/10) │     │   │   │
│  │  │  └─────────┘  └─────────┘  └─────────┘     │   │   │
│  │  └─────────────────────────────────────────────┘   │   │
│  │  ┌─────────────────────────────────────────────┐   │   │
│  │  │          老年代 (Old Generation)             │   │   │
│  │  │    长期存活对象 / 大对象直接分配              │   │   │
│  │  └─────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │           元空间 (Metaspace) - Java 8+              │   │
│  │    类元数据、常量池、方法信息                        │   │
│  │    默认无上限，受限于物理内存                        │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │           直接内存 (Direct Memory)                  │   │
│  │    NIO Buffer、堆外内存分配                          │   │
│  │    通过 -XX:MaxDirectMemorySize 限制                │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
│  ┌─────────────────┐  ┌─────────────────┐                  │
│  │  JVM线程栈      │  │  本地方法栈      │                  │
│  │  -Xss 默认1MB   │  │  Native方法    │                  │
│  └─────────────────┘  └─────────────────┘                  │
│                                                             │
│  ┌─────────────────────────────────────────────────────┐   │
│  │           程序计数器 (PC Register)                  │   │
│  │    每个线程的当前执行位置                            │   │
│  └─────────────────────────────────────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**对象生命周期**：

```
对象分配 → Eden区 → Minor GC存活 → Survivor区 →
多次GC存活(默认15次) → 老年代 → Full GC
```

### 2. 垃圾回收器对比

**主流GC算法特性**：

| 收集器 | 算法 | 目标 | 适用场景 | 停顿时间 |
|--------|------|------|----------|----------|
| Serial | 复制/标记-整理 | 单线程 | 客户端/嵌入式 | 几十ms |
| Parallel | 复制/标记-整理 | 吞吐 | 后台计算 | 几百ms |
| CMS | 标记-清除 | 低延迟 | Web应用 | 几十ms |
| G1 | 标记-整理+复制 | 平衡 | 大堆均衡 | 几十ms |
| ZGC | 染色指针 | 超低延迟 | 超大堆 | <10ms |
| Shenandoah | Brooks指针 | 超低延迟 | 超大堆 | <10ms |

**G1收集器详解**：

```
G1 (Garbage First) 设计特点：

1. 区域化内存管理
   - 堆划分为多个Region (1-32MB)
   - Eden/Survivor/Old/Humongous Region

2. 可预测停顿
   - 用户设定停顿目标 (-XX:MaxGCPauseMillis)
   - 根据历史数据选择回收收益最大的Region

3. 混合回收
   - 并发标记 + 复制算法
   - 逐步回收老年代，避免Full GC

G1回收阶段：
┌──────────┬─────────────────────────────────────┐
│  阶段    │            描述                      │
├──────────┼─────────────────────────────────────┤
│ 初始标记 │ STW，标记GC Roots直接引用           │
│ 并发标记 │ 与用户线程并发，遍历对象图          │
│ 最终标记 │ STW，处理SATB队列                   │
│ 筛选回收 │ STW，复制存活对象，清空Region       │
└──────────┴─────────────────────────────────────┘
```

### 3. JIT编译器优化

**HotSpot JIT分层编译**：

```
Level 0: 解释执行
   ↓ 方法调用计数 > 阈值 (默认1500)
Level 1: C1简单编译 (客户端编译器)
   ↓ 方法调用计数 > 阈值 (默认10000)
Level 2-3: C1带Profiling编译
   ↓ 后台编译完成
Level 4: C2优化编译 (服务端编译器)

编译触发条件：
- 方法调用计数器 (Invocation Counter)
- 回边计数器 (Back Edge Counter, 循环)
```

**JIT优化技术**：

```
1. 方法内联 (Method Inlining)
   将小方法直接嵌入调用处，减少调用开销

2. 逃逸分析 (Escape Analysis)
   - 栈上分配：对象不逃逸，在栈分配
   - 锁消除：对象不逃逸，去除同步
   - 标量替换：对象拆分为基本类型

3. 热点代码优化
   - 去虚化 (Devirtualization)
   - 循环展开 (Loop Unrolling)
   - 范围检查消除
```

## 实践方法

### GC调优实践

**1. 内存大小配置**：

```bash
# 基础内存配置
-Xms8g -Xmx8g           # 堆初始和最大8GB，避免动态调整
-XX:MetaspaceSize=256m  # 元空间初始256MB
-XX:MaxMetaspaceSize=512m  # 元空间最大512MB
-Xss1m                  # 线程栈1MB
-XX:MaxDirectMemorySize=2g  # 直接内存2GB

# 年轻代配置
-XX:NewRatio=2          # 老年代:年轻代 = 2:1
# 或
-Xmn3g                  # 年轻代固定3GB
-XX:SurvivorRatio=8     # Eden:S0:S1 = 8:1:1
```

**2. G1收集器配置**：

```bash
# G1推荐配置（JDK 11+）
-XX:+UseG1GC
-XX:MaxGCPauseMillis=100    # 目标最大停顿100ms
-XX:G1HeapRegionSize=16m    # Region大小16MB
-XX:G1NewSizePercent=20     # 年轻代最小20%
-XX:G1MaxNewSizePercent=35  # 年轻代最大35%
-XX:G1ReservePercent=15     # 预留15%防止晋升失败
-XX:InitiatingHeapOccupancyPercent=45  # 老年代45%触发并发标记
-XX:G1MixedGCCountTarget=8  # 混合回收目标次数
-XX:G1MixedGCLiveThresholdPercent=85   # Region存活率>85%不回收

# 大堆配置（>16GB）
-XX:G1HeapRegionSize=32m
-XX:G1ConcRefinementThreads=8
```

**3. ZGC配置（JDK 15+）**：

```bash
# ZGC超低延迟配置
-XX:+UseZGC
-XX:+ZGenerational    # JDK 21+ 分代ZGC
-Xms16g -Xmx16g
-XX:SoftMaxHeapSize=12g  # 建议堆大小
-XX:ZCollectionInterval=5  # 强制GC间隔（秒）
-XX:ZAllocationSpikeTolerance=2  # 分配尖峰容忍度

# ZGC诊断
-XX:+ZProactive        # 主动GC
-Xlog:gc*:file=gc.log:time,uptime,level,tags:filecount=10,filesize=100m
```

**4. GC日志分析**：

```bash
# JDK 9+ 统一日志
-Xlog:gc*:file=gc.log:time,uptime,level,tags:filecount=10,filesize=100m

# 关键GC指标
# 1. GC频率
# 2. GC停顿时间
# 3. 内存回收效率
# 4. 晋升失败/并发模式失败
```

**GC日志分析脚本**：

```python
#!/usr/bin/env python3
import re
import sys
from collections import defaultdict

def parse_gc_log(log_file):
    gc_events = []

    # G1 GC日志模式
    g1_pattern = re.compile(
        r'\[(?P<time>[\d.]+)s\]\s+'
        r'\[(?P<phase>[^\]]+)\s+'
        r'(?P<duration>[\d.]+)ms\]'
    )

    with open(log_file) as f:
        for line in f:
            match = g1_pattern.search(line)
            if match:
                gc_events.append({
                    'time': float(match.group('time')),
                    'phase': match.group('phase'),
                    'duration': float(match.group('duration'))
                })

    return gc_events

def analyze_gc(gc_events):
    pause_events = [e for e in gc_events if 'Pause' in e['phase']]

    if not pause_events:
        print("未找到GC停顿事件")
        return

    durations = [e['duration'] for e in pause_events]

    print("=" * 60)
    print("GC停顿分析")
    print("=" * 60)
    print(f"GC次数: {len(pause_events)}")
    print(f"平均停顿: {sum(durations)/len(durations):.2f}ms")
    print(f"最大停顿: {max(durations):.2f}ms")
    print(f"P99停顿: {sorted(durations)[int(len(durations)*0.99)]:.2f}ms")
    print(f"P95停顿: {sorted(durations)[int(len(durations)*0.95)]:.2f}ms")

    # 按阶段统计
    phase_stats = defaultdict(list)
    for e in pause_events:
        phase_stats[e['phase']].append(e['duration'])

    print("\n各阶段停顿:")
    for phase, times in sorted(phase_stats.items()):
        avg = sum(times) / len(times)
        max_time = max(times)
        print(f"  {phase}: 次数={len(times)}, 平均={avg:.2f}ms, 最大={max_time:.2f}ms")

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <gc.log>")
        sys.exit(1)

    events = parse_gc_log(sys.argv[1])
    analyze_gc(events)
```

### 内存优化实践

**1. 对象分配优化**：

```java
// 优化前：大量临时对象
public String process(String input) {
    String result = "";
    for (String part : input.split(",")) {
        result += part.trim().toUpperCase();  // ❌ 每次循环创建新String
    }
    return result;
}

// 优化后：使用StringBuilder
public String process(String input) {
    StringBuilder sb = new StringBuilder(input.length());
    for (String part : input.split(",")) {
        sb.append(part.trim().toUpperCase());
    }
    return sb.toString();
}

// 优化后：预编译正则，避免重复创建
public class Validator {
    private static final Pattern EMAIL_PATTERN =
        Pattern.compile("^[A-Za-z0-9+_.-]+@(.+)$");  // ✓ 静态常量

    public boolean isValidEmail(String email) {
        return EMAIL_PATTERN.matcher(email).matches();
    }
}
```

**2. 集合大小预分配**：

```java
// 优化前：默认扩容
List<String> list = new ArrayList<>();  // 默认容量10
for (int i = 0; i < 10000; i++) {
    list.add(String.valueOf(i));  // 多次扩容：10→15→22→33→50→75→...
}

// 优化后：预估容量
List<String> list = new ArrayList<>(10000);  // ✓ 一次性分配
for (int i = 0; i < 10000; i++) {
    list.add(String.valueOf(i));
}

// HashMap预计算
int expectedSize = 10000;
// 负载因子0.75，计算所需初始容量
int initialCapacity = (int) (expectedSize / 0.75f + 1);
Map<String, Object> map = new HashMap<>(initialCapacity);
```

**3. 大对象和堆外内存**：

```java
// 直接内存分配（堆外）
ByteBuffer directBuffer = ByteBuffer.allocateDirect(1024 * 1024);  // 1MB

// 使用try-with-resources确保释放
public void processLargeFile(String path) throws IOException {
    try (FileChannel channel = FileChannel.open(Paths.get(path), StandardOpenOption.READ)) {
        ByteBuffer buffer = ByteBuffer.allocateDirect(8192);
        while (channel.read(buffer) > 0) {
            buffer.flip();
            process(buffer);
            buffer.clear();
        }
    }
}

// 监控直接内存使用
System.out.println("Max Direct Memory: " +
    sun.misc.VM.maxDirectMemory() / 1024 / 1024 + " MB");
```

### JIT编译优化

**1. 内联优化**：

```bash
# 查看JIT编译和内联
-XX:+PrintCompilation
-XX:+PrintInlining

# 内联参数调优
-XX:MaxInlineSize=35       # 方法大小<35字节内联
-XX:FreqInlineSize=325     # 热点方法<325字节内联
-XX:MaxInlineLevel=9       # 内联嵌套深度
-XX:MaxTrivialSize=6       # 简单方法<6字节必内联
```

**2. 逃逸分析优化**：

```bash
# 开启逃逸分析（JDK 8默认开启）
-XX:+DoEscapeAnalysis

# 开启锁消除
-XX:+EliminateLocks

# 开启栈上分配
-XX:+EliminateAllocations
```

**JIT优化示例**：

```java
// 锁消除示例
public String concat(String s1, String s2) {
    StringBuffer sb = new StringBuffer();  // sb不会逃逸
    sb.append(s1);  // 锁被消除
    sb.append(s2);  // 锁被消除
    return sb.toString();
}

// 栈上分配示例
public void createPoints() {
    for (int i = 0; i < 1000000; i++) {
        Point p = new Point(i, i);  // 可能栈上分配
        process(p);
    }
}
```

## 工具使用

### JVM监控工具

**1. jstat - JVM统计**：

```bash
# GC统计
jstat -gc <pid> 1000 10  # 每秒输出，共10次

# 输出字段说明
# S0C/S1C: Survivor区容量
# S0U/S1U: Survivor区使用
# EC/EU: Eden区容量/使用
# OC/OU: 老年代容量/使用
# MC/MU: 元空间容量/使用
# YGC/YGCT: Young GC次数/时间
# FGC/FGCT: Full GC次数/时间
# GCT: GC总时间

# 类加载统计
jstat -class <pid>

# 编译统计
jstat -compiler <pid>
```

**2. jmap - 内存分析**：

```bash
# 生成堆转储
jmap -dump:format=b,file=heap.hprof <pid>

# 堆摘要
jmap -heap <pid>

# 直方图（对象统计）
jmap -histo <pid> | head -30
jmap -histo:live <pid>  # 只统计存活对象

# 最终化对象
jmap -finalizerinfo <pid>
```

**3. 可视化工具**：

```bash
# JFR (Java Flight Recorder)
java -XX:StartFlightRecording=duration=60s,filename=recording.jfr MyApp

# 分析JFR
jfr print --events jdk.GCPhasePause recording.jfr

# VisualVM / JConsole
jvisualvm
jconsole <pid>

# async-profiler
./profiler.sh -d 60 -f profile.html <pid>
```

## 案例数据

### 电商系统GC优化案例

**优化前状况**：

```
配置：-Xms4g -Xmx4g -XX:+UseParallelGC

问题：
- Full GC频率：每10分钟一次
- Full GC耗时：3-5秒
- 高峰期OOM频繁
- P99延迟：2秒

GC日志分析：
[Full GC (Ergonomics) [PSYoungGen: 1234567K->0K(1536000K)]
 [ParOldGen: 2345678K->2345678K(2560000K)] 3660245K->2345678K(4096000K)
, [Metaspace: 45678K->45678K(1081344K)], 4.1234567 secs]
```

**优化方案**：

```bash
# 1. 切换到G1GC
-XX:+UseG1GC
-Xms8g -Xmx8g

# 2. 调优G1参数
-XX:MaxGCPauseMillis=100
-XX:G1HeapRegionSize=16m
-XX:InitiatingHeapOccupancyPercent=35
-XX:G1MixedGCCountTarget=4

# 3. 元空间扩容
-XX:MetaspaceSize=256m
-XX:MaxMetaspaceSize=512m

# 4. 代码优化（对象池）
```

**优化后效果**：

```
GC表现：
- Full GC：0次/天（混合回收替代）
- Young GC：平均20ms
- Mixed GC：平均50ms
- G1停顿：P99 < 80ms

业务指标：
- P99延迟：2秒 → 150ms
- 吞吐量：提升40%
- OOM：消除
```

### 大数据处理内存优化

**场景：Spark大数据作业**

**优化前**：

```
配置：-Xmx64g -XX:+UseG1GC
问题：GC时间占作业时间30%，Executor频繁OOM

分析：
- 大对象分配频繁（缓存块）
- 年轻代过小导致提前晋升
- 元空间泄漏
```

**优化配置**：

```bash
# Spark Executor JVM配置
spark.executor.extraJavaOptions="
  -XX:+UseG1GC
  -Xms32g -Xmx32g
  -XX:MaxGCPauseMillis=200
  -XX:G1HeapRegionSize=16m
  -XX:+UnlockDiagnosticVMOptions
  -XX:+DebugNonSafepoints
  -XX:+UseStringDeduplication  # 字符串去重
  -XX:MetaspaceSize=256m
  -XX:MaxMetaspaceSize=512m
  -XX:+AlwaysPreTouch  # 启动时分配所有内存
"

# 代码优化
conf.set("spark.serializer", "org.apache.spark.serializer.KryoSerializer")
conf.set("spark.kryo.registrationRequired", "false")
```

**优化效果**：

```
- GC时间占比：30% → 5%
- 作业执行时间：下降25%
- Executor OOM：消除
- 内存效率：提升35%
```

## 优化前后对比

| 优化项 | 优化前 | 优化后 | 改进 |
|--------|--------|--------|------|
| Full GC频率 | 6次/小时 | 0次/天 | 消除 |
| GC停顿P99 | 5秒 | 80ms | 98%↓ |
| 应用P99延迟 | 2秒 | 150ms | 92%↓ |
| 吞吐量 | 基准 | +40% | 显著提升 |
| 内存占用 | 4GB | 8GB（合理） | 可控 |
| OOM频率 | 频繁 | 0 | 消除 |

---

**总结**：JVM调优是一个系统工程，需要从内存配置、GC选择、代码优化、编译器优化多个维度综合考虑。合理的调优可以显著提升应用性能，但过度优化可能带来维护成本，应结合实际业务场景和监控数据进行渐进式优化。
