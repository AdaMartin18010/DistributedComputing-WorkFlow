# YARN 资源管理详解

## 1. 架构概述

Apache Hadoop YARN（Yet Another Resource Negotiator）是一个通用的分布式资源管理系统，为上层应用提供统一的资源管理和调度服务。它将资源管理和作业调度/监控分离为独立的守护进程。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    YARN 架构                                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    ResourceManager (RM)                        │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │   Scheduler │  │Applications │  │ ResourceManager     │   │ │
│  │  │   (调度器)   │  │   Manager   │  │     HA (Active/     │   │ │
│  │  │             │  │  (应用管理)  │  │     Standby)        │   │ │
│  │  │ - 纯调度器   │  │             │  │                     │   │ │
│  │  │ - 不跟踪应用 │  │ - 启动 AM    │  │ - ZooKeeper         │   │ │
│  │  │   状态      │  │ - 监控 AM    │  │ - 自动故障转移      │   │ │
│  │  │ - 支持多种  │  │ - 失败重启   │  │                     │   │ │
│  │  │   调度器    │  │             │  │                     │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  └───────────────────────────────┬───────────────────────────────┘ │
│                                  │                                  │
│           ┌──────────────────────┼──────────────────────┐          │
│           │                      │                      │          │
│           ▼                      ▼                      ▼          │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐│
│  │  NodeManager 1  │    │  NodeManager 2  │    │  NodeManager N  ││
│  │  ┌───────────┐  │    │  ┌───────────┐  │    │  ┌───────────┐  ││
│  │  │ Container │  │    │  │ Container │  │    │  │ Container │  ││
│  │  │ Container │  │    │  │ Container │  │    │  │ Container │  ││
│  │  │ Container │  │    │  │ Container │  │    │  │ Container │  ││
│  │  └───────────┘  │    │  └───────────┘  │    │  └───────────┘  ││
│  │                 │    │                 │    │                 ││
│  │  - 资源监控     │    │  - 资源监控     │    │  - 资源监控     ││
│  │  - 容器管理     │    │  - 容器管理     │    │  - 容器管理     ││
│  │  - 心跳汇报     │    │  - 心跳汇报     │    │  - 心跳汇报     ││
│  └─────────────────┘    └─────────────────┘    └─────────────────┘│
│                                                                     │
│  Container: YARN 的资源分配单元，包含 CPU、内存等资源                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.1 YARN 应用执行流程

```
┌─────────────────────────────────────────────────────────────────────┐
│                  YARN 应用提交流程                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Client           RM           Scheduler         NM          AM     │
│    │              │                │              │            │     │
│    │  1. submit   │                │              │            │     │
│    │─────────────▶│                │              │            │     │
│    │              │  2. allocate   │              │            │     │
│    │              │───────────────────────────────▶│            │     │
│    │              │                │              │            │     │
│    │              │                │  3. launch   │            │     │
│    │              │                │◀─────────────│            │     │
│    │              │                │              │            │     │
│    │              │                │              │ 4. start   │     │
│    │              │                │              │───────────▶│     │
│    │              │                │              │            │     │
│    │              │  5. register   │              │            │     │
│    │              │◀───────────────┼──────────────┼────────────│     │
│    │              │                │              │            │     │
│    │              │  6. request    │              │            │     │
│    │              │◀───────────────┼──────────────┼────────────│     │
│    │              │                │              │            │     │
│    │              │  7. allocate   │              │            │     │
│    │              │───────────────────────────────▶│            │     │
│    │              │                │              │            │     │
│    │              │                │  8. launch   │            │     │
│    │              │                │◀─────────────│            │     │
│    │              │                │              │ 9. run     │     │
│    │              │                │              │───────────▶│     │
│    │              │                │              │            │     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. 调度器

YARN 提供三种调度器，满足不同场景的资源调度需求。

```
┌─────────────────────────────────────────────────────────────────────┐
│                    YARN 调度器对比                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1. FIFO Scheduler (先进先出)                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Queue: Job1 ──▶ Job2 ──▶ Job3 ──▶ Job4                    │   │
│  │         (Run)    (Wait)   (Wait)   (Wait)                   │   │
│  │                                                             │   │
│  │  特点：简单，但大作业会阻塞小作业                              │   │
│  │  适用：测试环境、小规模集群                                    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  2. Capacity Scheduler (容量调度)                                   │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Queue A (40%)        Queue B (40%)        Queue C (20%)   │   │
│  │  ┌───────────┐        ┌───────────┐        ┌───────────┐   │   │
│  │  │ Job A1    │        │ Job B1    │        │ Job C1    │   │   │
│  │  │ Job A2    │        │ Job B2    │        │           │   │   │
│  │  └───────────┘        └───────────┘        └───────────┘   │   │
│  │                                                             │   │
│  │  特点：多队列，弹性容量，支持优先级                             │   │
│  │  适用：多租户集群、生产环境                                    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  3. Fair Scheduler (公平调度)                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  User A        User B        User C                        │   │
│  │  ┌────────┐   ┌────────┐   ┌────────┐                      │   │
│  │  │ 33%    │   │ 33%    │   │ 33%    │  ← 资源平均分配        │   │
│  │  │ Job A1 │   │ Job B1 │   │ Job C1 │                      │   │
│  │  │ Job A2 │   │        │   │        │                      │   │
│  │  │ (17%)  │   │ (33%)  │   │ (33%)  │  ← 内部公平分配        │   │
│  │  └────────┘   └────────┘   └────────┘                      │   │
│  │                                                             │   │
│  │  特点：公平分配，支持抢占，资源池化                             │   │
│  │  适用：共享集群、交互式查询                                    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.1 Capacity Scheduler 配置

```xml
<!-- capacity-scheduler.xml -->
<property>
    <name>yarn.scheduler.capacity.root.queues</name>
    <value>default,production,development</value>
</property>

<!-- 默认队列 -->
<property>
    <name>yarn.scheduler.capacity.root.default.capacity</name>
    <value>20</value>
</property>
<property>
    <name>yarn.scheduler.capacity.root.default.maximum-capacity</name>
    <value>50</value>
</property>

<!-- 生产队列 -->
<property>
    <name>yarn.scheduler.capacity.root.production.capacity</name>
    <value>50</value>
</property>
<property>
    <name>yarn.scheduler.capacity.root.production.maximum-capacity</name>
    <value>80</value>
</property>
<property>
    <name>yarn.scheduler.capacity.root.production.state</name>
    <value>RUNNING</value>
</property>
<property>
    <name>yarn.scheduler.capacity.root.production.acl_submit_applications</name>
    <value>produser1,produser2</value>
</property>

<!-- 开发队列 -->
<property>
    <name>yarn.scheduler.capacity.root.development.capacity</name>
    <value>30</value>
</property>
<property>
    <name>yarn.scheduler.capacity.root.development.maximum-capacity</name>
    <value>50</value>
</property>

<!-- 资源计算模式 -->
<property>
    <name>yarn.scheduler.capacity.resource-calculator</name>
    <value>org.apache.hadoop.yarn.util.resource.DominantResourceCalculator</value>
</property>
```

### 2.2 Fair Scheduler 配置

```xml
<!-- fair-scheduler.xml -->
<allocations>
    <!-- 默认队列设置 -->
    <defaultQueueSchedulingPolicy>fair</defaultQueueSchedulingPolicy>

    <!-- 用户队列 -->
    <user name="alice">
        <maxRunningApps>10</maxRunningApps>
    </user>
    <user name="bob">
        <maxRunningApps>5</maxRunningApps>
    </user>

    <!-- 队列定义 -->
    <queue name="production">
        <weight>4.0</weight>
        <minResources>1024mb,2vcores</minResources>
        <maxResources>8192mb,8vcores</maxResources>
        <maxRunningApps>50</maxRunningApps>
        <schedulingPolicy>fifo</schedulingPolicy>
    </queue>

    <queue name="development">
        <weight>2.0</weight>
        <maxResources>4096mb,4vcores</maxResources>
        <schedulingPolicy>fair</schedulingPolicy>
    </queue>

    <queue name="default">
        <weight>1.0</weight>
    </queue>

    <!-- 队列放置规则 -->
    <queuePlacementPolicy>
        <rule name="specified" create="false"/>
        <rule name="nestedUserQueue">
            <rule name="primaryGroup" create="false"/>
        </rule>
        <rule name="default" queue="default"/>
    </queuePlacementPolicy>
</allocations>
```

## 3. 资源配置

### 3.1 NodeManager 配置

```xml
<!-- yarn-site.xml -->
<!-- NodeManager 资源配置 -->
<property>
    <name>yarn.nodemanager.resource.memory-mb</name>
    <value>65536</value>
    <description>NodeManager 管理的总内存(MB)</description>
</property>

<property>
    <name>yarn.nodemanager.resource.cpu-vcores</name>
    <value>16</value>
    <description>NodeManager 管理的总 vcore 数</description>
</property>

<!-- 容器资源限制 -->
<property>
    <name>yarn.scheduler.minimum-allocation-mb</name>
    <value>1024</value>
    <description>容器最小内存分配(MB)</description>
</property>

<property>
    <name>yarn.scheduler.maximum-allocation-mb</name>
    <value>32768</value>
    <description>容器最大内存分配(MB)</description>
</property>

<property>
    <name>yarn.scheduler.minimum-allocation-vcores</name>
    <value>1</value>
    <description>容器最小 vcore 分配</description>
</property>

<property>
    <name>yarn.scheduler.maximum-allocation-vcores</name>
    <value>8</value>
    <description>容器最大 vcore 分配</description>
</property>

<!-- 内存增量 -->
<property>
    <name>yarn.scheduler.increment-allocation-mb</name>
    <value>512</value>
</property>
```

### 3.2 应用资源配置

```bash
# 提交 MapReduce 作业
hadoop jar app.jar \
    -Dmapreduce.map.memory.mb=2048 \
    -Dmapreduce.map.java.opts=-Xmx1638m \
    -Dmapreduce.reduce.memory.mb=4096 \
    -Dmapreduce.reduce.java.opts=-Xmx3276m \
    -Dmapreduce.job.queuename=production \
    MainClass input output

# 提交 Spark 作业
spark-submit \
    --master yarn \
    --deploy-mode cluster \
    --queue production \
    --driver-memory 4g \
    --driver-cores 2 \
    --executor-memory 8g \
    --executor-cores 4 \
    --num-executors 10 \
    application.jar
```

## 4. 高可用配置

```xml
<!-- yarn-site.xml -->
<!-- ResourceManager HA -->
<property>
    <name>yarn.resourcemanager.ha.enabled</name>
    <value>true</value>
</property>

<property>
    <name>yarn.resourcemanager.cluster-id</name>
    <value>yarn-cluster</value>
</property>

<property>
    <name>yarn.resourcemanager.ha.rm-ids</name>
    <value>rm1,rm2</value>
</property>

<!-- RM1 配置 -->
<property>
    <name>yarn.resourcemanager.hostname.rm1</name>
    <value>rm1.host</value>
</property>
<property>
    <name>yarn.resourcemanager.address.rm1</name>
    <value>rm1.host:8032</value>
</property>
<property>
    <name>yarn.resourcemanager.scheduler.address.rm1</name>
    <value>rm1.host:8030</value>
</property>

<!-- RM2 配置 -->
<property>
    <name>yarn.resourcemanager.hostname.rm2</name>
    <value>rm2.host</value>
</property>
<property>
    <name>yarn.resourcemanager.address.rm2</name>
    <value>rm2.host:8032</value>
</property>

<!-- ZooKeeper 配置 -->
<property>
    <name>yarn.resourcemanager.zk-address</name>
    <value>zk1:2181,zk2:2181,zk3:2181</value>
</property>

<property>
    <name>yarn.resourcemanager.zk-state-store.parent-path</name>
    <value>/rmstore</value>
</property>
```

## 5. 监控与诊断

### 5.1 YARN 命令行

```bash
# 查看集群状态
yarn node -list
yarn queue -status default

# 查看应用
yarn application -list
yarn application -status application_123456_0001
yarn application -kill application_123456_0001

# 查看日志
yarn logs -applicationId application_123456_0001
yarn logs -applicationId application_123456_0001 -log_files stdout

# 查看容器
yarn container -list application_123456_0001
```

### 5.2 REST API

```bash
# 集群指标
curl http://rm-host:8088/ws/v1/cluster/metrics

# 节点信息
curl http://rm-host:8088/ws/v1/cluster/nodes

# 应用信息
curl http://rm-host:8088/ws/v1/cluster/apps

# 调度器信息
curl http://rm-host:8088/ws/v1/cluster/scheduler
```

## 6. 性能调优

| 配置项 | 说明 | 建议值 |
|--------|------|--------|
| yarn.nodemanager.vmem-check-enabled | 虚拟内存检查 | false (避免 OOM 误杀) |
| yarn.nodemanager.pmem-check-enabled | 物理内存检查 | true |
| yarn.acl.enable | ACL 启用 | true (生产环境) |
| yarn.resourcemanager.am.max-attempts | AM 最大重试 | 2 |
| yarn.log-aggregation-enable | 日志聚合 | true |
| yarn.log.server.url | 日志服务器 | <http://jobhistory:19888/jobhistory/logs> |

## 7. 与 Kubernetes 对比

| 特性 | YARN | Kubernetes |
|------|------|------------|
| **设计目标** | 大数据处理 | 通用容器编排 |
| **调度粒度** | 容器 | Pod |
| **资源类型** | 内存、CPU | 更丰富（GPU、存储等） |
| **生态** | Hadoop 生态 | 云原生生态 |
| **适用场景** | 批处理、流处理 | 微服务、AI/ML |
| **调度延迟** | 较高 | 较低 |

## 8. 总结

YARN 作为 Hadoop 生态的资源管理基石：

- **优势**：成熟稳定、与 Hadoop 深度集成、多调度策略
- **适用**：大规模批处理、交互式查询、流处理
- **演进**：向容器化（YARN on Docker）和云原生方向发展

最佳实践：

1. 生产环境使用 Capacity 或 Fair Scheduler
2. 合理设置队列容量和权限
3. 启用 ResourceManager HA
4. 监控资源使用，及时调整配置


---

## 相关主题

- [Kubernetes调度器](./Kubernetes调度器.md)
- [Hadoop-MapReduce详解](../batch-processing/Hadoop-MapReduce详解.md)
- [资源隔离技术](./资源隔离技术.md)

## 参考资源

- [YARN官方文档](https://hadoop.apache.org/docs/stable/hadoop-yarn/hadoop-yarn-site/YARN.html)
