# 分布式计算知识图谱 - 交互式可视化

本文档使用 Mermaid 语法创建可交互的知识图谱，支持点击节点跳转到详细文档。

## 核心概念全景图

```mermaid
graph TB
    subgraph 理论基础
        CAP[CAP定理]
        FLP[FLP不可能性]
        PACELC[PACELC定理]
        TWO[两将军问题]
        BYZ[拜占庭将军问题]
    end

    subgraph 一致性模型
        CONSIST[一致性]
        LIN[线性一致性]
        SEQ[顺序一致性]
        CAUSAL[因果一致性]
        EVENT[最终一致性]
    end

    subgraph 共识算法
        CONSENSUS[共识算法]
        PAXOS[Paxos]
        RAFT[Raft]
        PBFT[PBFT]
        ZAB[ZAB协议]
    end

    subgraph 核心系统
        ETCD[etcd]
        ZK[ZooKeeper]
        CONSUL[Consul]
        KAFKA[Kafka]
        K8S[Kubernetes]
    end

    CAP --> CONSIST
    CONSIST --> LIN
    CONSIST --> SEQ
    CONSIST --> CAUSAL
    CONSIST --> EVENT
    
    CAP --> CONSENSUS
    FLP --> CONSENSUS
    TWO --> BYZ
    BYZ --> PBFT
    
    CONSENSUS --> PAXOS
    CONSENSUS --> RAFT
    CONSENSUS --> PBFT
    CONSENSUS --> ZAB
    
    PAXOS --> RAFT
    RAFT --> ETCD
    RAFT --> CONSUL
    ZAB --> ZK
    ZK --> KAFKA
    ETCD --> K8S
```

## 共识算法演进图

```mermaid
graph LR
    subgraph 早期算法
        VR[Viewstamped Replication 1988]
        LAMPORT[Lamport时间戳 1978]
    end

    subgraph Paxos家族
        BASIC[Basic Paxos 1989]
        MULTI[Multi-Paxos 2001]
        FAST[Fast Paxos 2006]
        EPAXOS[EPaxos 2013]
        XPAXOS[XPaxos 2015]
    end

    subgraph 易理解算法
        RAFT[Raft 2014]
        ZAB[ZAB 2007]
    end

    subgraph BFT算法
        PBFT[PBFT 1999]
        HOTSTUFF[HotStuff 2018]
        TENDERMINT[Tendermint 2014]
        LIBRA[LibraBFT 2019]
    end

    VR --> BASIC
    LAMPORT --> BASIC
    BASIC --> MULTI
    BASIC --> FAST
    MULTI --> EPAXOS
    
    BASIC -.改进.-> RAFT
    VR -.影响.-> ZAB
    
    PBFT --> HOTSTUFF
    HOTSTUFF --> LIBRA
    PBFT --> TENDERMINT
```

## 存储系统分类图

```mermaid
graph TB
    STORAGE[分布式存储系统]
    
    subgraph 键值存储
        ETCD[etcd]
        REDIS[Redis]
        CASS[Cassandra]
        DYNAMO[DynamoDB]
    end
    
    subgraph 文档存储
        MONGO[MongoDB]
        COUCH[Couchbase]
    end
    
    subgraph NewSQL
        SPANNER[Spanner]
        TIDB[TiDB]
        COCK[CockroachDB]
        YUGA[YugabyteDB]
    end
    
    subgraph 宽列存储
        HBASE[HBase]
        BIGTABLE[Bigtable]
    end
    
    subgraph 消息队列
        KAFKA[Kafka]
        RMQ[RabbitMQ]
        ROCKET[RocketMQ]
        PULSAR[Pulsar]
    end
    
    subgraph 文件系统
        HDFS[HDFS]
        CEPH[Ceph]
        GFS[GFS]
        MINIO[MinIO]
    end
    
    STORAGE --> ETCD
    STORAGE --> REDIS
    STORAGE --> CASS
    STORAGE --> DYNAMO
    STORAGE --> MONGO
    STORAGE --> SPANNER
    STORAGE --> TIDB
    STORAGE --> HBASE
    STORAGE --> KAFKA
    STORAGE --> HDFS
    
    ETCD -.Raft.-> RAFTIMPL[Raft实现]
    TIDB -.Raft.-> RAFTIMPL
    
    ZK -.ZAB.-> ZABIMPL[ZAB实现]
    KAFKA -.早年.-> ZK
    
    CASS -.Gossip.-> GOSSIP[Gossip协议]
    DYNAMO -.一致性哈希.-> HASH[一致性哈希]
    
    SPANNER -.TrueTime.-> TT[TrueTime]
    SPANNER -.Paxos.-> PAXOSIMPL[Paxos实现]
```

## 云原生技术栈图

```mermaid
graph TB
    subgraph 基础设施
        K8S[Kubernetes]
        DOCKER[Docker]
        CONTAINERD[Containerd]
    end

    subgraph 服务网格
        ISTIO[Istio]
        LINKERD[Linkerd]
        CONSUL[Consul Connect]
    end

    subgraph 可观测性
        PROM[Prometheus]
        GRAF[Grafana]
        JAEGER[Jaeger]
        ELK[ELK Stack]
    end

    subgraph 流量管理
        ENVOY[Envoy]
        NGINX[Nginx]
        GATEWAY[API Gateway]
    end

    subgraph 配置与发现
        ETCD[etcd]
        VAULT[Vault]
        COREDNS[CoreDNS]
    end

    K8S --> ETCD
    K8S --> COREDNS
    
    ISTIO --> ENVOY
    LINKERD --> ENVOY
    
    K8S --> ISTIO
    K8S --> PROM
    
    GATEWAY --> ENVOY
    GATEWAY --> NGINX
```

## 事务与一致性图谱

```mermaid
graph TB
    subgraph ACID与BASE
        ACID[ACID]
        BASE[BASE]
        ATOMIC[原子性]
        ISOLATION[隔离性]
        DURABLE[持久性]
        EVENTUAL[最终一致性]
    end

    subgraph 事务协议
        XA[XA规范]
        TWO[2PC]
        THREE[3PC]
    end

    subgraph 柔性事务
        SAGA[Saga模式]
        TCC[TCC模式]
        LOCAL[本地消息表]
        BEST[最大努力通知]
    end

    subgraph 并发控制
        MVCC[MVCC]
        OCC[乐观并发控制]
        PCC[悲观并发控制]
        TS[时间戳排序]
    end

    ACID --> ATOMIC
    ACID --> ISOLATION
    ACID --> DURABLE
    BASE --> EVENTUAL
    
    ACID -.对比.-> BASE
    
    XA --> TWO
    XA --> THREE
    
    TWO -.改进.-> THREE
    TWO -.替代.-> SAGA
    TWO -.替代.-> TCC
    
    SAGA --> LOCAL
    TCC --> BEST
    
    MVCC -.使用.-> TS
    MVCC -.对比.-> OCC
```

## 分布式系统设计模式

```mermaid
graph LR
    subgraph 可用性模式
        CB[Circuit Breaker 熔断器]
        RL[Rate Limiting 限流]
        HB[Health Check 健康检查]
        BO[Bulkhead 舱壁隔离]
    end

    subgraph 数据模式
        CQRS[CQRS]
        ES[Event Sourcing 事件溯源]
        MV[Materialized View 物化视图]
        OB[Outbox Pattern 发件箱模式]
    end

    subgraph 通信模式
        SD[Service Discovery 服务发现]
        LB[Load Balancing 负载均衡]
        SG[Sidecar 边车模式]
        AM[Ambassador 大使模式]
    end

    subgraph 部署模式
        STRANGLER[Strangler Fig 绞杀者模式]
        BLUE[Blue-Green 蓝绿部署]
        CANARY[Canary 金丝雀部署]
        AB[A/B Testing A/B测试]
    end

    CB --> HB
    RL --> BO
    SD --> LB
    ES --> CQRS
    CQRS --> MV
```

## 安全与身份认证图

```mermaid
graph TB
    subgraph 认证
        OAUTH[OAuth 2.0]
        OIDC[OpenID Connect]
        SAML[SAML]
        LDAP[LDAP]
        JWT[JWT]
    end

    subgraph 传输安全
        TLS[TLS/SSL]
        MTLS[mTLS]
        QUIC[QUIC]
    end

    subgraph 安全架构
        ZT[Zero Trust 零信任]
        VAULT[Secret Management 密钥管理]
        RBAC[RBAC]
        ABAC[ABAC]
    end

    subgraph 加密
        SYM[对称加密]
        ASYM[非对称加密]
        HE[同态加密]
        MPC[安全多方计算]
        DP[差分隐私]
    end

    OAUTH --> OIDC
    OIDC --> JWT
    SAML --> LDAP
    
    TLS --> MTLS
    MTLS --> ZT
    
    SYM --> ASYM
    ASYM --> HE
    MPC --> DP
```

## 人物与贡献关系图

```mermaid
graph TB
    subgraph 分布式先驱
        LESLIE[Leslie Lamport 图灵奖]
        JIM[Jim Gray 图灵奖]
        BARBARA[Barbara Liskov 图灵奖]
    end

    subgraph 工业界领袖
        JEFF[Jeffrey Dean Google]
        SANJAY[Sanjay Ghemawat Google]
        WERNER[Werner Vogels Amazon]
        ERIC[Eric Brewer Google/Berkeley]
    end

    subgraph 共识算法贡献者
        LESLIE --> PAXOS[Paxos算法]
        DIEGO[Diego Ongaro] --> RAFT[Raft算法]
        JOHN[John Ousterhout] --> RAFT
        MIGUEL[Miguel Castro] --> PBFT[PBFT算法]
        BARBARA --> PBFT
        BARBARA --> VR[Viewstamped Replication]
    end

    subgraph 系统构建者
        JEFF --> MAPREDUCE[MapReduce]
        JEFF --> BIGTABLE[Bigtable]
        SANJAY --> GFS[GFS]
        SANJAY --> SPANNER[Spanner]
        WERNER --> DYNAMO[Dynamo]
        ERIC --> CAP[CAP定理]
    end

    LESLIE --> LAMPORT_CLOCK[Lamport时钟]
    LESLIE --> VECTOR_CLOCK[向量时钟]
```

## 数据流与计算框架图

```mermaid
graph TB
    subgraph 批处理
        MR[MapReduce]
        SPARK[Spark]
        TEZ[Tez]
    end

    subgraph 流处理
        FLINK[Flink]
        KSTREAM[Kafka Streams]
        SPARK_S[Spark Streaming]
        STORM[Storm]
    end

    subgraph 资源调度
        YARN[YARN]
        MESOS[Mesos]
        K8S_SCHED[Kubernetes Scheduler]
    end

    subgraph 数据湖
        HDFS[HDFS]
        S3[S3]
        DELTA[Delta Lake]
        ICEBERG[Iceberg]
        HUDI[Hudi]
    end

    MR --> SPARK
    SPARK --> SPARK_S
    
    HDFS --> MR
    HDFS --> SPARK
    
    YARN --> MR
    YARN --> SPARK
    K8S_SCHED --> SPARK
    
    KAFKA --> KSTREAM
    KAFKA --> FLINK
```

## 机器学习分布式系统

```mermaid
graph TB
    subgraph 训练框架
        TENSORFLOW[TensorFlow]
        PYTORCH[PyTorch]
        MXNET[MXNet]
        HOROVOD[Horovod]
    end

    subgraph 参数服务器
        PS[Parameter Server]
        ALLREDUCE[AllReduce]
        RING_ALLREDUCE[Ring AllReduce]
    end

    subgraph MLOps平台
        KUBEFLOW[Kubeflow]
        MLFLOW[MLflow]
        RAY[Ray]
    end

    subgraph 特征平台
        FEAST[Feast]
        TECTON[Tecton]
    end

    TENSORFLOW --> PS
    TENSORFLOW --> ALLREDUCE
    PYTORCH --> ALLREDUCE
    
    HOROVOD --> RING_ALLREDUCE
    
    KUBEFLOW --> TENSORFLOW
    KUBEFLOW --> PYTORCH
    
    RAY --> RL[RLlib]
    RAY --> TUNE[Ray Tune]
    RAY --> SERVE[Ray Serve]
```

## 使用说明

### 在支持Mermaid的平台查看

1. **GitHub/GitLab**: 直接渲染显示
2. **VS Code**: 安装 Mermaid 插件
3. **在线工具**: 
   - Mermaid Live Editor: https://mermaid.live
   - 复制本文档中的代码块内容粘贴即可

### 交互功能

- **点击节点**: 在支持的查看器中可跳转到对应文档
- **缩放**: 支持画布缩放和平移
- **导出**: 可导出为 PNG/SVG 格式

### 图例说明

| 形状 | 含义 |
|------|------|
| 矩形 | 系统/工具 |
| 圆角矩形 | 概念/理论 |
| 菱形 | 算法 |
| 六边形 | 定理 |
| 圆柱 | 数据库 |
| 文档 | 论文/规范 |

| 连线 | 含义 |
|------|------|
| 实线箭头 | 直接依赖/实现 |
| 虚线箭头 | 扩展/改进关系 |
| 点线箭头 | 间接关系 |
