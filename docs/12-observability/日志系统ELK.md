# ELK Stack 日志系统专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

ELK Stack 是业界最流行的开源日志收集、存储、分析和可视化解决方案，由 Elasticsearch、Logstash、Kibana 和 Beats 组成，能够处理海量日志数据并提供实时搜索与分析能力。

---

## 一、核心概念

### 1.1 定义与原理

ELK Stack 是一套完整的日志管理解决方案，其名称来源于三个核心组件的首字母：

- **Elasticsearch**：分布式搜索引擎，负责日志的存储和检索
- **Logstash**：数据处理管道，负责日志的收集、解析和转换
- **Kibana**：数据可视化平台，提供日志查询和图表展示界面

随着 Elastic Beats 轻量级采集器的加入，官方将其更名为 Elastic Stack。

**核心工作原理**：
1. **采集层**：Filebeat/Beats 从各服务器采集日志
2. **处理层**：Logstash 对日志进行过滤、解析、丰富化处理
3. **存储层**：Elasticsearch 建立索引并存储日志数据
4. **展示层**：Kibana 提供查询界面和可视化仪表板

### 1.2 关键特性

- **水平扩展性**：Elasticsearch 支持分布式部署，可处理 PB 级数据
- **实时搜索**：基于倒排索引，毫秒级日志检索响应
- **全文检索**：支持复杂查询、模糊匹配、聚合分析
- **可视化丰富**：Kibana 提供多种图表类型和仪表板构建能力
- **生态完善**：丰富的 Beats 采集器、插件和集成方案

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 集中式日志管理 | ⭐⭐⭐⭐⭐ | 统一收集分布式系统日志，标准化查询入口 |
| 安全审计分析 | ⭐⭐⭐⭐⭐ | 安全事件日志分析、入侵检测、合规审计 |
| 应用故障排查 | ⭐⭐⭐⭐⭐ | 快速定位错误日志、追踪请求链路 |
| 业务数据分析 | ⭐⭐⭐⭐ | 用户行为日志分析、转化率统计 |
| 实时日志告警 | ⭐⭐⭐ | 需配合 Watcher/X-Pack 实现实时监控 |
| 轻量级边缘采集 | ⭐⭐⭐ | Beats 虽轻量，但架构相对复杂 |

---

## 二、技术细节

### 2.1 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              ELK Stack 架构                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────┐    ┌─────────────┐    ┌─────────────┐                │
│   │  Application │    │  Application │    │  Application │                │
│   │   Server 1   │    │   Server 2   │    │   Server N   │                │
│   └──────┬──────┘    └──────┬──────┘    └──────┬──────┘                │
│          │                  │                  │                        │
│          ▼                  ▼                  ▼                        │
│   ┌─────────────┐    ┌─────────────┐    ┌─────────────┐                │
│   │  Filebeat   │    │  Filebeat   │    │  Filebeat   │  日志采集层     │
│   └──────┬──────┘    └──────┬──────┘    └──────┬──────┘                │
│          │                  │                  │                        │
│          └──────────────────┼──────────────────┘                        │
│                             ▼                                           │
│                    ┌─────────────────┐                                 │
│                    │    Logstash     │    数据处理层                    │
│                    │  (Filter/Parse) │                                 │
│                    └────────┬────────┘                                 │
│                             │                                          │
│                             ▼                                          │
│              ┌─────────────────────────────┐                          │
│              │       Elasticsearch         │    存储层                 │
│              │  ┌─────┐ ┌─────┐ ┌─────┐   │                          │
│              │  │Shard│ │Shard│ │Shard│   │                          │
│              │  └─────┘ └─────┘ └─────┘   │                          │
│              └─────────────┬───────────────┘                          │
│                            │                                          │
│                            ▼                                          │
│                    ┌─────────────┐                                    │
│                    │   Kibana    │    可视化层                         │
│                    │  Dashboard  │                                    │
│                    └─────────────┘                                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 组件详解

#### 2.2.1 Elasticsearch 日志存储

**核心概念**：
- **索引（Index）**：日志数据的逻辑容器，类似数据库
- **文档（Document）**：单条日志记录，JSON 格式
- **分片（Shard）**：数据物理分片，支持水平扩展
- **副本（Replica）**：分片副本，保证高可用

**倒排索引原理**：
```
传统索引：文档 → 词项列表
倒排索引：词项 → 文档列表

示例：
日志1: "ERROR connection timeout"
日志2: "WARNING connection slow"
日志3: "ERROR database failure"

倒排索引：
ERROR     → [日志1, 日志3]
WARNING   → [日志2]
connection→ [日志1, 日志2]
timeout   → [日志1]
slow      → [日志2]
database  → [日志3]
failure   → [日志3]
```

**索引策略**：
- **按时间滚动**：daily/weekly 索引，如 `logs-2026.01.01`
- **生命周期管理（ILM）**：热-温-冷-冻数据分层
- **分片规划**：单分片 20-50GB 为宜，避免过多过小分片

#### 2.2.2 Logstash 数据处理

**Pipeline 架构**：
```
Input → Filter → Output
  │        │        │
  ▼        ▼        ▼
采集    解析转换   输出存储
```

**常用插件**：
| 类型 | 插件 | 用途 |
|------|------|------|
| Input | file/tcp/udp/kafka | 从多种来源采集数据 |
| Filter | grok/json/mutate/date | 解析、转换、富化数据 |
| Output | elasticsearch/file/http | 输出到目标存储 |

**Grok 解析示例**：
```
# 原始日志
192.168.1.1 - - [03/Jan/2026:10:30:45 +0800] "GET /api/users HTTP/1.1" 200 1024

# Grok Pattern
%{IP:client_ip} %{USER:ident} %{USER:auth} \[%{HTTPDATE:timestamp}\] "%{WORD:method} %{URIPATHPARAM:request} HTTP/%{NUMBER:http_version}" %{NUMBER:status} %{NUMBER:bytes}

# 解析结果
{
  "client_ip": "192.168.1.1",
  "timestamp": "03/Jan/2026:10:30:45 +0800",
  "method": "GET",
  "request": "/api/users",
  "status": 200,
  "bytes": 1024
}
```

#### 2.2.3 Kibana 可视化

**核心功能**：
- **Discover**：日志检索、字段筛选、实时刷新
- **Visualize**：图表创建（柱状图、饼图、热力图等）
- **Dashboard**：多图表组合仪表板
- **Lens**：拖拽式可视化构建器
- **Machine Learning**：异常检测、日志模式识别

**KQL（Kibana Query Language）**：
```
# 基础查询
status:500 AND path:/api/users

# 范围查询
@timestamp >= "2026-01-01" AND @timestamp < "2026-02-01"

# 模糊匹配
message: "connection*timeout"

# 聚合查询（Dev Tools）
GET /logs-*/_search
{
  "aggs": {
    "status_codes": {
      "terms": { "field": "status" }
    }
  }
}
```

#### 2.2.4 Filebeat 采集

**轻量级设计**：
- 基于 Go 语言，无依赖，单二进制文件
- 资源占用低（内存 < 100MB）
- 支持背压感知，不会压垮下游

**核心模块**：
| 模块 | 用途 |
|------|------|
| system | 系统日志（syslog/auth.log）|
| nginx/apache | Web 服务器日志 |
| mysql/postgresql | 数据库慢日志 |
| docker/kubernetes | 容器日志采集 |

**配置示例**：
```yaml
filebeat.inputs:
- type: log
  enabled: true
  paths:
    - /var/log/app/*.log
  multiline.pattern: '^\['
  multiline.negate: true
  multiline.match: after

output.elasticsearch:
  hosts: ["http://es-node1:9200", "http://es-node2:9200"]
  index: "app-logs-%{+yyyy.MM.dd}"
```

### 2.3 实现机制

#### 数据流转优化

1. **批量处理**：
   - Filebeat 批量发送（默认 2048 条）
   - Logstash 批量处理（pipeline.batch.size）
   - Elasticsearch 批量索引（_bulk API）

2. **索引模板管理**：
   ```json
   {
     "index_patterns": ["app-logs-*"],
     "settings": {
       "number_of_shards": 3,
       "number_of_replicas": 1,
       "index.lifecycle.name": "logs-policy",
       "index.lifecycle.rollover_alias": "app-logs"
     },
     "mappings": {
       "properties": {
         "timestamp": { "type": "date" },
         "level": { "type": "keyword" },
         "message": { "type": "text" }
       }
     }
   }
   ```

3. **集群调优**：
   - 内存分配：堆内存不超过 32GB，JVM 压缩指针优化
   - 分片策略：避免频繁刷盘，合理设置 refresh_interval
   - 查询缓存：利用 request cache 和 field data cache

---

## 三、系统对比

### 3.1 ELK vs Loki 对比矩阵

| 维度 | ELK Stack | Grafana Loki |
|------|-----------|--------------|
| **存储架构** | 全文索引，倒排索引 | 仅索引标签，日志内容压缩存储 |
| **存储成本** | 较高（索引膨胀 1.5-2x）| 较低（仅为原始大小 1/5-1/10）|
| **查询性能** | 全文检索快，复杂聚合优秀 | 标签过滤快，内容检索较慢 |
| **资源占用** | 高（内存、CPU 要求高）| 低（轻量级设计）|
| **查询语言** | Lucene/KQL，功能丰富 | LogQL，类 PromQL 风格 |
| **可视化** | Kibana 功能全面 | Grafana 云原生集成好 |
| **水平扩展** | 成熟稳定，企业级验证 | 扩展性良好，持续迭代 |
| **云原生适配** | 较重，需一定运维成本 | 原生适配 Kubernetes |
| **告警能力** | X-Pack/Watcher（收费）| 原生支持 Alertmanager |
| **适用规模** | 大型企业，复杂查询需求 | 云原生环境，成本敏感场景 |

### 3.2 选型决策树

```
日志系统选型
├── 需要全文检索？
│   ├── 是 → 需要复杂聚合分析？
│   │   ├── 是 → ELK Stack
│   │   └── 否 → 资源充足？
│   │       ├── 是 → ELK Stack
│   │       └── 否 → Loki + 对象存储
│   └── 否 → 云原生环境？
│       ├── 是 → Loki（轻量、低成本）
│       └── 否 → 数据量小？
│           ├── 是 → 轻量级方案（如 Fluentd + ES 单节点）
│           └── 否 → ELK Stack
└── 预算限制严格？
    ├── 是 → Loki + Grafana
    └── 否 → ELK Stack（功能全面）
```

### 3.3 性能基准参考

| 指标 | ELK Stack（3节点） | Loki（3节点） |
|------|-------------------|---------------|
| 写入吞吐量 | 100K-500K docs/s | 500K-1M lines/s |
| 查询延迟（简单）| < 100ms | < 50ms |
| 查询延迟（全文）| 100ms-1s | 1s-10s（需扫全量）|
| 存储压缩率 | 70-80% | 10-20% |
| 内存需求 | 64GB+/节点 | 8GB+/节点 |

---

## 四、实践指南

### 4.1 部署配置

**Docker Compose 部署示例**：
```yaml
version: '3.8'
services:
  elasticsearch:
    image: elasticsearch:8.11.0
    environment:
      - discovery.type=single-node
      - xpack.security.enabled=false
      - "ES_JAVA_OPTS=-Xms2g -Xmx2g"
    volumes:
      - es-data:/usr/share/elasticsearch/data
    ports:
      - "9200:9200"

  logstash:
    image: logstash:8.11.0
    volumes:
      - ./logstash.conf:/usr/share/logstash/pipeline/logstash.conf
    ports:
      - "5044:5044"
    depends_on:
      - elasticsearch

  kibana:
    image: kibana:8.11.0
    environment:
      - ELASTICSEARCH_HOSTS=http://elasticsearch:9200
    ports:
      - "5601:5601"
    depends_on:
      - elasticsearch

  filebeat:
    image: elastic/filebeat:8.11.0
    volumes:
      - /var/log:/var/log:ro
      - ./filebeat.yml:/usr/share/filebeat/filebeat.yml
    depends_on:
      - logstash

volumes:
  es-data:
```

**Logstash 配置示例**：
```
input {
  beats {
    port => 5044
  }
}

filter {
  # JSON 解析
  json {
    source => "message"
    target => "parsed"
  }
  
  # 日期解析
  date {
    match => ["parsed.timestamp", "ISO8601"]
    target => "@timestamp"
  }
  
  # 添加环境标签
  mutate {
    add_field => { "environment" => "production" }
  }
  
  # 删除原始 message 释放空间
  mutate {
    remove_field => ["message"]
  }
}

output {
  elasticsearch {
    hosts => ["http://elasticsearch:9200"]
    index => "%{[parsed.service]}-%{+YYYY.MM.dd}"
  }
}
```

### 4.2 最佳实践

1. **索引生命周期管理（ILM）**：
   - 热阶段（Hot）：7 天，SSD 存储，高频查询
   - 温阶段（Warm）：30 天，HDD 存储，低频查询
   - 冷阶段（Cold）：90 天，只读存储，归档查询
   - 删除阶段（Delete）：超过 1 年自动删除

2. **字段映射优化**：
   - text 字段用于全文检索
   - keyword 字段用于精确匹配和聚合
   - 禁用不需要索引的字段（index: false）
   - 动态映射限制，避免字段爆炸

3. **日志规范化**：
   - 统一日志格式（推荐 JSON）
   - 标准化时间戳字段
   - 添加 trace_id 便于链路追踪
   - 分级日志（DEBUG/INFO/WARNING/ERROR/FATAL）

4. **高可用设计**：
   - Elasticsearch 至少 3 节点，避免脑裂
   - Logstash 多实例负载均衡
   - 定期快照备份到对象存储

### 4.3 常见问题

**Q1: Elasticsearch 内存溢出（OOM）怎么办？**
A: 
- 调整堆内存：不超过物理内存 50% 且不超过 32GB
- 限制聚合深度：设置 search.max_buckets
- 优化查询：避免深度分页，使用 scroll/search_after
- 监控 fielddata：设置 fielddata circuit breaker

**Q2: Logstash 处理延迟高如何解决？**
A:
- 增加 pipeline.workers 数量（默认 CPU 核数）
- 调整 pipeline.batch.size（默认 125）
- 使用持久化队列（PQ）防止数据丢失
- 复杂过滤逻辑前置到 Filebeat（如使用 processors）

**Q3: Kibana 加载慢怎么优化？**
A:
- 缩小默认时间范围（如 Last 15 minutes）
- 避免无筛选查询大索引
- 使用 Index Pattern 过滤无关索引
- 启用 Kibana 查询缓存

---

## 五、与其他主题的关联

### 5.1 上游依赖

- [分布式追踪](../13-tracing/分布式追踪.md) - 日志与 TraceID 关联
- [微服务架构](../07-microservices/微服务架构设计.md) - 多服务日志采集
- [Docker容器化](../08-containerization/Docker容器化技术.md) - 容器日志采集

### 5.2 下游应用

- [告警通知系统](./告警通知系统.md) - 日志异常告警
- [安全信息与事件管理](../15-security/SIEM安全运营.md) - 安全日志分析

### 5.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| Fluentd | 替代方案 | 同为日志收集器，可与 ES 配合 |
| OpenTelemetry | 演进方向 | 统一可观测性标准，包含日志规范 |
| Kafka | 缓冲层 | 可作为 Logstash 前置消息队列 |

---

## 六、参考资源

### 6.1 官方文档

1. [Elasticsearch 官方文档](https://www.elastic.co/guide/en/elasticsearch/reference/current/index.html)
2. [Logstash 配置参考](https://www.elastic.co/guide/en/logstash/current/configuration.html)
3. [Kibana 用户指南](https://www.elastic.co/guide/en/kibana/current/index.html)
4. [Filebeat 快速入门](https://www.elastic.co/guide/en/beats/filebeat/current/filebeat-getting-started.html)

### 6.2 开源项目

1. [elastic/helm-charts](https://github.com/elastic/helm-charts) - Kubernetes Helm 部署
2. [deviantony/docker-elk](https://github.com/deviantony/docker-elk) - Docker 部署模板

### 6.3 学习资料

1. [Elasticsearch 权威指南](https://www.elastic.co/guide/cn/elasticsearch/guide/current/index.html) - 中文版
2. [ELK Stack 深度解析](https://www.ruanyifeng.com/blog/2017/08/elasticsearch.html) - 阮一峰博客

---

**维护者**：项目团队
**最后更新**：2026年
