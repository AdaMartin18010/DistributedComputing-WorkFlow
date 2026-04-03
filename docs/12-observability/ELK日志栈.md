# ELK日志栈

## 概述

ELK是Elasticsearch、Logstash、Kibana三个开源软件组成的数据分析栈，是目前最流行的日志处理和分析解决方案。它能够集中收集、存储、搜索和可视化海量日志数据，帮助运维和开发团队快速定位问题、分析趋势。

## 架构设计

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          ELK Stack 架构                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐         │
│  │ Log Source│───►│  Filebeat │───►│ Logstash  │───►│Elasticsearch│    │
│  │   (App)  │    │  (Agent)  │    │ (Pipeline)│    │  (Storage)  │    │
│  └──────────┘    └──────────┘    └─────┬─────┘    └──────┬────┘      │
│       │                                │                  │            │
│  ┌────┴────┐    ┌──────────┐    ┌─────┴─────┐    ┌──────┴────┐       │
│  │  App Log │    │ Metricbeat│    │  Filter   │    │  Index    │      │
│  │ Sys Log  │    │Packetbeat│    │  Grok     │    │  Shard    │      │
│  │Container │    │Auditbeat │    │  Date     │    │  Replica  │      │
│  └──────────┘    └──────────┘    └───────────┘    └───────────┘       │
│                                                                         │
│                                          ┌──────────┐                  │
│                                          │  Kibana   │                  │
│                                          │(Visualize)│◄────────────────┤
│                                          └─────┬────┘                  │
│                                                │                       │
│                                          ┌─────┴────┐                 │
│                                          │Dashboard │                 │
│                                          │Discovery │                 │
│                                          └──────────┘                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

## 核心组件

### 1. Elasticsearch

分布式搜索和分析引擎，负责日志存储和检索。

```yaml
# elasticsearch.yml
cluster:
  name: elk-cluster
  routing.allocation.disk.threshold_enabled: true
  routing.allocation.disk.watermark.low: "85%"
  routing.allocation.disk.watermark.high: "90%"
  routing.allocation.disk.watermark.flood_stage: "95%"

node:
  name: ${HOSTNAME}
  roles: [master, data, ingest]

network:
  host: 0.0.0.0
  bind_host: 0.0.0.0
  publish_host: ${POD_IP}

http:
  port: 9200
  cors:
    enabled: true
    allow-origin: "*"

discovery:
  seed_hosts:
    - elasticsearch-0.elasticsearch
    - elasticsearch-1.elasticsearch
    - elasticsearch-2.elasticsearch
  seed_resolver:
    timeout: 5s

cluster.initial_master_nodes:
  - elasticsearch-0
  - elasticsearch-1
  - elasticsearch-2

xpack:
  security:
    enabled: true
    transport:
      ssl:
        enabled: true
        verification_mode: certificate
        keystore:
          path: /usr/share/elasticsearch/config/certs/elastic-certificates.p12
        truststore:
          path: /usr/share/elasticsearch/config/certs/elastic-certificates.p12
  monitoring:
    collection:
      enabled: true
      indices: true

# 性能调优
indices:
  memory.index_buffer_size: "30%"
  queries.cache.size: "5%"

# 索引生命周期管理
ilm:
  enabled: true
  poll_interval: "10m"
```

### 2. Logstash

数据处理管道，负责日志解析、过滤和转换。

```yaml
# logstash.yml
http.host: "0.0.0.0"
xpack.monitoring.enabled: true
xpack.monitoring.elasticsearch.hosts: ["https://elasticsearch:9200"]
xpack.monitoring.elasticsearch.username: "logstash_system"
xpack.monitoring.elasticsearch.password: "${LOGSTASH_PASSWORD}"

# pipeline配置
config.reload.automatic: true
config.reload.interval: 3s

# 性能调优
pipeline.workers: 4
pipeline.batch.size: 125
pipeline.batch.delay: 50
```

```ruby
# pipelines/logstash.conf
input {
  beats {
    port => 5044
    type => "beats"
  }

  tcp {
    port => 5000
    type => "tcp"
    codec => json_lines
  }
}

filter {
  if [type] == "beats" {
    # 解析Nginx日志
    if [source] =~ /nginx.*\.log/ {
      grok {
        match => {
          "message" => "%{IPORHOST:client_ip} - %{USER:auth} \[%{HTTPDATE:timestamp}\] \"%{WORD:method} %{URIPATHPARAM:request} HTTP/%{NUMBER:http_version}\" %{NUMBER:status:int} %{NUMBER:bytes:int} \"%{URI:referrer}\" \"%{DATA:user_agent}\" %{NUMBER:request_time:float}"
        }
        remove_field => ["message"]
      }

      # 解析User-Agent
      useragent {
        source => "user_agent"
        target => "user_agent_parsed"
      }

      # 解析时间
      date {
        match => ["timestamp", "dd/MMM/yyyy:HH:mm:ss Z"]
        target => "@timestamp"
      }

      # 添加地理位置
      geoip {
        source => "client_ip"
        target => "geoip"
      }

      # 根据状态码添加标签
      if [status] >= 500 {
        mutate { add_tag => ["error", "server_error"] }
      } else if [status] >= 400 {
        mutate { add_tag => ["error", "client_error"] }
      }

      # 计算响应时间分级
      if [request_time] >= 1.0 {
        mutate { add_field => { "response_speed" => "slow" } }
      } else if [request_time] >= 0.5 {
        mutate { add_field => { "response_speed" => "medium" } }
      } else {
        mutate { add_field => { "response_speed" => "fast" } }
      }
    }

    # 应用日志解析
    if [kubernetes][container][name] == "app" {
      json {
        source => "message"
        skip_on_invalid_json => true
      }

      # 保留原始消息
      mutate {
        add_field => { "raw_message" => "%{message}" }
      }
    }
  }
}

output {
  # 按日期分索引
  elasticsearch {
    hosts => ["https://elasticsearch:9200"]
    user => "logstash_writer"
    password => "${ELASTIC_PASSWORD}"
    ssl => true
    ssl_certificate_verification => false

    # ILM配置
    ilm_enabled => true
    ilm_rollover_alias => "logs"
    ilm_pattern => "{now/d}-000001"
    ilm_policy => "logs-retention-policy"

    # 动态索引命名
    index => "%{[@metadata][beat]}-%{[@metadata][version]}-%{+YYYY.MM.dd}"

    # 批量写入优化
    flush_size => 1000
    idle_flush_time => 10
  }

  # 错误日志单独输出
  if "error" in [tags] {
    elasticsearch {
      hosts => ["https://elasticsearch:9200"]
      index => "logs-error-%{+YYYY.MM.dd}"
    }
  }

  # 调试输出
  stdout {
    codec => rubydebug
  }
}
```

### 3. Kibana

可视化界面，提供日志搜索、分析和仪表盘功能。

```yaml
# kibana.yml
server:
  host: "0.0.0.0"
  port: 5601
  name: "kibana"

elasticsearch:
  hosts: ["https://elasticsearch:9200"]
  username: "kibana_system"
  password: "${KIBANA_PASSWORD}"
  ssl:
    verificationMode: none

xpack:
  security:
    encryptionKey: "${ENCRYPTION_KEY}"
  reporting:
    encryptionKey: "${REPORTING_KEY}"

# 功能配置
monitoring:
  enabled: true
  ui:
    container:
      elasticsearch:
        enabled: true

# 日志配置
logging:
  root:
    level: info
```

### 4. Beats

轻量级数据采集器。

```yaml
# filebeat.yml
filebeat.inputs:
  - type: log
    enabled: true
    paths:
      - /var/log/nginx/*.log
    fields:
      log_type: nginx
      environment: production
    fields_under_root: true
    multiline.pattern: '^\d{4}-\d{2}-\d{2}'
    multiline.negate: true
    multiline.match: after

  - type: container
    enabled: true
    paths:
      - /var/lib/docker/containers/*/*.log
    processors:
      - add_kubernetes_metadata:
          host: ${NODE_NAME}
          matchers:
            - logs_path:
                logs_path: /var/lib/docker/containers/

filebeat.autodiscover:
  providers:
    - type: kubernetes
      hints.enabled: true
      hints.default_config:
        type: container
        paths:
          - /var/log/containers/*-${data.kubernetes.container.id}.log

# 输出到Logstash
output.logstash:
  hosts: ["logstash:5044"]
  loadbalance: true
  compression_level: 3

# 处理器
processors:
  - add_host_metadata:
      when.not.contains.tags: forwarded
  - add_cloud_metadata: ~
  - add_docker_metadata: ~
  - drop_fields:
      fields: ["agent.ephemeral_id", "agent.hostname"]

# 性能调优
queue.mem:
  events: 4096
  flush.min_events: 512
  flush.timeout: 5s
```

## 索引生命周期管理 (ILM)

```json
// ILM策略
PUT _ilm/policy/logs-retention-policy
{
  "policy": {
    "phases": {
      "hot": {
        "min_age": "0ms",
        "actions": {
          "rollover": {
            "max_primary_shard_size": "50GB",
            "max_age": "1d",
            "max_docs": 100000000
          },
          "set_priority": {
            "priority": 100
          }
        }
      },
      "warm": {
        "min_age": "3d",
        "actions": {
          "shrink": {
            "number_of_shards": 1
          },
          "forcemerge": {
            "max_num_segments": 1
          },
          "set_priority": {
            "priority": 50
          }
        }
      },
      "cold": {
        "min_age": "30d",
        "actions": {
          "searchable_snapshot": {
            "snapshot_repository": "my_repo",
            "force_merge_index": true
          },
          "set_priority": {
            "priority": 0
          }
        }
      },
      "delete": {
        "min_age": "90d",
        "actions": {
          "delete": {}
        }
      }
    }
  }
}
```

## 常用KQL查询

```kql
# 基础查询
status:500

# 范围查询
@timestamp >= "now-1h" and status >= 400

# 多条件查询
service.name:payment AND (level:ERROR OR level:WARN)

# 模糊查询
message:*timeout*

# 字段存在检查
_exists_:trace.id

# 正则查询
host.name:/prod-.*/
```

## 最佳实践

1. **分片规划**：单分片大小控制在20-50GB
2. **热温冷分离**：按访问频率分层存储，降低成本
3. **映射优化**：禁用_all字段，合理设置字段类型
4. **批量写入**：使用Bulk API，批量大小5-15MB
5. **监控告警**：监控集群状态、节点健康、磁盘空间
