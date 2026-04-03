# 健康检查 专题文档

**文档版本**：v1.0
**创建时间**：2026年4月
**最后更新**：2026年4月
**状态**：✅ 已完成

---

## 📋 执行摘要

健康检查（Health Check）是分布式系统中监控服务可用性的核心机制。通过探针设计，负载均衡器和编排系统能够及时发现不健康实例并剔除，确保流量只路由到健康节点。

---

## 一、核心概念

### 1.1 定义与原理

**健康检查**是通过定期探测服务的健康状态，判断实例是否可用、是否需要从服务池中剔除的机制。

Kubernetes三种探针类型：

| 探针类型 | 用途 | 失败行为 |
|----------|------|----------|
| **Liveness** | 检测应用是否存活 | 重启容器 |
| **Readiness** | 检测应用是否就绪 | 从Service摘除 |
| **Startup** | 检测应用是否启动完成 | 禁用其他探针 |

探针检测方式：

| 方式 | 适用场景 | 开销 |
|------|----------|------|
| HTTP GET | Web应用 | 低 |
| TCP Socket | 非HTTP服务 | 最低 |
| Exec命令 | 复杂检测逻辑 | 较高 |
| gRPC | gRPC服务 | 低 |

### 1.2 关键特性

- **多维度检查**：业务、依赖、资源等多角度
- **分级健康**：区分致命和非致命问题
- **自愈能力**：配合自动重启实现自愈
- **零停机部署**：就绪探针配合滚动更新
- **可观测性**：健康状态暴露给监控系统

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| K8s Pod管理 | ⭐⭐⭐⭐⭐ | 核心功能 |
| 负载均衡 | ⭐⭐⭐⭐⭐ | 剔除不健康节点 |
| 服务发现 | ⭐⭐⭐⭐ | 注册中心健康检查 |
| 自动扩缩容 | ⭐⭐⭐⭐ | 基于健康状态决策 |
| 告警通知 | ⭐⭐⭐⭐ | 健康变化触发告警 |

---

## 二、技术细节

### 2.1 架构设计

```mermaid
graph TB
    subgraph "探针检测层"
        Kubelet[Kubelet/Agent]
        LB[负载均衡器]
        Consul[服务注册中心]
    end

    subgraph "应用探针端点"
        Live[/health/live]
        Ready[/health/ready]
        Startup[/health/startup]
        Custom[/health/custom]
    end

    subgraph "依赖检查"
        DB[(数据库)]
        Cache[(缓存)]
        MQ[消息队列]
        Ext[外部服务]
    end

    Kubelet --> Live
    Kubelet --> Ready
    Kubelet --> Startup
    LB --> Ready
    Consul --> Custom

    Ready -->|检查依赖| DB
    Ready -->|检查依赖| Cache
    Ready -->|检查依赖| MQ
    Custom -->|检查依赖| Ext
```

### 2.2 探针实现

#### Spring Boot Actuator

```java
@Component
public class CustomHealthIndicator implements HealthIndicator {

    @Autowired
    private DataSource dataSource;

    @Autowired
    private RedisTemplate redisTemplate;

    @Override
    public Health health() {
        Health.Builder builder = Health.up();

        // 检查数据库
        try (Connection conn = dataSource.getConnection()) {
            if (conn.isValid(3)) {
                builder.withDetail("database", "UP");
            } else {
                builder.down().withDetail("database", "Connection invalid");
            }
        } catch (SQLException e) {
            builder.down().withDetail("database", e.getMessage());
        }

        // 检查Redis
        try {
            redisTemplate.opsForValue().get("health_check");
            builder.withDetail("redis", "UP");
        } catch (Exception e) {
            builder.down().withDetail("redis", e.getMessage());
        }

        // 检查磁盘空间
        File disk = new File("/");
        long freeSpace = disk.getFreeSpace();
        long totalSpace = disk.getTotalSpace();
        double freePercent = (double) freeSpace / totalSpace * 100;

        if (freePercent < 10) {
            builder.down().withDetail("disk", "Low disk space: " + freePercent + "%");
        } else {
            builder.withDetail("disk", "UP (" + String.format("%.1f", freePercent) + "% free)");
        }

        return builder.build();
    }
}

// 区分Liveness和Readiness
@Component("livenessProbe")
public class LivenessProbe implements HealthIndicator {
    @Override
    public Health health() {
        // 只检查应用本身是否存活
        return Health.up().build();
    }
}

@Component("readinessProbe")
public class ReadinessProbe implements HealthIndicator {
    @Override
    public Health health() {
        // 检查所有依赖是否就绪
        // 实现略...
        return Health.up().build();
    }
}
```

#### Go实现

```go
package main

import (
    "context"
    "database/sql"
    "encoding/json"
    "net/http"
    "time"
)

type HealthStatus struct {
    Status   string                 `json:"status"`
    Checks   map[string]CheckResult `json:"checks"`
    Timestamp time.Time             `json:"timestamp"`
}

type CheckResult struct {
    Status  string `json:"status"`
    Message string `json:"message,omitempty"`
    Latency string `json:"latency,omitempty"`
}

func healthHandler(w http.ResponseWriter, r *http.Request) {
    status := HealthStatus{
        Status:    "UP",
        Checks:    make(map[string]CheckResult),
        Timestamp: time.Now(),
    }

    // 检查数据库
    dbStart := time.Now()
    if err := db.PingContext(r.Context()); err != nil {
        status.Status = "DOWN"
        status.Checks["database"] = CheckResult{
            Status:  "DOWN",
            Message: err.Error(),
        }
    } else {
        status.Checks["database"] = CheckResult{
            Status:  "UP",
            Latency: time.Since(dbStart).String(),
        }
    }

    // 检查Redis
    redisStart := time.Now()
    if err := redisClient.Ping(r.Context()).Err(); err != nil {
        status.Status = "DOWN"
        status.Checks["redis"] = CheckResult{
            Status:  "DOWN",
            Message: err.Error(),
        }
    } else {
        status.Checks["redis"] = CheckResult{
            Status:  "UP",
            Latency: time.Since(redisStart).String(),
        }
    }

    // 返回结果
    w.Header().Set("Content-Type", "application/json")
    if status.Status == "DOWN" {
        w.WriteHeader(http.StatusServiceUnavailable)
    }
    json.NewEncoder(w).Encode(status)
}

// 独立的存活检查
func livenessHandler(w http.ResponseWriter, r *http.Request) {
    // 只要进程存活就返回200
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(`{"status":"UP"}`))
}

// 就绪检查
func readinessHandler(w http.ResponseWriter, r *http.Request) {
    // 检查应用是否准备好接收流量
    if !appReady {
        w.WriteHeader(http.StatusServiceUnavailable)
        w.Write([]byte(`{"status":"DOWN","reason":"Application not ready"}`))
        return
    }
    w.Write([]byte(`{"status":"UP"}`))
}
```

### 2.3 Kubernetes配置

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  template:
    spec:
      containers:
        - name: app
          image: my-app:latest
          ports:
            - containerPort: 8080

          # 存活探针 - 检测是否需要重启
          livenessProbe:
            httpGet:
              path: /health/live
              port: 8080
            initialDelaySeconds: 30
            periodSeconds: 10
            timeoutSeconds: 5
            failureThreshold: 3

          # 就绪探针 - 检测是否可以接收流量
          readinessProbe:
            httpGet:
              path: /health/ready
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 5
            timeoutSeconds: 3
            failureThreshold: 3
            successThreshold: 1

          # 启动探针 - 检测启动完成
          startupProbe:
            httpGet:
              path: /health/startup
              port: 8080
            initialDelaySeconds: 10
            periodSeconds: 5
            failureThreshold: 30  # 最多等待 10 + 30*5 = 160s
```

---

## 三、系统对比

### 3.1 探针配置对比

| 探针类型 | initialDelay | period | timeout | failureThreshold |
|----------|--------------|--------|---------|------------------|
| Liveness | 30s | 10s | 5s | 3 |
| Readiness | 5s | 5s | 3s | 3 |
| Startup | 10s | 5s | 3s | 30 |

---

## 四、实践指南

### 4.1 最佳实践

1. **区分Live和Ready**：Live检测进程存活，Ready检测依赖就绪
2. **轻量级检查**：探针检查应快速返回，避免重查询
3. **缓存结果**：频繁探针可缓存检查结果
4. **渐进式检查**：Readiness失败不一定需要重启
5. **日志记录**：探针失败时记录详细原因

### 4.2 常见问题

**Q1: Liveness和Readiness有什么区别？**
A: Liveness失败会重启容器，Readiness失败只从Service摘除。Liveness应该轻量，Readiness应该全面。

**Q2: 如何避免探针风暴？**
A: 设置合理的periodSeconds，在应用内缓存健康检查结果（如5秒刷新一次）。

---

## 五、形式化分析

### 5.1 探针状态机

```
状态：Unknown -> Healthy -> Unhealthy -> Healthy/Restart

转换：
- Unknown -(initialDelay)-> Healthy/Unhealthy
- Healthy -(failureThreshold次失败)-> Unhealthy
- Unhealthy -(successThreshold次成功)-> Healthy
- Unhealthy (Liveness) -> 容器重启
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [故障检测器](./01-fault-detector.md)

### 6.2 下游应用

- [优雅关闭](./09-graceful-shutdown.md)

---

## 七、参考资源

### 7.1 官方文档

1. [Kubernetes Probes](https://kubernetes.io/docs/concepts/workloads/pods/pod-lifecycle/#container-probes)

---

**维护者**：项目团队
**最后更新**：2026年4月
