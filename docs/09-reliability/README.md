# 09-reliability - 可靠性与容错

分布式系统的可靠性设计与容错机制。

## 文档列表

### 基础概念
- [01-故障检测器](./故障检测器.md) - 超时与心跳机制
- [02-故障恢复机制](./故障恢复机制.md) - 重启与切换
- [03-灾难恢复](./灾难恢复.md) - RPO/RTO设计
- [04-自稳定算法](./自稳定算法.md) - 自动恢复

### 稳定性模式
- [05-熔断器模式](./05-circuit-breaker.md) - Circuit Breaker
- [06-限流算法](./06-rate-limiting.md) - 令牌桶/漏桶
- [07-降级策略](./07-degradation.md) - 服务降级
- [08-重试与退避](./08-retry-backoff.md) - 指数退避

### 运维保障
- [09-优雅关闭](./09-graceful-shutdown.md) - 零停机部署
- [10-健康检查](./10-health-check.md) - 探针设计
- [11-多活架构](./11-multi-active.md) - 异地多活
- [12-备份与恢复](./12-backup-recovery.md) - 数据保护

## 相关章节

- [10-performance](../10-performance/) - 性能与可靠性的平衡
- [11-security](../11-security/) - 安全与可靠性
