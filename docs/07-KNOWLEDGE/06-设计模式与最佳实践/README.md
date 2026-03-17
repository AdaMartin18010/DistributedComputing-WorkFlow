# 设计模式与最佳实践

**定位**：实践层 - 工作流系统的工程实践和生产经验

---

## 核心问题

1. 如何在实际系统中应用工作流模式？
2. 如何处理分布式环境下的故障？
3. 如何优化工作流性能？
4. 如何监控和调试工作流？

---

## 模式分类

### 1. 编排模式 (Orchestration Patterns)

| 模式 | 问题 | 解决方案 | 适用场景 |
|------|------|----------|----------|
| **编排器** | 服务间协调 | 中央控制器 | 复杂流程 |
| **编舞** | 松耦合通信 | 事件驱动 | 简单流程 |
| **Saga** | 长事务 | 补偿机制 | 微服务事务 |
| **BFF** | 前端聚合 | 后端-for-前端 | 多端应用 |
| **API组合** | 数据聚合 | 组合服务 | 查询场景 |

### 2. 事务模式 (Transaction Patterns)

| 模式 | 一致性 | 性能 | 复杂度 |
|------|--------|------|--------|
| **2PC** | 强一致 | 低 | 高 |
| **TCC** | 最终一致 | 高 | 中 |
| **Saga** | 最终一致 | 高 | 中 |
| **本地消息表** | 最终一致 | 中 | 低 |
| **最大努力通知** | 弱一致 | 高 | 低 |

### 3. 容错模式 (Resilience Patterns)

| 模式 | 解决的问题 | 实现方式 |
|------|-----------|----------|
| **重试** | 瞬态故障 | 指数退避 |
| **熔断** | 级联故障 | 断路器模式 |
| **降级** | 资源不足 | 备用逻辑 |
| **舱壁** | 故障隔离 | 资源限制 |
| **超时** | 无限等待 | 超时控制 |
| **限流** | 过载保护 | 速率限制 |

---

## 最佳实践

### 工作流设计原则

1. **单一职责**
   - 每个活动只做一件事
   - 避免巨型工作流
   - 合理拆分子工作流

2. **幂等设计**
   - 所有活动必须幂等
   - 使用唯一ID去重
   - 记录已处理状态

3. **补偿完整性**
   - 每个操作都有补偿
   - 补偿本身也要幂等
   - 记录补偿状态

4. **超时控制**
   - 设置合理的超时时间
   - 区分可重试和不可重试错误
   - 超时后触发补偿

### 性能优化

**批处理**：
```go
// 批量处理提升吞吐量
func BatchProcess(items []Item) error {
    batchSize := 100
    for i := 0; i < len(items); i += batchSize {
        end := min(i+batchSize, len(items))
        batch := items[i:end]
        if err := processBatch(batch); err != nil {
            return err
        }
    }
    return nil
}
```

**并行执行**：
```go
// 并行执行独立活动
func ParallelExecute(activities []Activity) error {
    errChan := make(chan error, len(activities))
    var wg sync.WaitGroup
    
    for _, act := range activities {
        wg.Add(1)
        go func(a Activity) {
            defer wg.Done()
            if err := a.Execute(); err != nil {
                errChan <- err
            }
        }(act)
    }
    
    wg.Wait()
    close(errChan)
    
    return aggregateErrors(errChan)
}
```

### 可观测性

**分布式追踪**：
```json
{
  "traceId": "abc123",
  "spanId": "def456",
  "operation": "ProcessOrder",
  "startTime": "2026-03-18T10:00:00Z",
  "duration": "150ms",
  "tags": {
    "workflowId": "wf-123",
    "step": "payment"
  }
}
```

**关键指标**：
| 指标 | 说明 | 告警阈值 |
|------|------|----------|
| 工作流延迟 | P99执行时间 | > 5s |
| 成功率 | 完成率 | < 99.9% |
| 活动失败率 | 单个活动失败 | > 1% |
| 队列深度 | 待处理任务数 | > 1000 |
| 补偿率 | 触发补偿比例 | > 0.1% |

---

## 企业案例

### Netflix - 媒体处理工作流

**场景**：视频转码、内容分发

**方案**：
- 使用 Conductor 编排
- 分阶段处理（验证→转码→审核→发布）
- 每个阶段失败触发补偿

**效果**：
- 日均处理百万视频
- 99.99% 成功率

### Uber - 出行交易工作流

**场景**：订单、支付、派单

**方案**：
- 使用 Cadence/Temopral
- Saga模式处理支付
- 幂等设计防止重复扣款

**效果**：
- 每日数十亿交易
- 一致性保证

### Stripe - 支付处理

**场景**：全球支付、退款、争议

**方案**：
- 状态机模型
- 严格幂等性保证
- 多阶段确认

**效果**：
- 金融级一致性
- 全球合规

---

## 常见陷阱

### 1. 分布式事务误用

**反模式**：
```go
// 错误：在微服务中使用2PC
func ProcessOrder() {
    tx := BeginDistributedTransaction()
    serviceA.Update(tx)
    serviceB.Update(tx) // 网络故障导致悬挂事务
    tx.Commit()
}
```

**正确做法**：
```go
// 使用Saga模式
func ProcessOrder() {
    try {
        serviceA.Update()
        serviceB.Update()
    } catch {
        serviceA.Compensate()
        serviceB.Compensate()
    }
}
```

### 2. 超时设置不当

**问题**：
- 超时太短：频繁触发不必要的重试
- 超时太长：故障恢复慢

**建议**：
```
超时时间 = P99延迟 × 3 + 网络往返时间
```

### 3. 忽视幂等性

**后果**：
- 重复扣款
- 重复发货
- 数据不一致

**检查清单**：
- [ ] 所有活动接口幂等
- [ ] 使用唯一请求ID
- [ ] 数据库有幂等键
- [ ] 补偿操作也幂等

---

## 相关文档

- [微服务编排](微服务编排.md) - 编排vs编舞
- [长事务模式](长事务模式.md) - 2PC/TCC/Saga
- [容错设计](容错设计.md) - 重试、熔断、降级
- [可观测性](可观测性.md) - 追踪、指标、日志
- [性能优化](性能优化.md) - 批处理、缓存、并行

---

## 参考资源

- [Microservices Patterns](https://microservices.io/patterns/)
- [Designing Data-Intensive Applications](https://dataintensive.net/)
- [AWS Well-Architected](https://aws.amazon.com/architecture/well-architected/)
- [Google SRE Book](https://sre.google/sre-book/table-of-contents/)

---

**状态**：✅ 已完成  
**最后更新**：2026年3月
