# Saga 模式实现示例

本文档展示 Saga 分布式事务模式在 Go、Java、TypeScript 和 Python 中的完整实现，包括**编排式（Orchestration）**和**编舞式（Choreography）**两种模式。

---

## 目录

- [Saga 模式实现示例](#saga-模式实现示例)
  - [目录](#目录)
  - [Saga 模式概述](#saga-模式概述)
    - [什么是 Saga 模式](#什么是-saga-模式)
    - [两种实现模式](#两种实现模式)
  - [Go 实现](#go-实现)
    - [项目结构](#项目结构)
    - [1. 编排式 Saga 实现](#1-编排式-saga-实现)
    - [2. 编舞式 Saga 实现](#2-编舞式-saga-实现)
    - [运行说明](#运行说明)
    - [测试用例](#测试用例)
  - [Java 实现](#java-实现)
    - [项目结构（Maven）](#项目结构maven)
    - [1. 编排式 Saga 实现](#1-编排式-saga-实现-1)
    - [2. 编舞式 Saga 实现](#2-编舞式-saga-实现-1)
    - [运行说明](#运行说明-1)
  - [TypeScript 实现](#typescript-实现)
    - [项目结构](#项目结构-1)
    - [1. 编排式 Saga 实现](#1-编排式-saga-实现-2)
    - [2. 编舞式 Saga 实现](#2-编舞式-saga-实现-2)
    - [运行说明](#运行说明-2)
  - [Python 实现](#python-实现)
    - [项目结构](#项目结构-2)
    - [1. 编排式 Saga 实现](#1-编排式-saga-实现-3)
    - [2. 编舞式 Saga 实现](#2-编舞式-saga-实现-3)
    - [运行说明](#运行说明-3)
  - [对比总结](#对比总结)
    - [四种语言实现对比](#四种语言实现对比)
    - [模式选择建议](#模式选择建议)
    - [通用最佳实践](#通用最佳实践)

---

## Saga 模式概述

### 什么是 Saga 模式

Saga 是一种用于处理分布式事务的设计模式，将一个长事务拆分为多个本地事务，每个本地事务执行后发送事件或消息触发下一个事务。如果某个步骤失败，则执行补偿操作回滚之前的步骤。

### 两种实现模式

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Saga 模式架构图                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  【编排式 Saga (Orchestration)】                                               │
│                                                                             │
│     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐                 │
│     │  Saga       │────▶│  Service A  │     │  Service B  │                 │
│     │  Orchestrator│     │  (执行/补偿) │     │  (执行/补偿) │                 │
│     │             │◀────│             │◀────│             │                 │
│     └─────────────┘     └─────────────┘     └─────────────┘                 │
│          │                                                                 │
│          │ 集中式协调器统一管理事务流程和补偿逻辑                                  │
│                                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  【编舞式 Saga (Choreography)】                                                │
│                                                                             │
│     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐                 │
│     │  Service A  │──▶Event│  Service B  │──▶Event│  Service C  │             │
│     │  (执行后发布) │         │  (执行后发布) │         │  (执行后发布) │             │
│     │  (失败时监听) │◀────────│  (失败时补偿) │◀────────│  (失败时补偿) │             │
│     └─────────────┘         └─────────────┘         └─────────────┘         │
│                                                                             │
│          │ 分布式协作，各服务通过事件总线自主协调                                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Go 实现

### 项目结构

```
saga-go/
├── cmd/
│   └── example/
│       └── main.go
├── internal/
│   ├── orchestration/
│   │   ├── saga.go
│   │   ├── coordinator.go
│   │   └── steps.go
│   ├── choreography/
│   │   ├── event_bus.go
│   │   ├── handlers.go
│   │   └── saga.go
│   └── models/
│       └── order.go
├── pkg/
│   └── errors/
│       └── errors.go
└── go.mod
```

### 1. 编排式 Saga 实现

```go
// internal/orchestration/saga.go
package orchestration

import (
    "context"
    "fmt"
    "sync"
    "time"
)

// SagaState 表示 Saga 执行状态
type SagaState int

const (
    SagaStatePending SagaState = iota
    SagaStateRunning
    SagaStateCompleted
    SagaStateCompensating
    SagaStateCompensated
    SagaStateFailed
)

func (s SagaState) String() string {
    switch s {
    case SagaStatePending:
        return "PENDING"
    case SagaStateRunning:
        return "RUNNING"
    case SagaStateCompleted:
        return "COMPLETED"
    case SagaStateCompensating:
        return "COMPENSATING"
    case SagaStateCompensated:
        return "COMPENSATED"
    case SagaStateFailed:
        return "FAILED"
    default:
        return "UNKNOWN"
    }
}

// StepResult 表示步骤执行结果
type StepResult struct {
    StepName string
    Success  bool
    Data     interface{}
    Error    error
}

// SagaStep 定义 Saga 步骤接口
type SagaStep interface {
    // Name 返回步骤名称
    Name() string
    // Execute 执行正向操作
    Execute(ctx context.Context, sagaContext SagaContext) (interface{}, error)
    // Compensate 执行补偿操作
    Compensate(ctx context.Context, sagaContext SagaContext) error
    // CanRetry 判断是否可重试
    CanRetry(err error) bool
}

// SagaContext 保存 Saga 执行上下文
type SagaContext struct {
    SagaID      string
    Data        map[string]interface{}
    Results     map[string]StepResult
    mu          sync.RWMutex
}

// NewSagaContext 创建新的 Saga 上下文
func NewSagaContext(sagaID string) *SagaContext {
    return &SagaContext{
        SagaID:  sagaID,
        Data:    make(map[string]interface{}),
        Results: make(map[string]StepResult),
    }
}

// Set 存储数据
func (sc *SagaContext) Set(key string, value interface{}) {
    sc.mu.Lock()
    defer sc.mu.Unlock()
    sc.Data[key] = value
}

// Get 获取数据
func (sc *SagaContext) Get(key string) (interface{}, bool) {
    sc.mu.RLock()
    defer sc.mu.RUnlock()
    v, ok := sc.Data[key]
    return v, ok
}

// SetResult 存储步骤结果
func (sc *SagaContext) SetResult(stepName string, result StepResult) {
    sc.mu.Lock()
    defer sc.mu.Unlock()
    sc.Results[stepName] = result
}

// GetResult 获取步骤结果
func (sc *SagaContext) GetResult(stepName string) (StepResult, bool) {
    sc.mu.RLock()
    defer sc.mu.RUnlock()
    r, ok := sc.Results[stepName]
    return r, ok
}

// Saga 编排器定义
type Saga struct {
    ID           string
    Name         string
    Steps        []SagaStep
    state        SagaState
    context      *SagaContext
    onStepStart  func(step SagaStep)
    onStepEnd    func(step SagaStep, result StepResult)
    onSagaEnd    func(state SagaState, err error)
    mu           sync.RWMutex
}

// NewSaga 创建新的 Saga
func NewSaga(id, name string) *Saga {
    return &Saga{
        ID:      id,
        Name:    name,
        Steps:   make([]SagaStep, 0),
        state:   SagaStatePending,
        context: NewSagaContext(id),
    }
}

// AddStep 添加步骤
func (s *Saga) AddStep(step SagaStep) *Saga {
    s.Steps = append(s.Steps, step)
    return s
}

// OnStepStart 设置步骤开始回调
func (s *Saga) OnStepStart(fn func(step SagaStep)) *Saga {
    s.onStepStart = fn
    return s
}

// OnStepEnd 设置步骤结束回调
func (s *Saga) OnStepEnd(fn func(step SagaStep, result StepResult)) *Saga {
    s.onStepEnd = fn
    return s
}

// OnSagaEnd 设置 Saga 结束回调
func (s *Saga) OnSagaEnd(fn func(state SagaState, err error)) *Saga {
    s.onSagaEnd = fn
    return s
}

// Execute 执行 Saga
func (s *Saga) Execute(ctx context.Context) error {
    s.setState(SagaStateRunning)

    executedSteps := make([]SagaStep, 0, len(s.Steps))

    for _, step := range s.Steps {
        select {
        case <-ctx.Done():
            // 上下文取消，执行补偿
            s.compensate(ctx, executedSteps)
            return ctx.Err()
        default:
        }

        // 通知步骤开始
        if s.onStepStart != nil {
            s.onStepStart(step)
        }

        // 执行步骤
        data, err := step.Execute(ctx, *s.context)

        result := StepResult{
            StepName: step.Name(),
            Success:  err == nil,
            Data:     data,
            Error:    err,
        }

        s.context.SetResult(step.Name(), result)

        // 通知步骤结束
        if s.onStepEnd != nil {
            s.onStepEnd(step, result)
        }

        if err != nil {
            // 执行失败，执行补偿
            s.compensate(ctx, executedSteps)

            if s.onSagaEnd != nil {
                s.onSagaEnd(SagaStateFailed, err)
            }

            return fmt.Errorf("step %s failed: %w", step.Name(), err)
        }

        executedSteps = append(executedSteps, step)
    }

    s.setState(SagaStateCompleted)

    if s.onSagaEnd != nil {
        s.onSagaEnd(SagaStateCompleted, nil)
    }

    return nil
}

// compensate 执行补偿
func (s *Saga) compensate(ctx context.Context, steps []SagaStep) {
    s.setState(SagaStateCompensating)

    // 反向执行补偿
    for i := len(steps) - 1; i >= 0; i-- {
        step := steps[i]

        // 补偿操作应该使用新的超时上下文
        compensateCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
        defer cancel()

        if err := step.Compensate(compensateCtx, *s.context); err != nil {
            // 补偿失败需要记录日志或告警，人工介入
            fmt.Printf("CRITICAL: Compensation failed for step %s: %v\n", step.Name(), err)
        }
    }

    s.setState(SagaStateCompensated)
}

func (s *Saga) setState(state SagaState) {
    s.mu.Lock()
    defer s.mu.Unlock()
    s.state = state
}

// State 获取当前状态
func (s *Saga) State() SagaState {
    s.mu.RLock()
    defer s.mu.RUnlock()
    return s.state
}
```

```go
// internal/orchestration/steps.go
package orchestration

import (
    "context"
    "encoding/json"
    "fmt"
    "net/http"
    "strings"
    "time"
)

// CreateOrderStep 创建订单步骤
type CreateOrderStep struct {
    OrderServiceURL string
    HTTPClient      *http.Client
}

func (s *CreateOrderStep) Name() string {
    return "CreateOrder"
}

func (s *CreateOrderStep) Execute(ctx context.Context, sagaContext SagaContext) (interface{}, error) {
    // 获取订单数据
    orderData, _ := sagaContext.Get("order_data")

    reqBody, _ := json.Marshal(map[string]interface{}{
        "order": orderData,
    })

    req, err := http.NewRequestWithContext(ctx, "POST",
        s.OrderServiceURL+"/orders", strings.NewReader(string(reqBody)))
    if err != nil {
        return nil, err
    }
    req.Header.Set("Content-Type", "application/json")
    req.Header.Set("X-Saga-ID", sagaContext.SagaID)

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return nil, fmt.Errorf("failed to create order: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusCreated {
        return nil, fmt.Errorf("create order failed with status: %d", resp.StatusCode)
    }

    var result struct {
        OrderID string `json:"order_id"`
    }
    if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
        return nil, err
    }

    // 保存订单 ID 供后续步骤使用
    return result.OrderID, nil
}

func (s *CreateOrderStep) Compensate(ctx context.Context, sagaContext SagaContext) error {
    result, ok := sagaContext.GetResult("CreateOrder")
    if !ok || !result.Success {
        return nil // 步骤未成功执行，无需补偿
    }

    orderID := result.Data.(string)

    req, err := http.NewRequestWithContext(ctx, "DELETE",
        s.OrderServiceURL+"/orders/"+orderID, nil)
    if err != nil {
        return err
    }

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return fmt.Errorf("failed to cancel order: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNoContent {
        return fmt.Errorf("cancel order failed with status: %d", resp.StatusCode)
    }

    return nil
}

func (s *CreateOrderStep) CanRetry(err error) bool {
    // 网络错误可重试，业务错误不可重试
    if err == nil {
        return false
    }
    errStr := err.Error()
    return strings.Contains(errStr, "connection") ||
           strings.Contains(errStr, "timeout")
}

// ReserveInventoryStep 库存预留步骤
type ReserveInventoryStep struct {
    InventoryServiceURL string
    HTTPClient          *http.Client
}

func (s *ReserveInventoryStep) Name() string {
    return "ReserveInventory"
}

func (s *ReserveInventoryStep) Execute(ctx context.Context, sagaContext SagaContext) (interface{}, error) {
    // 获取订单 ID 和商品信息
    orderResult, _ := sagaContext.GetResult("CreateOrder")
    orderID := orderResult.Data.(string)

    items, _ := sagaContext.Get("items")

    reqBody, _ := json.Marshal(map[string]interface{}{
        "order_id": orderID,
        "items":    items,
    })

    req, err := http.NewRequestWithContext(ctx, "POST",
        s.InventoryServiceURL+"/reservations", strings.NewReader(string(reqBody)))
    if err != nil {
        return nil, err
    }
    req.Header.Set("Content-Type", "application/json")

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusCreated {
        return nil, fmt.Errorf("reserve inventory failed: %d", resp.StatusCode)
    }

    var result struct {
        ReservationID string `json:"reservation_id"`
    }
    json.NewDecoder(resp.Body).Decode(&result)

    return result.ReservationID, nil
}

func (s *ReserveInventoryStep) Compensate(ctx context.Context, sagaContext SagaContext) error {
    result, ok := sagaContext.GetResult("ReserveInventory")
    if !ok || !result.Success {
        return nil
    }

    reservationID := result.Data.(string)

    req, _ := http.NewRequestWithContext(ctx, "DELETE",
        s.InventoryServiceURL+"/reservations/"+reservationID, nil)

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    return nil
}

func (s *ReserveInventoryStep) CanRetry(err error) bool {
    return false // 库存不足等错误通常不可重试
}

// ProcessPaymentStep 支付处理步骤
type ProcessPaymentStep struct {
    PaymentServiceURL string
    HTTPClient        *http.Client
}

func (s *ProcessPaymentStep) Name() string {
    return "ProcessPayment"
}

func (s *ProcessPaymentStep) Execute(ctx context.Context, sagaContext SagaContext) (interface{}, error) {
    orderResult, _ := sagaContext.GetResult("CreateOrder")
    orderID := orderResult.Data.(string)

    amount, _ := sagaContext.Get("total_amount")

    reqBody, _ := json.Marshal(map[string]interface{}{
        "order_id": orderID,
        "amount":   amount,
        "currency": "USD",
    })

    req, _ := http.NewRequestWithContext(ctx, "POST",
        s.PaymentServiceURL+"/payments", strings.NewReader(string(reqBody)))
    req.Header.Set("Content-Type", "application/json")

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusCreated {
        return nil, fmt.Errorf("payment failed: %d", resp.StatusCode)
    }

    var result struct {
        PaymentID string `json:"payment_id"`
        Status    string `json:"status"`
    }
    json.NewDecoder(resp.Body).Decode(&result)

    return result.PaymentID, nil
}

func (s *ProcessPaymentStep) Compensate(ctx context.Context, sagaContext SagaContext) error {
    result, ok := sagaContext.GetResult("ProcessPayment")
    if !ok || !result.Success {
        return nil
    }

    paymentID := result.Data.(string)

    req, _ := http.NewRequestWithContext(ctx, "POST",
        s.PaymentServiceURL+"/payments/"+paymentID+"/refund", nil)

    resp, err := s.HTTPClient.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    return nil
}

func (s *ProcessPaymentStep) CanRetry(err error) bool {
    // 支付网关超时等可重试
    return strings.Contains(err.Error(), "timeout")
}
```

```go
// cmd/example/main.go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "time"

    "saga-go/internal/models"
    "saga-go/internal/orchestration"
)

func main() {
    httpClient := &http.Client{Timeout: 10 * time.Second}

    // 创建订单处理 Saga
    orderSaga := orchestration.NewSaga(
        generateSagaID(),
        "OrderProcessingSaga",
    ).
    OnStepStart(func(step orchestration.SagaStep) {
        fmt.Printf("▶ Starting step: %s\n", step.Name())
    }).
    OnStepEnd(func(step orchestration.SagaStep, result orchestration.StepResult) {
        status := "✓"
        if !result.Success {
            status = "✗"
        }
        fmt.Printf("%s Completed step: %s (Success: %v)\n", status, step.Name(), result.Success)
    }).
    OnSagaEnd(func(state orchestration.SagaState, err error) {
        if err != nil {
            fmt.Printf("⚠ Saga failed with state: %s, error: %v\n", state, err)
        } else {
            fmt.Printf("✓ Saga completed with state: %s\n", state)
        }
    })

    // 添加步骤
    orderSaga.
        AddStep(&orchestration.CreateOrderStep{
            OrderServiceURL: "http://order-service:8080",
            HTTPClient:      httpClient,
        }).
        AddStep(&orchestration.ReserveInventoryStep{
            InventoryServiceURL: "http://inventory-service:8080",
            HTTPClient:          httpClient,
        }).
        AddStep(&orchestration.ProcessPaymentStep{
            PaymentServiceURL: "http://payment-service:8080",
            HTTPClient:        httpClient,
        })

    // 准备 Saga 上下文数据
    sagaCtx := orderSaga.Context
    sagaCtx.Set("order_data", map[string]interface{}{
        "customer_id": "cust-123",
        "items": []map[string]interface{}{
            {"product_id": "prod-1", "quantity": 2, "price": 100.0},
            {"product_id": "prod-2", "quantity": 1, "price": 50.0},
        },
    })
    sagaCtx.Set("items", []models.OrderItem{
        {ProductID: "prod-1", Quantity: 2},
        {ProductID: "prod-2", Quantity: 1},
    })
    sagaCtx.Set("total_amount", 250.0)

    // 执行 Saga
    ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
    defer cancel()

    fmt.Println("=== Starting Order Processing Saga ===")
    if err := orderSaga.Execute(ctx); err != nil {
        log.Fatalf("Saga execution failed: %v", err)
    }

    fmt.Println("\n=== Final Saga Context ===")
    for stepName, result := range sagaCtx.Results {
        fmt.Printf("Step %s: Success=%v\n", stepName, result.Success)
    }
}

func generateSagaID() string {
    return fmt.Sprintf("saga-%d", time.Now().UnixNano())
}
```

### 2. 编舞式 Saga 实现

```go
// internal/choreography/event_bus.go
package choreography

import (
    "context"
    "encoding/json"
    "sync"
)

// EventType 事件类型
type EventType string

const (
    EventOrderCreated      EventType = "order.created"
    EventOrderCancelled    EventType = "order.cancelled"
    EventInventoryReserved EventType = "inventory.reserved"
    EventInventoryReleased EventType = "inventory.released"
    EventPaymentProcessed  EventType = "payment.processed"
    EventPaymentRefunded   EventType = "payment.refunded"
    EventSagaCompleted     EventType = "saga.completed"
    EventSagaFailed        EventType = "saga.failed"
)

// Event 事件结构
type Event struct {
    Type      EventType       `json:"type"`
    SagaID    string          `json:"saga_id"`
    Timestamp int64           `json:"timestamp"`
    Payload   json.RawMessage `json:"payload"`
    Metadata  map[string]string `json:"metadata"`
}

// EventHandler 事件处理器
type EventHandler func(ctx context.Context, event Event) error

// EventBus 事件总线接口
type EventBus interface {
    Publish(ctx context.Context, event Event) error
    Subscribe(eventType EventType, handler EventHandler) error
    Unsubscribe(eventType EventType, handler EventHandler) error
}

// InMemoryEventBus 内存事件总线实现（生产环境使用消息队列）
type InMemoryEventBus struct {
    subscribers map[EventType][]EventHandler
    mu          sync.RWMutex
}

func NewInMemoryEventBus() *InMemoryEventBus {
    return &InMemoryEventBus{
        subscribers: make(map[EventType][]EventHandler),
    }
}

func (b *InMemoryEventBus) Publish(ctx context.Context, event Event) error {
    b.mu.RLock()
    handlers := b.subscribers[event.Type]
    b.mu.RUnlock()

    for _, handler := range handlers {
        go func(h EventHandler) {
            if err := h(ctx, event); err != nil {
                // 错误处理：记录日志、重试或死信队列
            }
        }(handler)
    }

    return nil
}

func (b *InMemoryEventBus) Subscribe(eventType EventType, handler EventHandler) error {
    b.mu.Lock()
    defer b.mu.Unlock()

    b.subscribers[eventType] = append(b.subscribers[eventType], handler)
    return nil
}

func (b *InMemoryEventBus) Unsubscribe(eventType EventType, handler EventHandler) error {
    // 实现取消订阅逻辑
    return nil
}
```

```go
// internal/choreography/saga.go
package choreography

import (
    "context"
    "encoding/json"
    "fmt"
    "time"
)

// ChoreographySaga 编舞式 Saga 协调器
type ChoreographySaga struct {
    ID         string
    EventBus   EventBus
    State      SagaState
    StartTime  time.Time
    EndTime    *time.Time
    onComplete func(saga *ChoreographySaga)
    onFail     func(saga *ChoreographySaga, reason string)
}

// NewChoreographySaga 创建新的编舞式 Saga
func NewChoreographySaga(id string, eventBus EventBus) *ChoreographySaga {
    return &ChoreographySaga{
        ID:        id,
        EventBus:  eventBus,
        State:     SagaStatePending,
        StartTime: time.Now(),
    }
}

// Start 启动 Saga
func (s *ChoreographySaga) Start(ctx context.Context, initiatorEvent Event) error {
    s.State = SagaStateRunning
    return s.EventBus.Publish(ctx, initiatorEvent)
}

// Complete 标记 Saga 完成
func (s *ChoreographySaga) Complete() {
    s.State = SagaStateCompleted
    now := time.Now()
    s.EndTime = &now
    if s.onComplete != nil {
        s.onComplete(s)
    }
}

// Fail 标记 Saga 失败
func (s *ChoreographySaga) Fail(reason string) {
    s.State = SagaStateFailed
    now := time.Now()
    s.EndTime = &now
    if s.onFail != nil {
        s.onFail(s, reason)
    }
}
```

```go
// internal/choreography/handlers.go
package choreography

import (
    "context"
    "encoding/json"
    "fmt"
)

// OrderServiceHandler 订单服务事件处理器
type OrderServiceHandler struct {
    EventBus EventBus
}

func (h *OrderServiceHandler) HandleOrderCreateRequest(ctx context.Context, event Event) error {
    // 解析请求
    var req struct {
        CustomerID string      `json:"customer_id"`
        Items      interface{} `json:"items"`
    }
    if err := json.Unmarshal(event.Payload, &req); err != nil {
        return err
    }

    // 创建订单
    orderID := generateOrderID()

    fmt.Printf("[OrderService] Creating order %s for saga %s\n", orderID, event.SagaID)

    // 发布订单创建成功事件
    payload, _ := json.Marshal(map[string]string{
        "order_id": orderID,
    })

    return h.EventBus.Publish(ctx, Event{
        Type:      EventOrderCreated,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   payload,
        Metadata: map[string]string{
            "service": "order-service",
        },
    })
}

func (h *OrderServiceHandler) HandleOrderCancel(ctx context.Context, event Event) error {
    var payload struct {
        OrderID string `json:"order_id"`
    }
    json.Unmarshal(event.Payload, &payload)

    fmt.Printf("[OrderService] Cancelling order %s for saga %s\n", payload.OrderID, event.SagaID)

    // 执行取消操作

    return h.EventBus.Publish(ctx, Event{
        Type:      EventOrderCancelled,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   event.Payload,
    })
}

// InventoryServiceHandler 库存服务事件处理器
type InventoryServiceHandler struct {
    EventBus EventBus
}

func (h *InventoryServiceHandler) HandleOrderCreated(ctx context.Context, event Event) error {
    var payload struct {
        OrderID string `json:"order_id"`
    }
    json.Unmarshal(event.Payload, &payload)

    fmt.Printf("[InventoryService] Reserving inventory for order %s\n", payload.OrderID)

    // 预留库存
    reservationID := generateReservationID()

    // 发布库存预留成功事件
    respPayload, _ := json.Marshal(map[string]string{
        "order_id":       payload.OrderID,
        "reservation_id": reservationID,
    })

    return h.EventBus.Publish(ctx, Event{
        Type:      EventInventoryReserved,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   respPayload,
    })
}

func (h *InventoryServiceHandler) HandlePaymentFailed(ctx context.Context, event Event) error {
    var payload struct {
        OrderID string `json:"order_id"`
    }
    json.Unmarshal(event.Payload, &payload)

    fmt.Printf("[InventoryService] Releasing inventory for order %s (payment failed)\n", payload.OrderID)

    // 释放库存
    return h.EventBus.Publish(ctx, Event{
        Type:      EventInventoryReleased,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   event.Payload,
    })
}

// PaymentServiceHandler 支付服务事件处理器
type PaymentServiceHandler struct {
    EventBus EventBus
}

func (h *PaymentServiceHandler) HandleInventoryReserved(ctx context.Context, event Event) error {
    var payload struct {
        OrderID string  `json:"order_id"`
        Amount  float64 `json:"amount"`
    }
    json.Unmarshal(event.Payload, &payload)

    fmt.Printf("[PaymentService] Processing payment for order %s\n", payload.OrderID)

    // 模拟支付处理
    paymentID := generatePaymentID()

    respPayload, _ := json.Marshal(map[string]interface{}{
        "order_id":   payload.OrderID,
        "payment_id": paymentID,
        "amount":     payload.Amount,
    })

    return h.EventBus.Publish(ctx, Event{
        Type:      EventPaymentProcessed,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   respPayload,
    })
}

func (h *PaymentServiceHandler) HandleCompensationRequest(ctx context.Context, event Event) error {
    var payload struct {
        PaymentID string `json:"payment_id"`
    }
    json.Unmarshal(event.Payload, &payload)

    fmt.Printf("[PaymentService] Refunding payment %s\n", payload.PaymentID)

    return h.EventBus.Publish(ctx, Event{
        Type:      EventPaymentRefunded,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   event.Payload,
    })
}

// SagaCoordinator Saga 协调处理器（处理完成和失败）
type SagaCoordinator struct {
    EventBus EventBus
    sagas    map[string]*ChoreographySaga
}

func (c *SagaCoordinator) HandlePaymentProcessed(ctx context.Context, event Event) error {
    fmt.Printf("[SagaCoordinator] Saga %s completed successfully\n", event.SagaID)

    if saga, ok := c.sagas[event.SagaID]; ok {
        saga.Complete()
    }

    return c.EventBus.Publish(ctx, Event{
        Type:      EventSagaCompleted,
        SagaID:    event.SagaID,
        Timestamp: time.Now().Unix(),
        Payload:   event.Payload,
    })
}

func (c *SagaCoordinator) HandleSagaFailed(ctx context.Context, event Event) error {
    fmt.Printf("[SagaCoordinator] Saga %s failed\n", event.SagaID)

    if saga, ok := c.sagas[event.SagaID]; ok {
        saga.Fail(event.Metadata["reason"])
    }

    return nil
}

func generateOrderID() string      { return "ORD-" + generateID() }
func generateReservationID() string { return "RES-" + generateID() }
func generatePaymentID() string     { return "PAY-" + generateID() }
func generateID() string            { return fmt.Sprintf("%d", time.Now().UnixNano()) }
```

### 运行说明

```bash
# 1. 初始化项目
mkdir saga-go && cd saga-go
go mod init saga-go

# 2. 安装依赖
go get github.com/stretchr/testify
go get github.com/google/uuid

# 3. 运行编排式示例
go run cmd/example/main.go

# 4. 运行测试
go test ./...

# 5. 构建
go build -o bin/saga-example cmd/example/main.go
```

### 测试用例

```go
// internal/orchestration/saga_test.go
package orchestration

import (
    "context"
    "errors"
    "testing"
    "time"
)

// MockStep 模拟步骤用于测试
type MockStep struct {
    name           string
    executeResult  interface{}
    executeError   error
    compensateError error
    executed       bool
    compensated    bool
}

func (m *MockStep) Name() string { return m.name }

func (m *MockStep) Execute(ctx context.Context, sagaContext SagaContext) (interface{}, error) {
    m.executed = true
    return m.executeResult, m.executeError
}

func (m *MockStep) Compensate(ctx context.Context, sagaContext SagaContext) error {
    m.compensated = true
    return m.compensateError
}

func (m *MockStep) CanRetry(err error) bool { return false }

func TestSaga_SuccessfulExecution(t *testing.T) {
    step1 := &MockStep{name: "Step1", executeResult: "result1"}
    step2 := &MockStep{name: "Step2", executeResult: "result2"}
    step3 := &MockStep{name: "Step3", executeResult: "result3"}

    saga := NewSaga("test-1", "TestSaga")
    saga.AddStep(step1).AddStep(step2).AddStep(step3)

    err := saga.Execute(context.Background())

    if err != nil {
        t.Errorf("Expected no error, got %v", err)
    }

    if saga.State() != SagaStateCompleted {
        t.Errorf("Expected state COMPLETED, got %s", saga.State())
    }

    if !step1.executed || !step2.executed || !step3.executed {
        t.Error("All steps should be executed")
    }
}

func TestSaga_CompensationOnFailure(t *testing.T) {
    step1 := &MockStep{name: "Step1", executeResult: "result1"}
    step2 := &MockStep{name: "Step2", executeError: errors.New("step2 failed")}
    step3 := &MockStep{name: "Step3", executeResult: "result3"}

    saga := NewSaga("test-2", "TestSaga")
    saga.AddStep(step1).AddStep(step2).AddStep(step3)

    err := saga.Execute(context.Background())

    if err == nil {
        t.Error("Expected error")
    }

    if saga.State() != SagaStateCompensated {
        t.Errorf("Expected state COMPENSATED, got %s", saga.State())
    }

    if !step1.compensated {
        t.Error("Step1 should be compensated")
    }

    if step3.executed {
        t.Error("Step3 should not be executed")
    }
}

func TestSaga_ContextCancellation(t *testing.T) {
    step1 := &MockStep{name: "Step1", executeResult: "result1"}
    step2 := &MockStep{
        name: "Step2",
        executeResult: "result2",
    }

    saga := NewSaga("test-3", "TestSaga")
    saga.AddStep(step1).AddStep(step2)

    ctx, cancel := context.WithCancel(context.Background())

    // 在步骤1完成后取消
    saga.OnStepEnd(func(step SagaStep, result StepResult) {
        if step.Name() == "Step1" {
            cancel()
        }
    })

    err := saga.Execute(ctx)

    if err != context.Canceled {
        t.Errorf("Expected context.Canceled, got %v", err)
    }

    if !step1.compensated {
        t.Error("Step1 should be compensated on cancellation")
    }
}
```

---

## Java 实现

### 项目结构（Maven）

```
saga-java/
├── pom.xml
├── src/
│   ├── main/
│   │   ├── java/
│   │   │   └── com/example/saga/
│   │   │       ├── orchestration/
│   │   │       │   ├── Saga.java
│   │   │       │   ├── SagaStep.java
│   │   │       │   ├── SagaContext.java
│   │   │       │   └── SagaCoordinator.java
│   │   │       ├── choreography/
│   │   │       │   ├── EventBus.java
││   │   │       │   ├── SagaEventHandler.java
│   │   │       │   └── ChoreographySaga.java
│   │   │       ├── steps/
│   │   │       │   ├── CreateOrderStep.java
│   │   │       │   ├── ReserveInventoryStep.java
│   │   │       │   └── ProcessPaymentStep.java
│   │   │       └── SagaApplication.java
│   │   └── resources/
│   └── test/
│       └── java/
│           └── com/example/saga/
│               └── SagaTest.java
```

### 1. 编排式 Saga 实现

```java
// src/main/java/com/example/saga/orchestration/SagaState.java
package com.example.saga.orchestration;

public enum SagaState {
    PENDING("待执行"),
    RUNNING("执行中"),
    COMPLETED("已完成"),
    COMPENSATING("补偿中"),
    COMPENSATED("已补偿"),
    FAILED("失败");

    private final String description;

    SagaState(String description) {
        this.description = description;
    }

    public String getDescription() {
        return description;
    }
}
```

```java
// src/main/java/com/example/saga/orchestration/SagaContext.java
package com.example.saga.orchestration;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/**
 * Saga 执行上下文
 * 线程安全的上下文存储，用于步骤间数据传递
 */
public class SagaContext {
    private final String sagaId;
    private final ConcurrentMap<String, Object> data = new ConcurrentHashMap<>();
    private final ConcurrentMap<String, StepResult> results = new ConcurrentHashMap<>();

    public SagaContext(String sagaId) {
        this.sagaId = sagaId;
    }

    public String getSagaId() {
        return sagaId;
    }

    public void set(String key, Object value) {
        data.put(key, value);
    }

    @SuppressWarnings("unchecked")
    public <T> T get(String key) {
        return (T) data.get(key);
    }

    public void setResult(String stepName, StepResult result) {
        results.put(stepName, result);
    }

    public StepResult getResult(String stepName) {
        return results.get(stepName);
    }

    public ConcurrentMap<String, StepResult> getAllResults() {
        return new ConcurrentHashMap<>(results);
    }
}
```

```java
// src/main/java/com/example/saga/orchestration/StepResult.java
package com.example.saga.orchestration;

/**
 * 步骤执行结果
 */
public class StepResult {
    private final String stepName;
    private final boolean success;
    private final Object data;
    private final Throwable error;

    private StepResult(Builder builder) {
        this.stepName = builder.stepName;
        this.success = builder.success;
        this.data = builder.data;
        this.error = builder.error;
    }

    public static Builder builder() {
        return new Builder();
    }

    // Getters
    public String getStepName() { return stepName; }
    public boolean isSuccess() { return success; }
    public Object getData() { return data; }
    public Throwable getError() { return error; }

    public static class Builder {
        private String stepName;
        private boolean success;
        private Object data;
        private Throwable error;

        public Builder stepName(String stepName) {
            this.stepName = stepName;
            return this;
        }

        public Builder success(boolean success) {
            this.success = success;
            return this;
        }

        public Builder data(Object data) {
            this.data = data;
            return this;
        }

        public Builder error(Throwable error) {
            this.error = error;
            return this;
        }

        public StepResult build() {
            return new StepResult(this);
        }
    }
}
```

```java
// src/main/java/com/example/saga/orchestration/SagaStep.java
package com.example.saga.orchestration;

import java.util.concurrent.CompletableFuture;

/**
 * Saga 步骤接口
 * @param <R> 执行结果类型
 */
public interface SagaStep<R> {

    /**
     * 步骤名称
     */
    String getName();

    /**
     * 执行正向操作
     * @param context Saga 上下文
     * @return 异步执行结果
     */
    CompletableFuture<R> execute(SagaContext context);

    /**
     * 执行补偿操作
     * @param context Saga 上下文
     * @return 异步补偿结果
     */
    CompletableFuture<Void> compensate(SagaContext context);

    /**
     * 判断错误是否可重试
     * @param throwable 错误
     * @return 是否可重试
     */
    default boolean isRetryable(Throwable throwable) {
        return false;
    }

    /**
     * 获取最大重试次数
     */
    default int getMaxRetries() {
        return 3;
    }

    /**
     * 获取重试间隔（毫秒）
     */
    default long getRetryDelayMs() {
        return 1000;
    }
}
```

```java
// src/main/java/com/example/saga/orchestration/Saga.java
package com.example.saga.orchestration;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

/**
 * Saga 编排器
 * 管理多个步骤的执行和补偿
 */
public class Saga {
    private static final Logger logger = LoggerFactory.getLogger(Saga.class);

    private final String id;
    private final String name;
    private final List<SagaStep<?>> steps = new ArrayList<>();
    private final AtomicReference<SagaState> state = new AtomicReference<>(SagaState.PENDING);
    private final SagaContext context;

    // 回调
    private Consumer<SagaStep<?>> onStepStart;
    private BiConsumer<SagaStep<?>, StepResult> onStepEnd;
    private BiConsumer<SagaState, Throwable> onSagaEnd;

    public Saga(String id, String name) {
        this.id = id;
        this.name = name;
        this.context = new SagaContext(id);
    }

    public Saga addStep(SagaStep<?> step) {
        steps.add(step);
        return this;
    }

    public Saga onStepStart(Consumer<SagaStep<?>> callback) {
        this.onStepStart = callback;
        return this;
    }

    public Saga onStepEnd(BiConsumer<SagaStep<?>, StepResult> callback) {
        this.onStepEnd = callback;
        return this;
    }

    public Saga onSagaEnd(BiConsumer<SagaState, Throwable> callback) {
        this.onSagaEnd = callback;
        return this;
    }

    /**
     * 执行 Saga
     * @return CompletableFuture 表示异步执行结果
     */
    public CompletableFuture<Void> execute() {
        if (!state.compareAndSet(SagaState.PENDING, SagaState.RUNNING)) {
            return CompletableFuture.failedFuture(
                new IllegalStateException("Saga is not in PENDING state")
            );
        }

        logger.info("Starting Saga [{}]: {}", id, name);

        List<SagaStep<?>> executedSteps = Collections.synchronizedList(new ArrayList<>());

        CompletableFuture<Void> future = CompletableFuture.completedFuture(null);

        for (SagaStep<?> step : steps) {
            future = future.thenCompose(v -> executeStep(step, executedSteps));
        }

        return future
            .thenRun(() -> {
                state.set(SagaState.COMPLETED);
                logger.info("Saga [{}] completed successfully", id);
                if (onSagaEnd != null) {
                    onSagaEnd.accept(SagaState.COMPLETED, null);
                }
            })
            .exceptionally(throwable -> {
                Throwable cause = throwable instanceof CompletionException
                    ? throwable.getCause() : throwable;
                logger.error("Saga [{}] failed: {}", id, cause.getMessage());

                // 执行补偿
                return compensate(executedSteps, cause).join();
            });
    }

    @SuppressWarnings("unchecked")
    private <R> CompletableFuture<Void> executeStep(SagaStep<R> step, List<SagaStep<?>> executedSteps) {
        return CompletableFuture.runAsync(() -> {
            if (onStepStart != null) {
                onStepStart.accept(step);
            }
        })
        .thenCompose(v -> executeWithRetry(step))
        .thenAccept(result -> {
            executedSteps.add(step);

            StepResult stepResult = StepResult.builder()
                .stepName(step.getName())
                .success(true)
                .data(result)
                .build();

            context.setResult(step.getName(), stepResult);

            if (onStepEnd != null) {
                onStepEnd.accept(step, stepResult);
            }

            logger.debug("Step [{}] completed successfully", step.getName());
        })
        .exceptionally(throwable -> {
            Throwable cause = throwable instanceof CompletionException
                ? throwable.getCause() : throwable;

            StepResult stepResult = StepResult.builder()
                .stepName(step.getName())
                .success(false)
                .error(cause)
                .build();

            context.setResult(step.getName(), stepResult);

            if (onStepEnd != null) {
                onStepEnd.accept(step, stepResult);
            }

            throw new CompletionException(cause);
        });
    }

    @SuppressWarnings("unchecked")
    private <R> CompletableFuture<R> executeWithRetry(SagaStep<R> step) {
        return executeWithRetryInternal(step, 0);
    }

    private <R> CompletableFuture<R> executeWithRetryInternal(SagaStep<R> step, int attempt) {
        return step.execute(context)
            .exceptionallyCompose(throwable -> {
                if (attempt < step.getMaxRetries() && step.isRetryable(throwable)) {
                    logger.warn("Step [{}] failed, retrying ({}/{}): {}",
                        step.getName(), attempt + 1, step.getMaxRetries(), throwable.getMessage());

                    return CompletableFuture.supplyAsync(() -> {
                        try {
                            Thread.sleep(step.getRetryDelayMs() * (attempt + 1));
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                        return null;
                    }).thenCompose(v -> executeWithRetryInternal(step, attempt + 1));
                }
                throw new CompletionException(throwable);
            });
    }

    private Void compensate(List<SagaStep<?>> executedSteps, Throwable cause) {
        state.set(SagaState.COMPENSATING);
        logger.info("Starting compensation for Saga [{}]", id);

        List<Throwable> compensationErrors = new ArrayList<>();

        // 反向执行补偿
        for (int i = executedSteps.size() - 1; i >= 0; i--) {
            SagaStep<?> step = executedSteps.get(i);
            try {
                step.compensate(context).join();
                logger.info("Compensation for step [{}] completed", step.getName());
            } catch (Exception e) {
                logger.error("Compensation for step [{}] failed: {}", step.getName(), e.getMessage());
                compensationErrors.add(e);
            }
        }

        if (compensationErrors.isEmpty()) {
            state.set(SagaState.COMPENSATED);
            logger.info("Saga [{}] compensated successfully", id);
        } else {
            state.set(SagaState.FAILED);
            logger.error("Saga [{}] compensation had {} failures", id, compensationErrors.size());
        }

        if (onSagaEnd != null) {
            onSagaEnd.accept(state.get(), cause);
        }

        return null;
    }

    public SagaState getState() {
        return state.get();
    }

    public SagaContext getContext() {
        return context;
    }

    public String getId() {
        return id;
    }
}
```

```java
// src/main/java/com/example/saga/steps/CreateOrderStep.java
package com.example.saga.steps;

import com.example.saga.orchestration.SagaContext;
import com.example.saga.orchestration.SagaStep;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.web.client.RestTemplate;

import java.util.Map;
import java.util.concurrent.CompletableFuture;

/**
 * 创建订单步骤
 */
public class CreateOrderStep implements SagaStep<String> {
    private static final Logger logger = LoggerFactory.getLogger(CreateOrderStep.class);

    private final RestTemplate restTemplate;
    private final String orderServiceUrl;

    public CreateOrderStep(RestTemplate restTemplate, String orderServiceUrl) {
        this.restTemplate = restTemplate;
        this.orderServiceUrl = orderServiceUrl;
    }

    @Override
    public String getName() {
        return "CreateOrder";
    }

    @Override
    public CompletableFuture<String> execute(SagaContext context) {
        return CompletableFuture.supplyAsync(() -> {
            logger.info("Creating order for saga {}", context.getSagaId());

            @SuppressWarnings("unchecked")
            Map<String, Object> orderData = context.get("orderData");

            // 调用订单服务
            Map<String, Object> response = restTemplate.postForObject(
                orderServiceUrl + "/orders",
                orderData,
                Map.class
            );

            String orderId = (String) response.get("orderId");
            logger.info("Order created: {}", orderId);

            return orderId;
        });
    }

    @Override
    public CompletableFuture<Void> compensate(SagaContext context) {
        return CompletableFuture.runAsync(() -> {
            StepResult result = context.getResult("CreateOrder");
            if (result == null || !result.isSuccess()) {
                return;
            }

            String orderId = (String) result.getData();
            logger.info("Cancelling order: {}", orderId);

            restTemplate.delete(orderServiceUrl + "/orders/" + orderId);
        });
    }

    @Override
    public boolean isRetryable(Throwable throwable) {
        String message = throwable.getMessage();
        return message != null && (message.contains("timeout") || message.contains("connection"));
    }
}
```

### 2. 编舞式 Saga 实现

```java
// src/main/java/com/example/saga/choreography/EventBus.java
package com.example.saga.choreography;

import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;

/**
 * 事件总线接口
 */
public interface EventBus {

    /**
     * 发布事件
     */
    CompletableFuture<Void> publish(SagaEvent event);

    /**
     * 订阅事件
     */
    void subscribe(String eventType, Consumer<SagaEvent> handler);

    /**
     * 取消订阅
     */
    void unsubscribe(String eventType, Consumer<SagaEvent> handler);
}
```

```java
// src/main/java/com/example/saga/choreography/SagaEvent.java
package com.example.saga.choreography;

import java.time.Instant;
import java.util.HashMap;
import java.util.Map;
import java.util.UUID;

/**
 * Saga 事件
 */
public class SagaEvent {
    private final String id;
    private final String sagaId;
    private final String type;
    private final Instant timestamp;
    private final Map<String, Object> payload;
    private final Map<String, String> metadata;

    private SagaEvent(Builder builder) {
        this.id = builder.id != null ? builder.id : UUID.randomUUID().toString();
        this.sagaId = builder.sagaId;
        this.type = builder.type;
        this.timestamp = builder.timestamp != null ? builder.timestamp : Instant.now();
        this.payload = new HashMap<>(builder.payload);
        this.metadata = new HashMap<>(builder.metadata);
    }

    public static Builder builder() {
        return new Builder();
    }

    // Getters
    public String getId() { return id; }
    public String getSagaId() { return sagaId; }
    public String getType() { return type; }
    public Instant getTimestamp() { return timestamp; }
    public Map<String, Object> getPayload() { return new HashMap<>(payload); }
    public Map<String, String> getMetadata() { return new HashMap<>(metadata); }

    public static class Builder {
        private String id;
        private String sagaId;
        private String type;
        private Instant timestamp;
        private Map<String, Object> payload = new HashMap<>();
        private Map<String, String> metadata = new HashMap<>();

        public Builder id(String id) {
            this.id = id;
            return this;
        }

        public Builder sagaId(String sagaId) {
            this.sagaId = sagaId;
            return this;
        }

        public Builder type(String type) {
            this.type = type;
            return this;
        }

        public Builder timestamp(Instant timestamp) {
            this.timestamp = timestamp;
            return this;
        }

        public Builder payload(Map<String, Object> payload) {
            this.payload = payload;
            return this;
        }

        public Builder addPayloadEntry(String key, Object value) {
            this.payload.put(key, value);
            return this;
        }

        public Builder metadata(Map<String, String> metadata) {
            this.metadata = metadata;
            return this;
        }

        public SagaEvent build() {
            if (sagaId == null || type == null) {
                throw new IllegalArgumentException("sagaId and type are required");
            }
            return new SagaEvent(this);
        }
    }
}
```

```java
// src/main/java/com/example/saga/choreography/InMemoryEventBus.java
package com.example.saga.choreography;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.Consumer;

/**
 * 内存事件总线实现
 * 生产环境应使用 Kafka、RabbitMQ 等消息队列
 */
public class InMemoryEventBus implements EventBus {
    private static final Logger logger = LoggerFactory.getLogger(InMemoryEventBus.class);

    private final Map<String, List<Consumer<SagaEvent>>> subscribers = new ConcurrentHashMap<>();

    @Override
    public CompletableFuture<Void> publish(SagaEvent event) {
        return CompletableFuture.runAsync(() -> {
            logger.debug("Publishing event: {} for saga {}", event.getType(), event.getSagaId());

            List<Consumer<SagaEvent>> handlers = subscribers.get(event.getType());
            if (handlers != null) {
                handlers.forEach(handler -> {
                    // 异步处理，避免阻塞
                    CompletableFuture.runAsync(() -> handler.accept(event))
                        .exceptionally(throwable -> {
                            logger.error("Error handling event: {}", event.getType(), throwable);
                            return null;
                        });
                });
            }
        });
    }

    @Override
    public void subscribe(String eventType, Consumer<SagaEvent> handler) {
        subscribers.computeIfAbsent(eventType, k -> new CopyOnWriteArrayList<>()).add(handler);
        logger.debug("Subscribed handler for event type: {}", eventType);
    }

    @Override
    public void unsubscribe(String eventType, Consumer<SagaEvent> handler) {
        List<Consumer<SagaEvent>> handlers = subscribers.get(eventType);
        if (handlers != null) {
            handlers.remove(handler);
        }
    }
}
```

### 运行说明

```bash
# 1. 创建 Maven 项目
mvn archetype:generate \
  -DgroupId=com.example \
  -DartifactId=saga-java \
  -DarchetypeArtifactId=maven-archetype-quickstart \
  -DinteractiveMode=false

# 2. 添加依赖到 pom.xml
# （Spring Boot, Lombok, SLF4J, JUnit 等）

# 3. 编译
mvn clean compile

# 4. 运行测试
mvn test

# 5. 打包
mvn package

# 6. 运行
java -jar target/saga-java-1.0-SNAPSHOT.jar
```

---

## TypeScript 实现

### 项目结构

```
saga-ts/
├── src/
│   ├── orchestration/
│   │   ├── saga.ts
│   │   ├── saga-step.ts
│   │   └── saga-context.ts
│   ├── choreography/
│   │   ├── event-bus.ts
│   │   └── saga-coordinator.ts
│   └── examples/
│       └── order-saga.ts
├── tests/
│   └── saga.test.ts
├── package.json
└── tsconfig.json
```

### 1. 编排式 Saga 实现

```typescript
// src/orchestration/types.ts

/**
 * Saga 执行状态
 */
export enum SagaState {
  PENDING = 'PENDING',
  RUNNING = 'RUNNING',
  COMPLETED = 'COMPLETED',
  COMPENSATING = 'COMPENSATING',
  COMPENSATED = 'COMPENSATED',
  FAILED = 'FAILED',
}

/**
 * 步骤执行结果
 */
export interface StepResult<T = unknown> {
  stepName: string;
  success: boolean;
  data?: T;
  error?: Error;
}

/**
 * Saga 配置选项
 */
export interface SagaOptions {
  maxRetries?: number;
  retryDelayMs?: number;
  compensationTimeoutMs?: number;
}
```

```typescript
// src/orchestration/saga-context.ts

import { StepResult } from './types';

/**
 * Saga 执行上下文
 * 用于步骤间数据传递和状态共享
 */
export class SagaContext {
  private data = new Map<string, unknown>();
  private results = new Map<string, StepResult>();

  constructor(public readonly sagaId: string) {}

  set<T>(key: string, value: T): void {
    this.data.set(key, value);
  }

  get<T>(key: string): T | undefined {
    return this.data.get(key) as T | undefined;
  }

  setResult(stepName: string, result: StepResult): void {
    this.results.set(stepName, result);
  }

  getResult(stepName: string): StepResult | undefined {
    return this.results.get(stepName);
  }

  getAllResults(): Map<string, StepResult> {
    return new Map(this.results);
  }
}
```

```typescript
// src/orchestration/saga-step.ts

import { SagaContext } from './saga-context';

/**
 * Saga 步骤接口
 */
export interface SagaStep<T = unknown> {
  readonly name: string;

  /**
   * 执行正向操作
   */
  execute(context: SagaContext): Promise<T>;

  /**
   * 执行补偿操作
   */
  compensate(context: SagaContext): Promise<void>;

  /**
   * 判断错误是否可重试
   */
  isRetryable?(error: Error): boolean;

  /**
   * 最大重试次数
   */
  readonly maxRetries?: number;

  /**
   * 重试延迟（毫秒）
   */
  readonly retryDelayMs?: number;
}

/**
 * 抽象步骤基类
 */
export abstract class AbstractSagaStep<T = unknown> implements SagaStep<T> {
  abstract readonly name: string;
  maxRetries = 3;
  retryDelayMs = 1000;

  abstract execute(context: SagaContext): Promise<T>;
  abstract compensate(context: SagaContext): Promise<void>;

  isRetryable(error: Error): boolean {
    // 默认：网络错误可重试
    const retryableErrors = ['ETIMEDOUT', 'ECONNREFUSED', 'ENOTFOUND', 'timeout'];
    return retryableErrors.some(e => error.message.includes(e));
  }

  protected async sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}
```

```typescript
// src/orchestration/saga.ts

import { EventEmitter } from 'events';
import { SagaContext } from './saga-context';
import { SagaStep } from './saga-step';
import { SagaState, StepResult, SagaOptions } from './types';

/**
 * Saga 事件类型
 */
export interface SagaEvents {
  'step:start': (step: SagaStep) => void;
  'step:end': (step: SagaStep, result: StepResult) => void;
  'saga:end': (state: SagaState, error?: Error) => void;
  'compensation:start': (failedStep: string) => void;
  'compensation:end': (success: boolean) => void;
}

/**
 * Saga 编排器
 */
export class Saga extends EventEmitter<SagaEvents> {
  private steps: SagaStep[] = [];
  private state: SagaState = SagaState.PENDING;
  private context: SagaContext;
  private options: Required<SagaOptions>;

  private static readonly DEFAULT_OPTIONS: Required<SagaOptions> = {
    maxRetries: 3,
    retryDelayMs: 1000,
    compensationTimeoutMs: 30000,
  };

  constructor(
    public readonly id: string,
    public readonly name: string,
    options: SagaOptions = {}
  ) {
    super();
    this.context = new SagaContext(id);
    this.options = { ...Saga.DEFAULT_OPTIONS, ...options };
  }

  /**
   * 添加步骤
   */
  addStep<T>(step: SagaStep<T>): this {
    this.steps.push(step);
    return this;
  }

  /**
   * 执行 Saga
   */
  async execute(): Promise<void> {
    if (this.state !== SagaState.PENDING) {
      throw new Error(`Saga is not in PENDING state: ${this.state}`);
    }

    this.state = SagaState.RUNNING;
    console.log(`[Saga ${this.id}] Starting: ${this.name}`);

    const executedSteps: SagaStep[] = [];

    try {
      for (const step of this.steps) {
        await this.executeStep(step, executedSteps);
      }

      this.state = SagaState.COMPLETED;
      console.log(`[Saga ${this.id}] Completed successfully`);
      this.emit('saga:end', SagaState.COMPLETED);
    } catch (error) {
      const sagaError = error instanceof Error ? error : new Error(String(error));
      console.error(`[Saga ${this.id}] Failed:`, sagaError.message);

      // 执行补偿
      await this.compensate(executedSteps, sagaError);
      throw sagaError;
    }
  }

  /**
   * 执行单个步骤（带重试）
   */
  private async executeStep(step: SagaStep, executedSteps: SagaStep[]): Promise<void> {
    this.emit('step:start', step);

    const maxRetries = step.maxRetries ?? this.options.maxRetries;
    const retryDelayMs = step.retryDelayMs ?? this.options.retryDelayMs;

    let lastError: Error | undefined;

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
      try {
        const data = await step.execute(this.context);

        const result: StepResult = {
          stepName: step.name,
          success: true,
          data,
        };

        this.context.setResult(step.name, result);
        executedSteps.push(step);

        this.emit('step:end', step, result);
        console.log(`[Saga ${this.id}] Step "${step.name}" completed`);
        return;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));

        if (attempt < maxRetries && step.isRetryable?.(lastError)) {
          console.warn(
            `[Saga ${this.id}] Step "${step.name}" failed, retrying (${attempt + 1}/${maxRetries})`
          );
          await this.sleep(retryDelayMs * (attempt + 1));
        } else {
          break;
        }
      }
    }

    const result: StepResult = {
      stepName: step.name,
      success: false,
      error: lastError,
    };

    this.context.setResult(step.name, result);
    this.emit('step:end', step, result);

    throw lastError;
  }

  /**
   * 执行补偿
   */
  private async compensate(executedSteps: SagaStep[], error: Error): Promise<void> {
    this.state = SagaState.COMPENSATING;
    this.emit('compensation:start', executedSteps[executedSteps.length - 1]?.name ?? 'unknown');

    console.log(`[Saga ${this.id}] Starting compensation for ${executedSteps.length} steps`);

    const compensationErrors: Error[] = [];

    // 反向执行补偿
    for (let i = executedSteps.length - 1; i >= 0; i--) {
      const step = executedSteps[i];

      try {
        // 使用超时包装补偿操作
        await this.withTimeout(
          step.compensate(this.context),
          this.options.compensationTimeoutMs,
          `Compensation for step "${step.name}" timed out`
        );

        console.log(`[Saga ${this.id}] Compensated step: ${step.name}`);
      } catch (compError) {
        const wrappedError = compError instanceof Error ? compError : new Error(String(compError));
        console.error(`[Saga ${this.id}] Compensation failed for step "${step.name}":`, wrappedError);
        compensationErrors.push(wrappedError);
      }
    }

    const allCompensated = compensationErrors.length === 0;
    this.state = allCompensated ? SagaState.COMPENSATED : SagaState.FAILED;

    this.emit('compensation:end', allCompensated);
    this.emit('saga:end', this.state, error);

    if (!allCompensated) {
      console.error(`[Saga ${this.id}] Compensation had ${compensationErrors.length} failures`);
    }
  }

  /**
   * 带超时的 Promise 包装
   */
  private async withTimeout<T>(promise: Promise<T>, ms: number, message: string): Promise<T> {
    return Promise.race([
      promise,
      new Promise<T>((_, reject) =>
        setTimeout(() => reject(new Error(message)), ms)
      ),
    ]);
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  getState(): SagaState {
    return this.state;
  }

  getContext(): SagaContext {
    return this.context;
  }
}
```

```typescript
// src/examples/order-saga.ts

import { Saga } from '../orchestration/saga';
import { AbstractSagaStep, SagaContext } from '../orchestration';

// 模拟 HTTP 客户端
const httpClient = {
  async post(url: string, data: unknown): Promise<unknown> {
    console.log(`  → POST ${url}`, data);
    // 模拟成功响应
    return { id: Math.random().toString(36).substring(7) };
  },

  async delete(url: string): Promise<void> {
    console.log(`  → DELETE ${url}`);
  },
};

/**
 * 创建订单步骤
 */
class CreateOrderStep extends AbstractSagaStep<string> {
  readonly name = 'CreateOrder';

  async execute(context: SagaContext): Promise<string> {
    const orderData = context.get('orderData');
    const response = await httpClient.post('/api/orders', orderData);
    return (response as { id: string }).id;
  }

  async compensate(context: SagaContext): Promise<void> {
    const result = context.getResult('CreateOrder');
    if (result?.success) {
      const orderId = result.data as string;
      await httpClient.delete(`/api/orders/${orderId}`);
    }
  }
}

/**
 * 预留库存步骤
 */
class ReserveInventoryStep extends AbstractSagaStep<string> {
  readonly name = 'ReserveInventory';

  async execute(context: SagaContext): Promise<string> {
    const orderId = context.getResult('CreateOrder')?.data as string;
    const items = context.get('items');
    const response = await httpClient.post('/api/inventory/reserve', {
      orderId,
      items,
    });
    return (response as { id: string }).id;
  }

  async compensate(context: SagaContext): Promise<void> {
    const result = context.getResult('ReserveInventory');
    if (result?.success) {
      const reservationId = result.data as string;
      await httpClient.delete(`/api/inventory/reserve/${reservationId}`);
    }
  }
}

/**
 * 处理支付步骤
 */
class ProcessPaymentStep extends AbstractSagaStep<string> {
  readonly name = 'ProcessPayment';

  async execute(context: SagaContext): Promise<string> {
    const orderId = context.getResult('CreateOrder')?.data as string;
    const amount = context.get('totalAmount') as number;
    const response = await httpClient.post('/api/payments', {
      orderId,
      amount,
      currency: 'USD',
    });
    return (response as { id: string }).id;
  }

  async compensate(context: SagaContext): Promise<void> {
    const result = context.getResult('ProcessPayment');
    if (result?.success) {
      const paymentId = result.data as string;
      await httpClient.post(`/api/payments/${paymentId}/refund`, {});
    }
  }
}

// 示例使用
async function main() {
  const saga = new Saga('order-123', 'OrderProcessingSaga', {
    maxRetries: 2,
    retryDelayMs: 500,
  });

  // 设置事件监听
  saga
    .on('step:start', step => {
      console.log(`▶ Starting step: ${step.name}`);
    })
    .on('step:end', (step, result) => {
      const icon = result.success ? '✓' : '✗';
      console.log(`${icon} Completed step: ${step.name}`);
    })
    .on('saga:end', (state, error) => {
      if (error) {
        console.log(`⚠ Saga ended with state: ${state}, error: ${error.message}`);
      } else {
        console.log(`✓ Saga completed: ${state}`);
      }
    });

  // 添加步骤
  saga
    .addStep(new CreateOrderStep())
    .addStep(new ReserveInventoryStep())
    .addStep(new ProcessPaymentStep());

  // 准备上下文数据
  saga.getContext().set('orderData', {
    customerId: 'cust-456',
    items: [
      { productId: 'prod-1', quantity: 2 },
    ],
  });
  saga.getContext().set('items', [{ productId: 'prod-1', quantity: 2 }]);
  saga.getContext().set('totalAmount', 199.99);

  try {
    await saga.execute();
    console.log('\nFinal state:', saga.getState());
    console.log('Results:', saga.getContext().getAllResults());
  } catch (error) {
    console.error('\nSaga failed:', error);
    console.log('Final state:', saga.getState());
  }
}

main().catch(console.error);
```

### 2. 编舞式 Saga 实现

```typescript
// src/choreography/event-bus.ts

import { EventEmitter } from 'events';

/**
 * Saga 事件结构
 */
export interface SagaEvent {
  id: string;
  sagaId: string;
  type: string;
  timestamp: Date;
  payload: Record<string, unknown>;
  metadata?: Record<string, string>;
}

/**
 * 事件处理器类型
 */
export type EventHandler = (event: SagaEvent) => Promise<void> | void;

/**
 * 事件总线接口
 */
export interface EventBus {
  publish(event: SagaEvent): Promise<void>;
  subscribe(eventType: string, handler: EventHandler): void;
  unsubscribe(eventType: string, handler: EventHandler): void;
}

/**
 * 内存事件总线实现
 */
export class InMemoryEventBus extends EventEmitter implements EventBus {
  private handlers = new Map<string, Set<EventHandler>>();

  async publish(event: SagaEvent): Promise<void> {
    console.log(`📤 Publishing event: ${event.type} (saga: ${event.sagaId})`);

    const eventHandlers = this.handlers.get(event.type);
    if (eventHandlers) {
      const promises = Array.from(eventHandlers).map(async handler => {
        try {
          await handler(event);
        } catch (error) {
          console.error(`Error handling event ${event.type}:`, error);
        }
      });

      await Promise.all(promises);
    }
  }

  subscribe(eventType: string, handler: EventHandler): void {
    if (!this.handlers.has(eventType)) {
      this.handlers.set(eventType, new Set());
    }
    this.handlers.get(eventType)!.add(handler);
    console.log(`📥 Subscribed handler for: ${eventType}`);
  }

  unsubscribe(eventType: string, handler: EventHandler): void {
    this.handlers.get(eventType)?.delete(handler);
  }
}
```

```typescript
// src/choreography/saga-coordinator.ts

import { EventBus, SagaEvent } from './event-bus';
import { SagaState } from '../orchestration/types';

/**
 * 编舞式 Saga 协调器
 */
export class ChoreographySaga {
  private state: SagaState = SagaState.PENDING;
  private startTime = Date.now();
  private endTime?: number;

  constructor(
    public readonly id: string,
    private eventBus: EventBus,
    private onComplete?: (saga: ChoreographySaga) => void,
    private onFail?: (saga: ChoreographySaga, reason: string) => void
  ) {
    this.registerEventHandlers();
  }

  /**
   * 启动 Saga
   */
  async start(initiatorEvent: Omit<SagaEvent, 'id' | 'timestamp'>): Promise<void> {
    this.state = SagaState.RUNNING;

    const event: SagaEvent = {
      ...initiatorEvent,
      id: this.generateId(),
      timestamp: new Date(),
    };

    await this.eventBus.publish(event);
  }

  /**
   * 注册事件处理器
   */
  private registerEventHandlers(): void {
    // 监听完成事件
    this.eventBus.subscribe('saga.completed', event => {
      if (event.sagaId === this.id) {
        this.complete();
      }
    });

    // 监听失败事件
    this.eventBus.subscribe('saga.failed', event => {
      if (event.sagaId === this.id) {
        this.fail(event.payload.reason as string);
      }
    });
  }

  private complete(): void {
    this.state = SagaState.COMPLETED;
    this.endTime = Date.now();
    this.onComplete?.(this);
  }

  private fail(reason: string): void {
    this.state = SagaState.FAILED;
    this.endTime = Date.now();
    this.onFail?.(this, reason);
  }

  getState(): SagaState {
    return this.state;
  }

  getDuration(): number {
    return (this.endTime ?? Date.now()) - this.startTime;
  }

  private generateId(): string {
    return `evt-${Date.now()}-${Math.random().toString(36).substring(2, 9)}`;
  }
}
```

### 运行说明

```bash
# 1. 初始化项目
mkdir saga-ts && cd saga-ts
npm init -y

# 2. 安装依赖
npm install typescript @types/node --save-dev
npm install vitest --save-dev

# 3. 初始化 TypeScript
npx tsc --init

# 4. 编译运行
npx ts-node src/examples/order-saga.ts

# 5. 运行测试
npx vitest
```

---

## Python 实现

### 项目结构

```
saga_python/
├── saga/
│   ├── __init__.py
│   ├── orchestration.py
│   ├── choreography.py
│   └── types.py
├── examples/
│   └── order_example.py
├── tests/
│   └── test_saga.py
└── requirements.txt
```

### 1. 编排式 Saga 实现

```python
# saga/types.py
"""
Saga 类型定义
"""
from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Any, Optional, Dict
from datetime import datetime


class SagaState(Enum):
    """Saga 执行状态"""
    PENDING = "PENDING"
    RUNNING = "RUNNING"
    COMPLETED = "COMPLETED"
    COMPENSATING = "COMPENSATING"
    COMPENSATED = "COMPENSATED"
    FAILED = "FAILED"


@dataclass
class StepResult:
    """步骤执行结果"""
    step_name: str
    success: bool
    data: Any = None
    error: Optional[Exception] = None
    timestamp: datetime = field(default_factory=datetime.now)


@dataclass
class SagaContext:
    """Saga 执行上下文"""
    saga_id: str
    _data: Dict[str, Any] = field(default_factory=dict)
    _results: Dict[str, StepResult] = field(default_factory=dict)

    def set(self, key: str, value: Any) -> None:
        """存储数据"""
        self._data[key] = value

    def get(self, key: str, default: Any = None) -> Any:
        """获取数据"""
        return self._data.get(key, default)

    def set_result(self, step_name: str, result: StepResult) -> None:
        """存储步骤结果"""
        self._results[step_name] = result

    def get_result(self, step_name: str) -> Optional[StepResult]:
        """获取步骤结果"""
        return self._results.get(step_name)

    @property
    def results(self) -> Dict[str, StepResult]:
        """获取所有结果"""
        return self._results.copy()
```

```python
# saga/orchestration.py
"""
编排式 Saga 实现
"""
import asyncio
import logging
from abc import ABC, abstractmethod
from typing import List, Callable, Optional, Any
from dataclasses import dataclass, field

from .types import SagaState, StepResult, SagaContext

logger = logging.getLogger(__name__)


@dataclass
class SagaOptions:
    """Saga 配置选项"""
    max_retries: int = 3
    retry_delay_ms: float = 1000.0
    compensation_timeout_seconds: float = 30.0


class SagaStep(ABC):
    """Saga 步骤抽象基类"""

    @property
    @abstractmethod
    def name(self) -> str:
        """步骤名称"""
        pass

    @abstractmethod
    async def execute(self, context: SagaContext) -> Any:
        """执行正向操作"""
        pass

    @abstractmethod
    async def compensate(self, context: SagaContext) -> None:
        """执行补偿操作"""
        pass

    def is_retryable(self, error: Exception) -> bool:
        """判断错误是否可重试"""
        error_msg = str(error).lower()
        retryable_keywords = ['timeout', 'connection', 'network', 'temporarily']
        return any(kw in error_msg for kw in retryable_keywords)

    @property
    def max_retries(self) -> int:
        """最大重试次数"""
        return 3

    @property
    def retry_delay_ms(self) -> float:
        """重试延迟（毫秒）"""
        return 1000.0


class Saga:
    """Saga 编排器"""

    def __init__(
        self,
        saga_id: str,
        name: str,
        options: Optional[SagaOptions] = None
    ):
        self.id = saga_id
        self.name = name
        self.options = options or SagaOptions()
        self._steps: List[SagaStep] = []
        self._state = SagaState.PENDING
        self._context = SagaContext(saga_id=saga_id)

        # 回调函数
        self._on_step_start: Optional[Callable[[SagaStep], None]] = None
        self._on_step_end: Optional[Callable[[SagaStep, StepResult], None]] = None
        self._on_saga_end: Optional[Callable[[SagaState, Optional[Exception]], None]] = None

    def add_step(self, step: SagaStep) -> 'Saga':
        """添加步骤"""
        self._steps.append(step)
        return self

    def on_step_start(self, callback: Callable[[SagaStep], None]) -> 'Saga':
        """设置步骤开始回调"""
        self._on_step_start = callback
        return self

    def on_step_end(self, callback: Callable[[SagaStep, StepResult], None]) -> 'Saga':
        """设置步骤结束回调"""
        self._on_step_end = callback
        return self

    def on_saga_end(self, callback: Callable[[SagaState, Optional[Exception]], None]) -> 'Saga':
        """设置 Saga 结束回调"""
        self._on_saga_end = callback
        return self

    @property
    def state(self) -> SagaState:
        """获取当前状态"""
        return self._state

    @property
    def context(self) -> SagaContext:
        """获取上下文"""
        return self._context

    async def execute(self) -> None:
        """执行 Saga"""
        if self._state != SagaState.PENDING:
            raise RuntimeError(f"Saga is not in PENDING state: {self._state}")

        self._state = SagaState.RUNNING
        logger.info(f"[Saga {self.id}] Starting: {self.name}")

        executed_steps: List[SagaStep] = []

        try:
            for step in self._steps:
                await self._execute_step(step, executed_steps)

            self._state = SagaState.COMPLETED
            logger.info(f"[Saga {self.id}] Completed successfully")
            self._emit_saga_end(SagaState.COMPLETED, None)

        except Exception as error:
            logger.error(f"[Saga {self.id}] Failed: {error}")
            await self._compensate(executed_steps, error)
            raise

    async def _execute_step(self, step: SagaStep, executed_steps: List[SagaStep]) -> None:
        """执行单个步骤（带重试）"""
        self._emit_step_start(step)

        max_retries = step.max_retries
        retry_delay_ms = step.retry_delay_ms
        last_error: Optional[Exception] = None

        for attempt in range(max_retries + 1):
            try:
                data = await step.execute(self._context)

                result = StepResult(
                    step_name=step.name,
                    success=True,
                    data=data
                )

                self._context.set_result(step.name, result)
                executed_steps.append(step)

                self._emit_step_end(step, result)
                logger.debug(f"[Saga {self.id}] Step '{step.name}' completed")
                return

            except Exception as error:
                last_error = error

                if attempt < max_retries and step.is_retryable(error):
                    logger.warning(
                        f"[Saga {self.id}] Step '{step.name}' failed, "
                        f"retrying ({attempt + 1}/{max_retries})"
                    )
                    await asyncio.sleep(retry_delay_ms / 1000 * (attempt + 1))
                else:
                    break

        # 所有重试失败
        result = StepResult(
            step_name=step.name,
            success=False,
            error=last_error
        )
        self._context.set_result(step.name, result)
        self._emit_step_end(step, result)

        raise last_error

    async def _compensate(self, executed_steps: List[SagaStep], error: Exception) -> None:
        """执行补偿"""
        self._state = SagaState.COMPENSATING
        logger.info(f"[Saga {self.id}] Starting compensation for {len(executed_steps)} steps")

        compensation_errors: List[Exception] = []

        # 反向执行补偿
        for step in reversed(executed_steps):
            try:
                await asyncio.wait_for(
                    step.compensate(self._context),
                    timeout=self.options.compensation_timeout_seconds
                )
                logger.info(f"[Saga {self.id}] Compensated step: {step.name}")
            except Exception as comp_error:
                logger.error(
                    f"[Saga {self.id}] Compensation failed for step '{step.name}': {comp_error}"
                )
                compensation_errors.append(comp_error)

        if not compensation_errors:
            self._state = SagaState.COMPENSATED
            logger.info(f"[Saga {self.id}] Compensated successfully")
        else:
            self._state = SagaState.FAILED
            logger.error(
                f"[Saga {self.id}] Compensation had {len(compensation_errors)} failures"
            )

        self._emit_saga_end(self._state, error)

    def _emit_step_start(self, step: SagaStep) -> None:
        """触发步骤开始事件"""
        if self._on_step_start:
            try:
                self._on_step_start(step)
            except Exception as e:
                logger.warning(f"Step start callback failed: {e}")

    def _emit_step_end(self, step: SagaStep, result: StepResult) -> None:
        """触发步骤结束事件"""
        if self._on_step_end:
            try:
                self._on_step_end(step, result)
            except Exception as e:
                logger.warning(f"Step end callback failed: {e}")

    def _emit_saga_end(self, state: SagaState, error: Optional[Exception]) -> None:
        """触发 Saga 结束事件"""
        if self._on_saga_end:
            try:
                self._on_saga_end(state, error)
            except Exception as e:
                logger.warning(f"Saga end callback failed: {e}")
```

```python
# examples/order_example.py
"""
订单处理 Saga 示例
"""
import asyncio
import aiohttp
from typing import Any

from saga.orchestration import Saga, SagaStep, SagaOptions
from saga.types import SagaContext


class CreateOrderStep(SagaStep):
    """创建订单步骤"""

    def __init__(self, order_service_url: str):
        self.order_service_url = order_service_url

    @property
    def name(self) -> str:
        return "CreateOrder"

    async def execute(self, context: SagaContext) -> str:
        """创建订单"""
        order_data = context.get("order_data")

        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{self.order_service_url}/orders",
                json=order_data,
                headers={"X-Saga-ID": context.saga_id}
            ) as response:
                response.raise_for_status()
                result = await response.json()
                return result["order_id"]

    async def compensate(self, context: SagaContext) -> None:
        """取消订单"""
        result = context.get_result("CreateOrder")
        if not result or not result.success:
            return

        order_id = result.data
        async with aiohttp.ClientSession() as session:
            await session.delete(f"{self.order_service_url}/orders/{order_id}")


class ReserveInventoryStep(SagaStep):
    """预留库存步骤"""

    def __init__(self, inventory_service_url: str):
        self.inventory_service_url = inventory_service_url

    @property
    def name(self) -> str:
        return "ReserveInventory"

    async def execute(self, context: SagaContext) -> str:
        """预留库存"""
        order_result = context.get_result("CreateOrder")
        order_id = order_result.data if order_result else None
        items = context.get("items")

        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{self.inventory_service_url}/reservations",
                json={"order_id": order_id, "items": items}
            ) as response:
                response.raise_for_status()
                result = await response.json()
                return result["reservation_id"]

    async def compensate(self, context: SagaContext) -> None:
        """释放库存"""
        result = context.get_result("ReserveInventory")
        if not result or not result.success:
            return

        reservation_id = result.data
        async with aiohttp.ClientSession() as session:
            await session.delete(
                f"{self.inventory_service_url}/reservations/{reservation_id}"
            )


class ProcessPaymentStep(SagaStep):
    """处理支付步骤"""

    def __init__(self, payment_service_url: str):
        self.payment_service_url = payment_service_url

    @property
    def name(self) -> str:
        return "ProcessPayment"

    async def execute(self, context: SagaContext) -> str:
        """处理支付"""
        order_result = context.get_result("CreateOrder")
        order_id = order_result.data if order_result else None
        amount = context.get("total_amount")

        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{self.payment_service_url}/payments",
                json={
                    "order_id": order_id,
                    "amount": amount,
                    "currency": "USD"
                }
            ) as response:
                response.raise_for_status()
                result = await response.json()
                return result["payment_id"]

    async def compensate(self, context: SagaContext) -> None:
        """退款"""
        result = context.get_result("ProcessPayment")
        if not result or not result.success:
            return

        payment_id = result.data
        async with aiohttp.ClientSession() as session:
            await session.post(
                f"{self.payment_service_url}/payments/{payment_id}/refund"
            )


async def main():
    """主函数"""
    # 创建 Saga
    saga = Saga(
        saga_id="order-123",
        name="OrderProcessingSaga",
        options=SagaOptions(max_retries=2, retry_delay_ms=500)
    )

    # 设置回调
    saga.on_step_start(lambda step: print(f"▶ Starting step: {step.name}"))
    saga.on_step_end(
        lambda step, result: print(
            f"{'✓' if result.success else '✗'} Completed step: {step.name}"
        )
    )
    saga.on_saga_end(
        lambda state, error: print(
            f"{'⚠' if error else '✓'} Saga ended: {state.value}"
            f"{f', error: {error}' if error else ''}"
        )
    )

    # 添加步骤
    saga.add_step(CreateOrderStep("http://order-service:8080"))
    saga.add_step(ReserveInventoryStep("http://inventory-service:8080"))
    saga.add_step(ProcessPaymentStep("http://payment-service:8080"))

    # 准备上下文数据
    saga.context.set("order_data", {
        "customer_id": "cust-456",
        "email": "customer@example.com"
    })
    saga.context.set("items", [
        {"product_id": "prod-1", "quantity": 2, "price": 100.0},
        {"product_id": "prod-2", "quantity": 1, "price": 50.0}
    ])
    saga.context.set("total_amount", 250.0)

    try:
        await saga.execute()
        print(f"\nFinal state: {saga.state.value}")
        print("Results:")
        for step_name, result in saga.context.results.items():
            print(f"  {step_name}: success={result.success}")
    except Exception as e:
        print(f"\nSaga failed: {e}")
        print(f"Final state: {saga.state.value}")


if __name__ == "__main__":
    asyncio.run(main())
```

### 2. 编舞式 Saga 实现

```python
# saga/choreography.py
"""
编舞式 Saga 实现
"""
import asyncio
import uuid
from abc import ABC, abstractmethod
from typing import Dict, List, Callable, Any, Optional
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum

from .types import SagaState


class EventType(Enum):
    """事件类型"""
    ORDER_CREATED = "order.created"
    ORDER_CANCELLED = "order.cancelled"
    INVENTORY_RESERVED = "inventory.reserved"
    INVENTORY_RELEASED = "inventory.released"
    PAYMENT_PROCESSED = "payment.processed"
    PAYMENT_REFUNDED = "payment.refunded"
    SAGA_COMPLETED = "saga.completed"
    SAGA_FAILED = "saga.failed"


@dataclass
class SagaEvent:
    """Saga 事件"""
    event_type: EventType
    saga_id: str
    payload: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, str] = field(default_factory=dict)
    timestamp: datetime = field(default_factory=datetime.now)
    event_id: str = field(default_factory=lambda: str(uuid.uuid4()))


EventHandler = Callable[[SagaEvent], asyncio.Coroutine[Any, Any, None]]


class EventBus(ABC):
    """事件总线抽象基类"""

    @abstractmethod
    async def publish(self, event: SagaEvent) -> None:
        """发布事件"""
        pass

    @abstractmethod
    def subscribe(self, event_type: EventType, handler: EventHandler) -> None:
        """订阅事件"""
        pass


class InMemoryEventBus(EventBus):
    """内存事件总线实现"""

    def __init__(self):
        self._subscribers: Dict[EventType, List[EventHandler]] = {}

    async def publish(self, event: SagaEvent) -> None:
        """发布事件"""
        print(f"📤 Publishing event: {event.event_type.value} (saga: {event.saga_id})")

        handlers = self._subscribers.get(event.event_type, [])
        if handlers:
            await asyncio.gather(
                *[self._safe_handle(handler, event) for handler in handlers],
                return_exceptions=True
            )

    async def _safe_handle(self, handler: EventHandler, event: SagaEvent) -> None:
        """安全处理事件"""
        try:
            await handler(event)
        except Exception as e:
            print(f"Error handling event {event.event_type.value}: {e}")

    def subscribe(self, event_type: EventType, handler: EventHandler) -> None:
        """订阅事件"""
        if event_type not in self._subscribers:
            self._subscribers[event_type] = []
        self._subscribers[event_type].append(handler)
        print(f"📥 Subscribed handler for: {event_type.value}")


class ServiceHandler(ABC):
    """服务处理器基类"""

    def __init__(self, event_bus: EventBus):
        self.event_bus = event_bus

    async def _publish(self, event: SagaEvent) -> None:
        """发布事件"""
        await self.event_bus.publish(event)


class OrderServiceHandler(ServiceHandler):
    """订单服务处理器"""

    def __init__(self, event_bus: EventBus):
        super().__init__(event_bus)
        event_bus.subscribe(EventType.ORDER_CREATED, self.handle_create_order)

    async def handle_create_order(self, event: SagaEvent) -> None:
        """处理创建订单请求"""
        customer_id = event.payload.get("customer_id")
        print(f"[OrderService] Creating order for customer: {customer_id}")

        # 创建订单
        order_id = f"ORD-{uuid.uuid4().hex[:8]}"

        # 发布订单创建成功事件
        await self._publish(SagaEvent(
            event_type=EventType.ORDER_CREATED,
            saga_id=event.saga_id,
            payload={"order_id": order_id}
        ))


class ChoreographySaga:
    """编舞式 Saga 协调器"""

    def __init__(
        self,
        saga_id: str,
        event_bus: EventBus,
        on_complete: Optional[Callable[["ChoreographySaga"], None]] = None,
        on_fail: Optional[Callable[["ChoreographySaga", str], None]] = None
    ):
        self.id = saga_id
        self.event_bus = event_bus
        self.state = SagaState.PENDING
        self.start_time = datetime.now()
        self.end_time: Optional[datetime] = None
        self.on_complete = on_complete
        self.on_fail = on_fail

        self._register_handlers()

    def _register_handlers(self) -> None:
        """注册事件处理器"""
        self.event_bus.subscribe(EventType.SAGA_COMPLETED, self._on_completed)
        self.event_bus.subscribe(EventType.SAGA_FAILED, self._on_failed)

    async def start(self, initiator_event: SagaEvent) -> None:
        """启动 Saga"""
        self.state = SagaState.RUNNING
        await self.event_bus.publish(initiator_event)

    async def _on_completed(self, event: SagaEvent) -> None:
        """处理完成事件"""
        if event.saga_id == self.id:
            self.state = SagaState.COMPLETED
            self.end_time = datetime.now()
            if self.on_complete:
                self.on_complete(self)

    async def _on_failed(self, event: SagaEvent) -> None:
        """处理失败事件"""
        if event.saga_id == self.id:
            self.state = SagaState.FAILED
            self.end_time = datetime.now()
            reason = event.payload.get("reason", "Unknown")
            if self.on_fail:
                self.on_fail(self, reason)

    def get_duration_seconds(self) -> float:
        """获取执行时长（秒）"""
        end = self.end_time or datetime.now()
        return (end - self.start_time).total_seconds()
```

### 运行说明

```bash
# 1. 创建虚拟环境
python -m venv venv
source venv/bin/activate  # Windows: venv\Scripts\activate

# 2. 安装依赖
pip install aiohttp pytest pytest-asyncio

# 3. 运行示例
python examples/order_example.py

# 4. 运行测试
pytest tests/ -v
```

---

## 对比总结

### 四种语言实现对比

| 特性 | Go | Java | TypeScript | Python |
|------|-----|------|------------|--------|
| **并发模型** | Goroutines | CompletableFuture | Promise/async-await | asyncio |
| **类型系统** | 静态/强类型 | 静态/强类型 | 静态/强类型 | 动态类型 |
| **错误处理** | error 返回值 | 异常 | try-catch | try-except |
| **语法简洁度** | 中等 | 较冗长 | 简洁 | 最简洁 |
| **生态成熟度** | 中等 | 成熟 | 成熟 | 成熟 |
| **适用场景** | 云原生/微服务 | 企业级应用 | Web/Node.js | 数据/AI 集成 |

### 模式选择建议

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Saga 模式选择决策树                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. 流程复杂度                                                                │
│     ├─ 简单线性流程 (3-5 个步骤) → 两种模式都适用                              │
│     └─ 复杂条件分支/动态流程 → 编排式更适合                                    │
│                                                                             │
│  2. 团队组织                                                                  │
│     ├─ 中心化团队，统一管理 → 编排式                                          │
│     └─ 跨团队自治，服务独立 → 编舞式                                          │
│                                                                             │
│  3. 可观测性需求                                                               │
│     ├─ 需要全局流程视图 → 编排式                                              │
│     └─ 关注单个服务行为 → 编舞式                                              │
│                                                                             │
│  4. 技术栈                                                                    │
│     ├─ 已有消息中间件 (Kafka/RabbitMQ) → 编舞式更易集成                        │
│     └─ 使用工作流框架 (Temporal/Camunda) → 编排式更自然                        │
│                                                                             │
│  5. 补偿复杂度                                                                │
│     ├─ 补偿逻辑复杂，需要协调 → 编排式                                        │
│     └─ 各服务补偿独立简单 → 编舞式                                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 通用最佳实践

1. **幂等性设计**
   - 所有步骤操作必须幂等
   - 使用唯一请求 ID 防止重复处理
   - 补偿操作也要幂等

2. **超时与重试**
   - 为每个步骤设置合理的超时时间
   - 区分可重试错误和不可重试错误
   - 使用指数退避避免惊群效应

3. **监控与告警**
   - 记录详细的执行日志
   - 监控补偿失败（需要人工介入）
   - 设置 Saga 执行时长告警

4. **测试策略**
   - 单元测试每个步骤的正向和补偿逻辑
   - 集成测试完整的 Saga 流程
   - 混沌测试模拟各种故障场景

5. **数据一致性**
   - 理解最终一致性的限制
   - 设计业务上可接受的暂时不一致状态
   - 考虑使用事务性发件箱模式
