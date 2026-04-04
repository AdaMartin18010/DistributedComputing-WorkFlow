# Saga模式详解

## 概述

Saga模式是一种用于处理分布式长事务的设计模式，由Hector Garcia-Molina和Kenneth Salem在1987年的一篇论文中首次提出。与2PC、3PC等强一致性协议不同，Saga采用最终一致性（Eventually Consistency）的柔性事务策略，通过将长事务拆分为多个本地事务，并为每个本地事务提供补偿操作（Compensating Transaction）来实现事务的完整性和一致性。

Saga模式在现代微服务架构中得到了广泛应用，特别适合处理跨多个服务的长时间运行业务流程。

---

## 一、Saga模式的核心概念

### 1.1 基本定义

**Saga** 是一系列本地事务的集合，每个本地事务：

- 更新数据库并发布消息或事件
- 触发下一个本地事务
- 如果某个本地事务失败，则执行一系列补偿事务来回滚之前完成的操作

```
┌─────────────────────────────────────────────────────────────┐
│                    Saga模式结构                              │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   订单Saga示例：                                              │
│                                                             │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐ │
│   │ 创建订单 │───→│ 扣减库存 │───→│ 扣减余额 │───→│ 发送通知 │ │
│   │   T1    │    │   T2    │    │   T3    │    │   T4    │ │
│   └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘ │
│        │              │              │              │       │
│        │              │              │              │       │
│   ┌────▼────┐    ┌────▼────┐    ┌────▼────┐    ┌────▼────┐ │
│   │  C1     │    │  C2     │    │  C3     │    │  C4     │ │
│   │取消订单 │    │恢复库存 │    │恢复余额 │    │取消通知 │ │
│   │(补偿)   │    │(补偿)   │    │(补偿)   │    │(补偿)   │ │
│   └─────────┘    └─────────┘    └─────────┘    └─────────┘ │
│                                                             │
│   执行顺序：T1 → T2 → T3 → T4                               │
│   回滚顺序（T3失败）：C2 → C1                                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 两种实现方式

```
┌─────────────────────────────────────────────────────────────┐
│                Saga的两种实现方式                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   方式1：编排式Saga（Choreography-based）                     │
│   ─────────────────────────────────────                     │
│                                                             │
│   ┌─────────┐      事件       ┌─────────┐     事件       ┌─────────┐│
│   │ 服务A   │ ───────────────→│ 服务B   │───────────────→│ 服务C   ││
│   │ (订单)  │  "订单已创建"    │ (库存)  │  "库存已扣减"   │ (支付)  ││
│   └─────────┘                 └─────────┘                └─────────┘│
│        │                            │                         │     │
│        │                            │                         │     │
│        │       去中心化协调          │                         │     │
│        │       事件驱动              │                         │     │
│        │                            │                         │     │
│                                                             │
│   特点：                                                     │
│   - 无中心协调器                                              │
│   - 服务间通过事件总线通信                                      │
│   - 松耦合，易于扩展                                          │
│   - 事务流程分散在各服务中                                      │
│                                                             │
│   ───────────────────────────────────────────────────────── │
│                                                             │
│   方式2：编排式Saga（Orchestration-based）                    │
│   ─────────────────────────────────────                     │
│                                                             │
│                          ┌───────────┐                      │
│                          │ Saga协调器 │                      │
│                          │(Orchestrator)                    │
│                          └─────┬─────┘                      │
│                                │                            │
│           ┌────────────────────┼────────────────────┐       │
│           │                    │                    │       │
│           ▼                    ▼                    ▼       │
│      ┌─────────┐         ┌─────────┐         ┌─────────┐   │
│      │ 服务A   │         │ 服务B   │         │ 服务C   │   │
│      │ (订单)  │         │ (库存)  │         │ (支付)  │   │
│      └─────────┘         └─────────┘         └─────────┘   │
│                                                             │
│   特点：                                                     │
│   - 有中心协调器（Saga Orchestrator）                          │
│   - 协调器负责调用各服务                                       │
│   - 事务流程集中在协调器                                       │
│   - 易于理解和维护                                            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 二、编排式Saga（Choreography）

### 2.1 工作原理

```
┌─────────────────────────────────────────────────────────────┐
│              编排式Saga执行流程                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   第1步：创建订单                                            │
│   ┌─────────┐                                               │
│   │ 订单服务 │──→ 创建订单成功                                │
│   └────┬────┘                                               │
│        │                                                    │
│        │ 发布事件: OrderCreatedEvent                         │
│        ▼                                                    │
│   ┌─────────────────────────────────────┐                  │
│   │          消息队列/事件总线            │                  │
│   │     topic: order-events             │                  │
│   └─────────────────────────────────────┘                  │
│                                                             │
│   第2步：扣减库存                                            │
│                            ┌─────────┐                     │
│   OrderCreatedEvent ──────→│ 库存服务 │                     │
│                            │         │──→ 扣减库存成功      │
│                            └────┬────┘                     │
│                                 │                           │
│                                 │ 发布事件: StockDeductedEvent│
│                                 ▼                           │
│   ┌─────────────────────────────────────┐                  │
│   │          消息队列/事件总线            │                  │
│   │     topic: inventory-events         │                  │
│   └─────────────────────────────────────┘                  │
│                                                             │
│   第3步：处理支付                                            │
│                                                      ┌─────────┐│
│   StockDeductedEvent ───────────────────────────────→│ 支付服务 ││
│                                                      │         ││
│                                                      │──→ 扣款  ││
│                                                      └────┬────┘│
│                                                           │     │
│                                                           │     │
│   失败处理：                                                │     │
│   ┌───────────────────────────────────────────────────────┘     │
│   │                                                             │
│   ▼                                                             │
│   PaymentFailedEvent 发布                                        │
│   ┌─────────────────────────────────────┐                      │
│   │          消息队列/事件总线            │                      │
│   │     topic: payment-events           │                      │
│   └─────────────────────────────────────┘                      │
│        │                    │                                  │
│        │                    │                                  │
│        ▼                    ▼                                  │
│   ┌─────────┐         ┌─────────┐                             │
│   │ 库存服务 │         │ 订单服务 │                             │
│   │ 恢复库存 │         │ 取消订单 │                             │
│   │ (补偿)   │         │ (补偿)   │                             │
│   └─────────┘         └─────────┘                             │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Java实现示例

```java
/**
 * 编排式Saga - 订单服务
 */
@Service
public class OrderService {

    @Autowired
    private OrderRepository orderRepository;

    @Autowired
    private EventPublisher eventPublisher;

    /**
     * 创建订单（Saga的第一个步骤）
     */
    @Transactional
    public Order createOrder(CreateOrderRequest request) {
        // 1. 创建订单
        Order order = new Order();
        order.setId(UUID.randomUUID().toString());
        order.setUserId(request.getUserId());
        order.setProductId(request.getProductId());
        order.setQuantity(request.getQuantity());
        order.setAmount(request.getAmount());
        order.setStatus(OrderStatus.CREATED);
        order.setCreateTime(LocalDateTime.now());

        orderRepository.save(order);

        // 2. 发布订单创建事件，触发下一个Saga步骤
        OrderCreatedEvent event = OrderCreatedEvent.builder()
            .orderId(order.getId())
            .userId(order.getUserId())
            .productId(order.getProductId())
            .quantity(order.getQuantity())
            .amount(order.getAmount())
            .timestamp(System.currentTimeMillis())
            .build();

        eventPublisher.publish("order-events", event);

        return order;
    }

    /**
     * 补偿操作：取消订单
     */
    @Transactional
    public void cancelOrder(String orderId, String reason) {
        Order order = orderRepository.findById(orderId)
            .orElseThrow(() -> new OrderNotFoundException(orderId));

        // 幂等性检查：只有已创建状态的订单可以取消
        if (order.getStatus() == OrderStatus.CANCELLED) {
            return;  // 已经取消，直接返回
        }

        order.setStatus(OrderStatus.CANCELLED);
        order.setCancelReason(reason);
        order.setCancelTime(LocalDateTime.now());

        orderRepository.save(order);

        log.info("订单已取消: {}, 原因: {}", orderId, reason);
    }

    /**
     * 监听支付失败事件，执行补偿
     */
    @KafkaListener(topics = "payment-events", groupId = "order-service")
    public void handlePaymentFailedEvent(PaymentFailedEvent event) {
        if (event.getOrderId() != null) {
            cancelOrder(event.getOrderId(), "支付失败: " + event.getErrorMessage());
        }
    }
}

/**
 * 编排式Saga - 库存服务
 */
@Service
public class InventoryService {

    @Autowired
    private InventoryRepository inventoryRepository;

    @Autowired
    private EventPublisher eventPublisher;

    /**
     * 监听订单创建事件，扣减库存
     */
    @KafkaListener(topics = "order-events", groupId = "inventory-service")
    @Transactional
    public void handleOrderCreatedEvent(OrderCreatedEvent event) {
        // 幂等性检查
        if (inventoryRepository.existsDeductionRecord(event.getOrderId())) {
            log.info("库存已扣减，跳过: {}", event.getOrderId());
            return;
        }

        try {
            // 1. 扣减库存
            Inventory inventory = inventoryRepository
                .findByProductIdForUpdate(event.getProductId());

            if (inventory.getStock() < event.getQuantity()) {
                throw new InsufficientStockException("库存不足");
            }

            inventory.setStock(inventory.getStock() - event.getQuantity());
            inventory.setReservedStock(inventory.getReservedStock() + event.getQuantity());
            inventoryRepository.save(inventory);

            // 2. 记录扣减日志（用于幂等性和补偿）
            StockDeductionRecord record = new StockDeductionRecord();
            record.setOrderId(event.getOrderId());
            record.setProductId(event.getProductId());
            record.setQuantity(event.getQuantity());
            record.setStatus(StockStatus.DEDUCTED);
            inventoryRepository.saveDeductionRecord(record);

            // 3. 发布库存扣减成功事件
            StockDeductedEvent successEvent = StockDeductedEvent.builder()
                .orderId(event.getOrderId())
                .productId(event.getProductId())
                .quantity(event.getQuantity())
                .timestamp(System.currentTimeMillis())
                .build();

            eventPublisher.publish("inventory-events", successEvent);

        } catch (Exception e) {
            // 发布库存扣减失败事件
            StockDeductionFailedEvent failedEvent = StockDeductionFailedEvent.builder()
                .orderId(event.getOrderId())
                .productId(event.getProductId())
                .errorMessage(e.getMessage())
                .build();

            eventPublisher.publish("inventory-events", failedEvent);
            throw e;
        }
    }

    /**
     * 补偿操作：恢复库存
     */
    @KafkaListener(topics = "payment-events", groupId = "inventory-service")
    @Transactional
    public void handlePaymentFailedForCompensation(PaymentFailedEvent event) {
        String orderId = event.getOrderId();

        // 查找扣减记录
        StockDeductionRecord record = inventoryRepository
            .findDeductionRecord(orderId);

        if (record == null || record.getStatus() == StockStatus.RELEASED) {
            return;  // 未扣减或已恢复
        }

        // 恢复库存
        Inventory inventory = inventoryRepository
            .findByProductId(record.getProductId());

        inventory.setStock(inventory.getStock() + record.getQuantity());
        inventory.setReservedStock(inventory.getReservedStock() - record.getQuantity());
        inventoryRepository.save(inventory);

        // 更新记录状态
        record.setStatus(StockStatus.RELEASED);
        record.setReleaseTime(LocalDateTime.now());
        inventoryRepository.saveDeductionRecord(record);

        log.info("库存已恢复: orderId={}, productId={}, quantity={}",
            orderId, record.getProductId(), record.getQuantity());
    }
}

/**
 * 编排式Saga - 支付服务
 */
@Service
public class PaymentService {

    @Autowired
    private PaymentRepository paymentRepository;

    @Autowired
    private EventPublisher eventPublisher;

    /**
     * 监听库存扣减事件，执行支付
     */
    @KafkaListener(topics = "inventory-events", groupId = "payment-service")
    @Transactional
    public void handleStockDeductedEvent(StockDeductedEvent event) {
        // 幂等性检查
        if (paymentRepository.existsByOrderId(event.getOrderId())) {
            return;
        }

        try {
            // 1. 执行支付
            Payment payment = new Payment();
            payment.setId(UUID.randomUUID().toString());
            payment.setOrderId(event.getOrderId());
            payment.setAmount(event.getAmount());
            payment.setStatus(PaymentStatus.PROCESSING);

            // 调用第三方支付接口
            PaymentResult result = callPaymentGateway(payment);

            if (result.isSuccess()) {
                payment.setStatus(PaymentStatus.SUCCESS);
                payment.setTransactionId(result.getTransactionId());
                paymentRepository.save(payment);

                // 2. 发布支付成功事件
                PaymentSuccessEvent successEvent = PaymentSuccessEvent.builder()
                    .orderId(event.getOrderId())
                    .paymentId(payment.getId())
                    .transactionId(result.getTransactionId())
                    .build();

                eventPublisher.publish("payment-events", successEvent);

            } else {
                throw new PaymentException("支付失败: " + result.getErrorMessage());
            }

        } catch (Exception e) {
            // 发布支付失败事件，触发补偿
            PaymentFailedEvent failedEvent = PaymentFailedEvent.builder()
                .orderId(event.getOrderId())
                .errorMessage(e.getMessage())
                .build();

            eventPublisher.publish("payment-events", failedEvent);
            throw e;
        }
    }

    /**
     * 补偿操作：退款
     */
    @KafkaListener(topics = "order-events", groupId = "payment-service")
    @Transactional
    public void handleOrderCancelledForRefund(OrderCancelledEvent event) {
        Payment payment = paymentRepository.findByOrderId(event.getOrderId());

        if (payment == null || payment.getStatus() != PaymentStatus.SUCCESS) {
            return;  // 未支付成功，无需退款
        }

        // 执行退款
        RefundResult result = callRefundGateway(payment);

        if (result.isSuccess()) {
            payment.setStatus(PaymentStatus.REFUNDED);
            payment.setRefundId(result.getRefundId());
            payment.setRefundTime(LocalDateTime.now());
            paymentRepository.save(payment);

            log.info("退款成功: orderId={}, refundId={}",
                event.getOrderId(), result.getRefundId());
        }
    }
}
```

---

## 三、编排式Saga（Orchestration）

### 3.1 工作原理

```
┌─────────────────────────────────────────────────────────────┐
│              编排式Saga执行流程                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│                    ┌─────────────────┐                      │
│                    │  Saga协调器      │                      │
│                    │  (Orchestrator) │                      │
│                    └────────┬────────┘                      │
│                             │                               │
│   1. 开始Saga               │                               │
│      调用创建订单            │                               │
│      ┌─────────────────────→│                               │
│                             │                               │
│   2. 订单创建成功            │                               │
│      ←─────────────────────┤                               │
│                             │                               │
│   3. 调用扣减库存            │                               │
│      ┌─────────────────────→│                               │
│                             │                               │
│   4. 库存扣减成功            │                               │
│      ←─────────────────────┤                               │
│                             │                               │
│   5. 调用支付               │                               │
│      ┌─────────────────────→│                               │
│                             │                               │
│   6. 支付失败！              │                               │
│      ←─────────────────────┤                               │
│                             │                               │
│   7. 执行补偿流程            │                               │
│      ┌─────────────────────→│                               │
│      调用库存恢复            │                               │
│                             │                               │
│      ←─────────────────────┤                               │
│                             │                               │
│      调用订单取消            │                               │
│      ┌─────────────────────→│                               │
│                             │                               │
│      ←─────────────────────┤                               │
│                             │                               │
│   8. Saga结束               │                               │
│                             ▼                               │
│                                                             │
│   状态机定义：                                               │
│   CREATED → DEDUCTING_STOCK → PAYING → COMPLETED            │
│                  ↓               ↓                          │
│                  └─────────→ COMPENSATING → CANCELLED       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 Java实现示例

```java
/**
 * Saga定义
 */
public class OrderSaga implements SagaOrchestrator {

    @Autowired
    private SagaStepExecutor stepExecutor;

    @Autowired
    private SagaStateRepository stateRepository;

    /**
     * 定义Saga执行步骤
     */
    @Override
    public SagaDefinition defineSaga() {
        return SagaBuilder.create("order-saga")
            // 第1步：创建订单
            .step("create-order")
                .invoke(this::createOrder)
                .compensateWith(this::cancelOrder)
            .step("deduct-inventory")
                .invoke(this::deductInventory)
                .compensateWith(this::restoreInventory)
            .step("process-payment")
                .invoke(this::processPayment)
                .compensateWith(this::refundPayment)
            .step("send-notification")
                .invoke(this::sendNotification)
            .build();
    }

    /**
     * 执行Saga
     */
    public SagaResult execute(CreateOrderRequest request) {
        SagaInstance instance = SagaInstance.builder()
            .id(UUID.randomUUID().toString())
            .sagaType("order-saga")
            .status(SagaStatus.STARTED)
            .payload(request)
            .build();

        stateRepository.save(instance);

        try {
            // 顺序执行每个步骤
            executeStep(instance, "create-order", request);
            executeStep(instance, "deduct-inventory", request);
            executeStep(instance, "process-payment", request);
            executeStep(instance, "send-notification", request);

            instance.setStatus(SagaStatus.COMPLETED);
            stateRepository.save(instance);

            return SagaResult.success(instance.getId());

        } catch (Exception e) {
            // 执行补偿
            compensate(instance);

            instance.setStatus(SagaStatus.COMPENSATED);
            stateRepository.save(instance);

            return SagaResult.failure(instance.getId(), e.getMessage());
        }
    }

    private void executeStep(SagaInstance instance, String stepName, Object payload) {
        // 记录当前步骤
        instance.setCurrentStep(stepName);
        stateRepository.save(instance);

        // 执行步骤
        StepResult result = stepExecutor.execute(stepName, payload);

        if (!result.isSuccess()) {
            throw new SagaExecutionException("Step failed: " + stepName);
        }

        // 记录已完成的步骤
        instance.addCompletedStep(stepName);
        stateRepository.save(instance);
    }

    /**
     * 执行补偿
     */
    private void compensate(SagaInstance instance) {
        List<String> completedSteps = instance.getCompletedSteps();

        // 反向执行补偿操作
        for (int i = completedSteps.size() - 1; i >= 0; i--) {
            String stepName = completedSteps.get(i);
            stepExecutor.compensate(stepName, instance.getPayload());
        }
    }

    // ========== 具体步骤实现 ==========

    private StepResult createOrder(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        // 调用订单服务
        Order order = orderServiceClient.createOrder(request);
        return StepResult.success(order.getId());
    }

    private StepResult cancelOrder(Object payload) {
        String orderId = (String) payload;
        orderServiceClient.cancelOrder(orderId);
        return StepResult.success();
    }

    private StepResult deductInventory(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        inventoryServiceClient.deductStock(request.getProductId(), request.getQuantity());
        return StepResult.success();
    }

    private StepResult restoreInventory(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        inventoryServiceClient.restoreStock(request.getProductId(), request.getQuantity());
        return StepResult.success();
    }

    private StepResult processPayment(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        PaymentResult result = paymentServiceClient.charge(request.getUserId(), request.getAmount());
        return result.isSuccess() ? StepResult.success() : StepResult.failure(result.getError());
    }

    private StepResult refundPayment(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        paymentServiceClient.refund(request.getOrderId());
        return StepResult.success();
    }

    private StepResult sendNotification(Object payload) {
        CreateOrderRequest request = (CreateOrderRequest) payload;
        notificationServiceClient.sendOrderConfirmation(request.getUserId(), request.getOrderId());
        return StepResult.success();
    }
}

/**
 * Saga状态机
 */
@Component
public class SagaStateMachine {

    private final StateMachine<SagaStatus, SagaEvent> stateMachine;

    public SagaStateMachine() {
        this.stateMachine = StateMachineBuilder
            .newBuilder(SagaStatus.class, SagaEvent.class)
            .initialState(SagaStatus.STARTED)

            .transition(SagaStatus.STARTED, SagaEvent.STEP_SUCCESS, SagaStatus.CREATED)
            .transition(SagaStatus.CREATED, SagaEvent.STEP_SUCCESS, SagaStatus.INVENTORY_DEDUCTED)
            .transition(SagaStatus.INVENTORY_DEDUCTED, SagaEvent.STEP_SUCCESS, SagaStatus.PAID)
            .transition(SagaStatus.PAID, SagaEvent.STEP_SUCCESS, SagaStatus.COMPLETED)

            .transition(SagaStatus.CREATED, SagaEvent.STEP_FAILURE, SagaStatus.COMPENSATING)
            .transition(SagaStatus.INVENTORY_DEDUCTED, SagaEvent.STEP_FAILURE, SagaStatus.COMPENSATING)
            .transition(SagaStatus.PAID, SagaEvent.STEP_FAILURE, SagaStatus.COMPENSATING)

            .transition(SagaStatus.COMPENSATING, SagaEvent.COMPENSATION_COMPLETE, SagaStatus.COMPENSATED)

            .build();
    }

    public SagaStatus transition(SagaStatus currentStatus, SagaEvent event) {
        return stateMachine.fire(currentStatus, event);
    }
}
```

---

## 四、Saga的关键特性

### 4.1 幂等性

```java
/**
 * 幂等性处理示例
 */
@Service
public class IdempotentSagaHandler {

    @Autowired
    private IdempotencyKeyRepository idempotencyRepository;

    /**
     * 幂等性装饰器
     */
    public <T> T executeWithIdempotency(String idempotencyKey,
                                        Supplier<T> execution,
                                        Function<String, T> resultProvider) {
        // 1. 检查是否已经处理过
        Optional<IdempotencyRecord> existing = idempotencyRepository.findByKey(idempotencyKey);

        if (existing.isPresent()) {
            // 已经处理过，返回之前的结果
            log.info("幂等性命中，返回缓存结果: {}", idempotencyKey);
            return resultProvider.apply(existing.get().getResult());
        }

        // 2. 设置处理中状态（防止并发）
        IdempotencyRecord record = new IdempotencyRecord();
        record.setKey(idempotencyKey);
        record.setStatus(IdempotencyStatus.PROCESSING);
        record.setCreateTime(LocalDateTime.now());
        idempotencyRepository.save(record);

        try {
            // 3. 执行业务逻辑
            T result = execution.get();

            // 4. 保存结果
            record.setStatus(IdempotencyStatus.COMPLETED);
            record.setResult(serialize(result));
            record.setCompleteTime(LocalDateTime.now());
            idempotencyRepository.save(record);

            return result;

        } catch (Exception e) {
            // 5. 失败记录
            record.setStatus(IdempotencyStatus.FAILED);
            record.setErrorMessage(e.getMessage());
            idempotencyRepository.save(record);
            throw e;
        }
    }
}
```

### 4.2 可观测性

```java
/**
 * Saga监控和追踪
 */
@Component
public class SagaMonitor {

    @Autowired
    private MeterRegistry meterRegistry;

    @Autowired
    private Tracer tracer;

    /**
     * 记录Saga执行指标
     */
    public void recordSagaMetrics(SagaInstance saga) {
        // 计数器
        meterRegistry.counter("saga.executions",
            "sagaType", saga.getSagaType(),
            "status", saga.getStatus().name()
        ).increment();

        // 执行时间
        if (saga.getCompleteTime() != null) {
            long duration = Duration.between(
                saga.getStartTime(),
                saga.getCompleteTime()
            ).toMillis();

            meterRegistry.timer("saga.duration",
                "sagaType", saga.getSagaType()
            ).record(duration, TimeUnit.MILLISECONDS);
        }

        // 补偿次数
        if (saga.getCompensationCount() > 0) {
            meterRegistry.counter("saga.compensations",
                "sagaType", saga.getSagaType()
            ).increment(saga.getCompensationCount());
        }
    }

    /**
     * 分布式追踪
     */
    public Span startSagaSpan(SagaInstance saga) {
        Span span = tracer.nextSpan()
            .name("saga-execution")
            .tag("saga.id", saga.getId())
            .tag("saga.type", saga.getSagaType())
            .start();

        return span;
    }
}
```

---

## 五、Saga的优缺点

### 5.1 优点

| 优点 | 说明 |
|-----|------|
| **无全局锁** | 每个本地事务独立提交，无长时间资源锁定 |
| **高并发** | 不存在2PC的同步阻塞问题，吞吐量高 |
| **适合长事务** | 可以处理耗时较长的业务流程 |
| **天然适配微服务** | 每个服务管理自己的事务和补偿 |
| **松耦合** | 编排式Saga通过事件通信，服务间解耦 |

### 5.2 缺点

| 缺点 | 说明 |
|-----|------|
| **最终一致性** | 事务执行过程中数据处于不一致状态 |
| **补偿复杂** | 需要为每个操作设计补偿逻辑，业务侵入大 |
| **补偿可能失败** | 补偿操作本身也可能失败，需要重试或人工介入 |
| **隔离性问题** | 外部事务可能看到中间状态（脏读） |

### 5.3 隔离性问题的处理

```
┌─────────────────────────────────────────────────────────────┐
│                 Saga的隔离性问题                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   场景：用户看到不一致的中间状态                              │
│                                                             │
│   T1: 订单已创建（用户看到订单）                              │
│   T2: 库存已扣减（用户看到库存减少）                          │
│   T3: 支付失败 → 开始补偿                                    │
│                                                             │
│   在补偿完成前：                                             │
│   - 用户看到：订单存在，库存减少，但支付失败                   │
│   - 这不是最终状态！                                         │
│                                                             │
│   解决方案：                                                 │
│                                                             │
│   1. 语义锁（Semantic Lock）                                 │
│      ─────────────                                           │
│      在Saga完成前，标记数据为"处理中"，外部查询不可见          │
│                                                             │
│   ┌─────────┐                                               │
│   │ 订单记录 │                                               │
│   │ id: 001 │                                               │
│   │ status: PENDING ← 处理中，对用户不可见                   │
│   │ saga_id: saga_001                                       │
│   └─────────┘                                               │
│                                                             │
│   2. 交换式更新（Commutative Updates）                        │
│      ─────────────────────                                   │
│      使用可交换的操作，避免顺序依赖                            │
│      如：库存扣减使用"增加已售数量"代替"减少库存"              │
│                                                             │
│   3. 悲观视图（Pessimistic View）                             │
│      ─────────────────────                                   │
│      查询时考虑Saga进行中状态，返回"预期"结果                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 六、Saga框架对比

| 框架 | 类型 | 语言 | 特点 |
|-----|------|-----|------|
| **Axon Saga** | 编排式 | Java | 与Axon框架深度集成，Event Sourcing支持 |
| **Seata Saga** | 编排式 | Java | 阿里开源，支持状态机引擎，可视化设计 |
| **Camunda** | 编排式 | Java | BPMN工作流引擎，支持复杂业务流程 |
| **Eventuate** | 编排式 | Java/Go | 微服务事件驱动框架，Tram/Saga支持 |
| **Cadence/Temporal** | 编排式 | 多语言 | Uber开源，持久化工作流，适合长事务 |
| **NServiceBus** | 编排式 | .NET | .NET平台成熟方案， Saga支持完善 |

---

## 七、总结

Saga模式是处理分布式长事务的有效方案，特别适合微服务架构。它通过牺牲强一致性换取高可用性和高性能，在电商、金融等领域有广泛应用。

**关键要点**：

1. 选择编排式还是编舞式取决于系统复杂度和团队偏好
2. 必须实现幂等性保证
3. 补偿逻辑的设计是Saga成功的关键
4. 需要考虑隔离性问题的处理
5. 完善的监控和人工介入机制必不可少

在现代分布式系统中，Saga模式与TCC、2PC等方案互为补充，架构师应根据业务场景选择合适的事务处理策略。

---

## 参考资料

1. Hector Garcia-Molina, Kenneth Salem, "Sagas", ACM SIGMOD, 1987
2. Chris Richardson, "Pattern: Saga", microservices.io
3. "Microservices Patterns" by Chris Richardson, Chapter 4
4. Apache Seata Documentation: Saga Mode


---

## 相关主题

- [两阶段提交2PC](./两阶段提交2PC.md)
- [TCC事务模式](./TCC事务模式.md)
- [分布式事务选型指南](../分布式事务选型指南.md)

## 参考资源

- [Saga模式](https://microservices.io/patterns/data/saga.html)
- [Saga论文](https://www.cs.cornell.edu/andru/cs711/2002fa/reading/sagas.pdf)
