# Core Terms Glossary

This document provides the core terminology used in the project, with Chinese and English translations.

## 📋 Overview

This glossary ensures consistent terminology usage across all documents.

---

## 🔤 Core Terms

### A

#### Activity

**Chinese**: 活动

**English**: Activity

**Definition**: A single executable task in a workflow

**Usage Guidelines**:

- First occurrence: Activity（活动）
- Subsequent use: Activity or 活动
- Avoid: activity (lowercase)

**Related Terms**: Workflow, Worker, Task Queue

---

#### ACID

**Chinese**: ACID事务

**English**: ACID Transaction

**Definition**: Four basic properties of database transactions: Atomicity, Consistency, Isolation, Durability

**Usage Guidelines**:

- First occurrence: ACID (Atomicity, Consistency, Isolation, Durability)
- Subsequent use: ACID transaction, ACID properties
- Avoid: acid transaction (lowercase)

**Related Terms**: Atomicity, Consistency, Isolation, Durability

---

### B

#### Byzantine Fault Tolerance

**Chinese**: 拜占庭容错

**English**: Byzantine Fault Tolerance (BFT)

**Definition**: The ability of a system to function correctly even in the presence of Byzantine faults (malicious faults)

**Usage Guidelines**:

- Use: Byzantine Fault Tolerance, BFT
- Avoid: Byzantine fault tolerance (unless in specific context)

**Related Terms**: Byzantine Fault, Byzantine Generals Problem

---

### C

#### CAP Theorem

**Chinese**: CAP定理

**English**: CAP Theorem

**Definition**: In distributed systems, Consistency, Availability, and Partition Tolerance cannot be satisfied simultaneously

**Usage Guidelines**:

- Use: CAP Theorem
- Avoid: CAP Theory, CAP Principle

**Related Terms**: Consistency, Availability, Partition Tolerance

---

#### Consistency

**Chinese**: 一致性

**English**: Consistency

**Definition**: All nodes in a distributed system see the same data simultaneously

**Usage Guidelines**:

- In CAP theorem context: use "Consistency"
- In database context: use "Consistency" or "ACID Consistency"
- In consistency model context: use "Consistency Model" or specific model name (e.g., "Linear Consistency")

**Related Terms**: Strong Consistency, Weak Consistency, Eventual Consistency, Linear Consistency, Sequential Consistency

---

### D

#### Distributed Computing

**Chinese**: 分布式计算

**English**: Distributed Computing

**Definition**: Parallel execution of computing tasks across multiple computers

**Usage Guidelines**:

- First occurrence: Distributed Computing（分布式计算）
- Subsequent use: Distributed Computing or 分布式计算

**Related Terms**: Distributed System, Workflow Orchestration

---

#### Durable Execution

**Chinese**: 持久化执行

**English**: Durable Execution

**Definition**: Temporal's core feature that ensures workflow execution state is persisted, allowing recovery even if Workers crash

**Usage Guidelines**:

- Use: Durable Execution, 持久化执行
- First occurrence: Durable Execution（持久化执行）
- Avoid: Persistent Execution, Durable Execution Mechanism (unless in specific context)

**Related Terms**: Event Sourcing, State Recovery

---

### E

#### Event Sourcing

**Chinese**: 事件溯源

**English**: Event Sourcing

**Definition**: Reconstructing system state through event sequences

**Usage Guidelines**:

- First occurrence: Event Sourcing（事件溯源）
- Subsequent use: Event Sourcing or 事件溯源
- Avoid: Event Source (different concept)

**Related Terms**: Durable Execution, Workflow History

---

#### Eventual Consistency

**Chinese**: 最终一致性

**English**: Eventual Consistency

**Definition**: The system will eventually reach a consistent state

**Usage Guidelines**:

- Use: Eventual Consistency, 最终一致性
- First occurrence: Eventual Consistency（最终一致性）

**Related Terms**: Consistency, Strong Consistency, Weak Consistency

---

### F

#### Formal Verification

**Chinese**: 形式化验证

**English**: Formal Verification

**Definition**: Using mathematical methods to verify system correctness

**Usage Guidelines**:

- Use: Formal Verification, 形式化验证
- First occurrence: Formal Verification（形式化验证）

**Related Terms**: Model Checking, Theorem Proving

---

### I

#### Idempotency

**Chinese**: 幂等性

**English**: Idempotency

**Definition**: The result of executing the same operation multiple times is the same

**Usage Guidelines**:

- Use: Idempotency, 幂等性
- First occurrence: Idempotency（幂等性）

**Related Terms**: Compensation, Retry Strategy

---

### L

#### Linear Consistency

**Chinese**: 线性一致性

**English**: Linearizability

**Definition**: The strongest consistency model

**Usage Guidelines**:

- Use: Linear Consistency, Linearizability
- First occurrence: Linear Consistency（线性一致性）

**Related Terms**: Consistency, Sequential Consistency

---

### M

#### Model Checking

**Chinese**: 模型检查

**English**: Model Checking

**Definition**: Automatically verifying properties of finite state systems

**Usage Guidelines**:

- Use: Model Checking, 模型检查
- First occurrence: Model Checking（模型检查）

**Related Terms**: Formal Verification, Theorem Proving

---

### N

#### Namespace

**Chinese**: 命名空间

**English**: Namespace

**Definition**: Used to isolate workflows from different applications or environments

**Usage Guidelines**:

- Use: Namespace, 命名空间
- First occurrence: Namespace（命名空间）

**Related Terms**: Workflow, Task Queue

---

### P

#### Partition Tolerance

**Chinese**: 分区容错性

**English**: Partition Tolerance

**Definition**: The system can still function when network partitions occur

**Usage Guidelines**:

- Use: Partition Tolerance, 分区容错性
- First occurrence: Partition Tolerance（分区容错性）

**Related Terms**: CAP Theorem, Consistency, Availability

---

### S

#### Saga Pattern

**Chinese**: Saga模式

**English**: Saga Pattern

**Definition**: A design pattern for managing distributed long transactions by decomposing them into a series of local transactions and using compensation operations to handle failures

**Usage Guidelines**:

- Use: Saga Pattern, Saga模式
- First occurrence: Saga Pattern（Saga模式）

**Related Terms**: Compensation, Distributed Transaction, Eventual Consistency

---

### T

#### Task Queue

**Chinese**: 任务队列

**English**: Task Queue

**Definition**: A queue used to distribute tasks to Workers

**Usage Guidelines**:

- Use: Task Queue, 任务队列
- First occurrence: Task Queue（任务队列）

**Related Terms**: Worker, Activity, Workflow

---

#### Theorem Proving

**Chinese**: 定理证明

**English**: Theorem Proving

**Definition**: Using logical reasoning to prove system properties

**Usage Guidelines**:

- Use: Theorem Proving, 定理证明
- First occurrence: Theorem Proving（定理证明）

**Related Terms**: Formal Verification, Model Checking

---

### W

#### Worker

**Chinese**: Worker

**English**: Worker

**Definition**: A process or service that executes Activities

**Usage Guidelines**:

- Use: Worker (capitalized)
- First occurrence: Worker（工作进程）

**Related Terms**: Activity, Task Queue, Workflow

---

#### Workflow

**Chinese**: 工作流

**English**: Workflow

**Definition**: An automated execution flow of a series of interrelated tasks or activities

**Usage Guidelines**:

- First occurrence: Workflow（工作流）
- Subsequent use: Workflow or 工作流

**Related Terms**: Activity, Workflow Definition, Workflow Execution

---

#### Workflow Definition

**Chinese**: 工作流定义

**English**: Workflow Definition

**Definition**: Code that describes the structure and logic of a workflow

**Usage Guidelines**:

- Use: Workflow Definition, 工作流定义
- First occurrence: Workflow Definition（工作流定义）

**Related Terms**: Workflow, Workflow Execution

---

#### Workflow Execution

**Chinese**: 工作流执行

**English**: Workflow Execution

**Definition**: A single running instance of a workflow

**Usage Guidelines**:

- Use: Workflow Execution, 工作流执行
- First occurrence: Workflow Execution（工作流执行）

**Related Terms**: Workflow, Workflow Definition, Workflow History

---

#### Workflow History

**Chinese**: 工作流历史

**English**: Workflow History

**Definition**: The sequence of events generated during workflow execution

**Usage Guidelines**:

- Use: Workflow History, 工作流历史
- First occurrence: Workflow History（工作流历史）

**Related Terms**: Workflow Execution, Event Sourcing

---

#### Workflow Orchestration

**Chinese**: 工作流编排

**English**: Workflow Orchestration

**Definition**: Coordinating and managing the execution of tasks in a workflow

**Usage Guidelines**:

- First occurrence: Workflow Orchestration（工作流编排）
- Subsequent use: Workflow Orchestration or 工作流编排

**Related Terms**: Workflow, Distributed Computing

---

**Document Version**: v15.0

**Created**: 2024

**Maintainer**: Project Team
