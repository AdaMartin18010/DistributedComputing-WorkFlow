# 密钥管理KMS 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

密钥管理服务（KMS）是现代信息安全的基础设施，通过集中化的密钥生命周期管理、硬件安全模块（HSM）保护、以及信封加密等技术，为数据加密、数字签名和身份认证提供可信的密钥安全保障。

---

## 一、核心概念

### 1.1 定义与原理

**密钥管理系统（KMS）**是一种集中化服务，负责密钥的生成、存储、分发、轮换和销毁全生命周期管理。

**核心设计原则**：

1. **密钥分层**：根密钥 → 主密钥 → 数据加密密钥（DEK）
2. **职责分离**：密钥管理与业务逻辑分离
3. **安全边界**：HSM提供硬件级密钥保护
4. **审计追踪**：所有密钥操作可审计

**密钥管理生命周期**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    密钥生命周期管理                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐   │
│    │  生成   │───→│  分发   │───→│  使用   │───→│  轮换   │   │
│    │Generate │    │Distribute│   │  Use    │    │ Rotate  │   │
│    └─────────┘    └─────────┘    └────┬────┘    └────┬────┘   │
│         ↑                              │              │        │
│         │                              ↓              │        │
│         │                         ┌─────────┐         │        │
│         └─────────────────────────│  存储   │←────────┘        │
│                                   │ Store   │                  │
│                                   └────┬────┘                  │
│                                        │                        │
│                                        ↓                        │
│                                   ┌─────────┐                   │
│                                   │  销毁   │                   │
│                                   │Destroy  │                   │
│                                   └─────────┘                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 关键特性

- **集中管理**：统一的密钥策略和控制平面
- **高可用性**：多区域冗余和故障转移
- **合规认证**：FIPS 140-2/3、Common Criteria等
- **访问控制**：基于身份的细粒度权限
- **自动化**：密钥轮换和生命周期自动化

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 数据库加密 | ⭐⭐⭐⭐⭐ | 列级/表级加密密钥管理 |
| API密钥保护 | ⭐⭐⭐⭐⭐ | 第三方凭据安全存储 |
| 证书管理 | ⭐⭐⭐⭐⭐ | TLS证书私钥保护 |
| 区块链钱包 | ⭐⭐⭐⭐⭐ | 私钥托管和签名服务 |
| 文件加密 | ⭐⭐⭐⭐ | 文档/对象存储加密 |
| 容器密钥 | ⭐⭐⭐⭐ | Kubernetes Secrets管理 |

---

## 二、技术细节

### 2.1 HSM硬件安全模块

**HSM安全等级（FIPS 140-2）**：

```
┌─────────────────────────────────────────────────────────────────┐
│                 FIPS 140-2 安全等级                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Level 1                                                       │
│  ├── 软件加密算法                                              │
│  ├── 无物理安全要求                                            │
│  └── 例：普通软件加密库                                        │
│                                                                 │
│  Level 2                                                       │
│  ├── 防篡改证据（封条/涂层）                                   │
│  ├── 基于角色的认证                                            │
│  └── 例：入门级硬件加密模块                                    │
│                                                                 │
│  Level 3                                                       │
│  ├── 防篡改检测（清零密钥）                                    │
│  ├── 身份-based认证                                            │
│  ├── 物理隔离密钥                                              │
│  └── 例：企业级HSM（SafeNet Luna）                             │
│                                                                 │
│  Level 4                                                       │
│  ├── 主动防篡改（环境攻击检测）                                │
│  ├── 电压/温度攻击防护                                         │
│  └── 例：军事/金融级HSM                                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**HSM部署模式**：

| 类型 | 形态 | 适用场景 | 代表产品 |
|------|------|----------|----------|
| 物理HSM | 专用硬件设备 | 高安全要求、合规需求 | Thales Luna, SafeNet |
| 云HSM | 云服务 | 云原生应用、弹性需求 | AWS CloudHSM, Azure Dedicated HSM |
| 虚拟HSM | 软件模拟 | 开发测试、低安全场景 | SoftHSM |
| 嵌入式HSM | 集成芯片 | IoT、移动设备 | TPM, Secure Element |

**HSM集成架构**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    HSM集成架构                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  应用层                                                          │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐            │
│  │  WebApp │  │  API    │  │ 数据库  │  │  存储   │            │
│  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘            │
│       └─────────────┴─────────────┴─────────────┘                │
│                     │                                            │
│       ┌─────────────┴─────────────┐                             │
│       │      PKCS#11 / JCE        │                             │
│       │      / CNG / CAPI         │                             │
│       └─────────────┬─────────────┘                             │
│                     │                                            │
│  网络层             │                                            │
│  ┌──────────────────┼──────────────────┐                       │
│  │         TCP/IP 或 PCIe            │                       │
│  └──────────────────┼──────────────────┘                       │
│                     │                                            │
│  HSM层              ↓                                            │
│  ┌────────────────────────────────────────┐                    │
│  │            Hardware Security Module    │                    │
│  │  ┌────────────────────────────────┐   │                    │
│  │  │  • 安全密钥存储区               │   │                    │
│  │  │  • 加密处理器 (AES/RSA/ECC)     │   │                    │
│  │  │  • 真随机数生成器 (TRNG)        │   │                    │
│  │  │  • 防篡改检测电路               │   │                    │
│  │  └────────────────────────────────┘   │                    │
│  └────────────────────────────────────────┘                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 信封加密

**信封加密（Envelope Encryption）原理**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    信封加密机制                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  密钥层次：                                                      │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  根密钥 (Root Key) - 存储于HSM，永不离开                 │   │
│  │  用途：加密/解密主密钥                                   │   │
│  └────────────────────┬────────────────────────────────────┘   │
│                       │ 加密                                   │
│                       ↓                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  主密钥/密钥加密密钥 (KEK) - 存储于KMS                  │   │
│  │  用途：加密/解密数据加密密钥(DEK)                        │   │
│  └────────────────────┬────────────────────────────────────┘   │
│                       │ 加密                                   │
│                       ↓                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  数据加密密钥 (DEK) - 随数据存储                         │   │
│  │  用途：实际加密/解密业务数据                             │   │
│  └────────────────────┬────────────────────────────────────┘   │
│                       │ 加密                                   │
│                       ↓                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   加密数据                               │   │
│  │         (Ciphertext + Encrypted DEK)                    │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  解密流程：                                                      │
│  1. 使用根密钥解密KEK（如果需要）                                │
│  2. 使用KEK解密DEK                                             │
│  3. 使用DEK解密数据                                            │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**信封加密优势**：

| 优势 | 说明 |
|------|------|
| 性能优化 | DEK本地加解密，减少KMS调用 |
| 批量加密 | 一个DEK加密大量数据 |
| 密钥隔离 | DEK与数据一起存储，KEK集中保护 |
| 轮换便利 | 只需轮换KEK，重新加密DEK即可 |
| 访问控制 | 通过KEK访问控制实现细粒度权限 |

### 2.3 密钥轮换

**密钥轮换策略**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    密钥轮换策略                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. 自动定期轮换                                                │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  KMS Key Version                                        │   │
│  │                                                         │   │
│  │  v1 (2024-01) ──→ v2 (2024-07) ──→ v3 (2025-01)        │   │
│  │      │                │                │               │   │
│  │      ▼                ▼                ▼               │   │
│  │   用于解密          当前加密         预创建             │   │
│  │   历史数据          新数据           待命               │   │
│  │                                                         │   │
│  │  配置：每90天自动轮换                                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  2. 即时轮换（密钥泄露响应）                                     │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  检测到泄露 ──→ 立即禁用旧密钥 ──→ 创建新密钥            │   │
│  │       │              │                 │                │   │
│  │       ▼              ▼                 ▼                │   │
│  │   安全事件        禁止新加密       重新加密关键数据       │   │
│  │   响应            允许解密历史     更新所有服务           │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  3. 渐进式DEK轮换                                              │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  无需重新加密所有数据                                     │   │
│  │                                                         │   │
│  │  读取时：                                                 │   │
│  │    Old-DEK ──→ 解密数据 ──→ New-DEK ──→ 重新加密        │   │
│  │                                                         │   │
│  │  写入时：                                                 │   │
│  │    始终使用最新的DEK                                     │   │
│  │                                                         │   │
│  │  优势：零停机、渐进迁移                                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**密钥轮换最佳实践**：

```yaml
# 密钥轮换策略配置
key_rotation_policy:
  # 自动轮换配置
  automatic:
    enabled: true
    interval_days: 90
    schedule: "0 2 * * 0"  # 每周日凌晨2点
    
  # 版本管理
  versions:
    max_versions: 5        # 保留最多5个版本
    min_versions: 2        # 至少保留2个版本
    
  # 通知配置
  notifications:
    before_rotation: 7d    # 轮换前7天通知
    on_failure: immediate  # 失败立即通知
    
  # 合规要求
  compliance:
    pci_dss:
      rotation_period: 1y
    soc2:
      rotation_period: 1y
```

### 2.4 HashiCorp Vault详解

**Vault架构组件**：

```
┌─────────────────────────────────────────────────────────────────┐
│                  HashiCorp Vault 架构                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  API层                                                          │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  HTTP API │ CLI │ SDK (Go/Python/Java)                 │   │
│  └──────────────────────────┬──────────────────────────────┘   │
│                             │                                   │
│  核心层                                                       │
│  ┌──────────────────────────┴──────────────────────────────┐   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │   │
│  │  │  Token Auth │  │  Policy Engine│  │  Audit Log │     │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘     │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │   │
│  │  │  Cubbyhole │  │  Response Wrapping │  │  Lease │     │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘     │   │
│  └─────────────────────────────────────────────────────────┘   │
│                             │                                   │
│  Secret引擎                                                   │
│  ┌──────────────────────────┴──────────────────────────────┐   │
│  │  KV v1/v2 │ Database │ PKI │ AWS │ Azure │ GCP │ SSH   │   │
│  │  Transit  │  RabbitMQ│ ...                           │   │
│  └─────────────────────────────────────────────────────────┘   │
│                             │                                   │
│  存储层                                                       │
│  ┌──────────────────────────┴──────────────────────────────┐   │
│  │  Consul │ etcd │ S3/DynamoDB │ PostgreSQL │ Integrated │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  高可用部署：                                                   │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐                 │
│  │ Vault   │◄────►│  Vault  │◄────►│  Vault  │                 │
│  │ Leader  │      │ Follower│      │ Follower│                 │
│  └────┬────┘      └─────────┘      └─────────┘                 │
│       │                                                         │
│       └──────────────────────────────────► Consul (Raft)        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Vault核心特性**：

| 特性 | 说明 | 使用场景 |
|------|------|----------|
| Dynamic Secrets | 按需生成临时凭据 | 数据库访问、云服务 |
| Secret Versioning | KV引擎的版本控制 | 配置管理、密钥历史 |
| Transit Engine | 加密即服务 | 应用层数据加密 |
| PKI Engine | 证书生命周期管理 | 自动化TLS证书 |
| SSH Engine | 动态SSH证书 | 服务器访问控制 |

**Vault Transit加密示例**：

```bash
# 启用Transit引擎
vault secrets enable transit

# 创建加密密钥
vault write -f transit/keys/my-app-key

# 加密数据
vault write transit/encrypt/my-app-key \
  plaintext=$(base64 <<< "sensitive data")

# 响应：
# Key           Value
# ---           -----
# ciphertext    vault:v1:abcd1234...

# 解密数据
vault write transit/decrypt/my-app-key \
  ciphertext=vault:v1:abcd1234...
```

### 2.5 云KMS对比

**AWS KMS vs 阿里云KMS**：

```
┌─────────────────────────────────────────────────────────────────┐
│              云KMS服务对比                                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  AWS KMS                                                       │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  • 密钥类型: 对称(AES-256) / 非对称(RSA/ECC)            │   │
│  │  • 密钥来源: AWS托管 / 客户托管 / 外部(CloudHSM)        │   │
│  │  • 集成服务: 100+ AWS服务原生集成                       │   │
│  │  • 区域支持: 全球多区域                                   │   │
│  │  • 定价: $1/密钥/月 + API调用费用                       │   │
│  │  • 特色功能:                                            │   │
│  │    - Multi-Region Keys                                  │   │
│  │    - External Key Store (XKS)                           │   │
│  │    - Key Policy + IAM + Grants 三层授权                 │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  阿里云KMS                                                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  • 密钥类型: 对称(SM4/AES) / 非对称(RSA/ECC/SM2)        │   │
│  │  • 密钥来源: 托管版 / 专属版 / 托管密码机               │   │
│  │  • 集成服务: OSS/RDS/ECS等阿里云产品                     │   │
│  │  • 区域支持: 国内/国际多区域                              │   │
│  │  • 定价: 按API调用 + 密钥实例计费                        │   │
│  │  • 特色功能:                                            │   │
│  │    - 国密算法支持(SM2/SM3/SM4)                          │   │
│  │    - 软件/硬件/专属密码机分级                            │   │
│  │    - 应用接入层SDK优化                                   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

| 特性 | AWS KMS | 阿里云KMS |
|------|---------|-----------|
| FIPS 140-2 Level | Level 2 (默认) / Level 3 (CloudHSM) | 二级/三级 |
| 国密算法 | 不支持 | SM2/SM3/SM4 |
| 多区域密钥 | ✅ 原生支持 | ✅ 可用 |
| 外部密钥存储 | ✅ XKS | ✅ 专属版 |
| 自动轮换 | ✅ 1-3年 | ✅ 支持 |
| API限流 | 10,000 req/s | 依实例规格 |
| 访问审计 | CloudTrail | ActionTrail |

---

## 三、系统对比

### 3.1 主流KMS解决方案对比

| 维度 | HashiCorp Vault | AWS KMS | 阿里云KMS | Thales CipherTrust |
|------|-----------------|---------|-----------|-------------------|
| 部署模式 | 自托管/托管 | SaaS | SaaS | 混合 |
| 开源 | 是 (MPL) | 否 | 否 | 否 |
| 动态密钥 | 强 | 有限 | 有限 | 中等 |
| 多云支持 | 强 | AWS生态 | 阿里生态 | 强 |
| Secret类型 | 丰富 | 密钥为主 | 密钥为主 | 丰富 |
| 学习曲线 | 陡峭 | 平缓 | 平缓 | 中等 |
| 企业特性 | 需Enterprise | 完整 | 完整 | 完整 |

### 3.2 选型决策树

```
KMS解决方案选型
│
├── 云环境？
│   ├── AWS独占 → AWS KMS
│   ├── 阿里云独占 → 阿里云KMS
│   ├── Azure独占 → Azure Key Vault
│   └── 多云/混合 → HashiCorp Vault / Thales
│
├── 国密合规要求？
│   ├── 是 → 阿里云KMS / 卫士通等国产方案
│   └── 否 → 国际主流方案
│
├── 动态Secret需求？
│   ├── 高 (DB/云凭据) → HashiCorp Vault
│   └── 低 → 云原生KMS
│
├── 预算限制？
│   ├── 有限 → HashiCorp Vault (开源)
│   └── 充足 → 企业级方案
│
└── 运维能力？
    ├── 强技术团队 → Vault自托管
    └── 有限运维 → 托管KMS服务
```

### 3.3 性能基准

| 指标 | AWS KMS | Vault (优化) | 本地HSM |
|------|---------|--------------|---------|
| 加密延迟 (p99) | ~10ms | ~5ms | ~1ms |
| 吞吐量 | 10K req/s | 依赖部署 | 100+ req/s |
| 密钥创建 | ~100ms | ~50ms | ~200ms |
| 跨区域复制 | 秒级 | 依赖后端 | N/A |

---

## 四、实践指南

### 4.1 部署配置

**HashiCorp Vault生产配置**：

```hcl
# vault.hcl - Vault服务器配置
# 存储后端 - Consul推荐用于HA
storage "consul" {
  address = "127.0.0.1:8500"
  path    = "vault/"
  token   = "${CONSUL_TOKEN}"
}

# 监听器配置
listener "tcp" {
  address       = "0.0.0.0:8200"
  tls_cert_file = "/opt/vault/tls/vault.crt"
  tls_key_file  = "/opt/vault/tls/vault.key"
  
  # TLS版本限制
  tls_min_version = "tls12"
  
  # 代理协议支持
  proxy_protocol_behavior = "allow_authorized"
}

# API地址配置
api_addr = "https://vault.example.com:8200"
cluster_addr = "https://vault-internal.example.com:8201"

# 性能调优
default_max_request_duration = "90s"
max_lease_ttl = "768h"      # 32天最大租约
default_lease_ttl = "768h"

# 审计日志
audit_file {
  path = "/var/log/vault/audit.log"
}

# 遥测
telemetry {
  prometheus_enabled = true
  disable_hostname   = true
}

# Seal配置 - 自动解封（云KMS集成）
seal "awskms" {
  region     = "us-east-1"
  kms_key_id = "arn:aws:kms:us-east-1:..."
}
```

**应用集成示例（Java Spring）**：

```java
@Configuration
public class VaultConfig extends AbstractVaultConfiguration {

    @Override
    public VaultEndpoint vaultEndpoint() {
        return VaultEndpoint.create("vault.example.com", 8200);
    }

    @Override
    public ClientAuthentication clientAuthentication() {
        // AppRole认证
        AppRoleAuthenticationOptions options = AppRoleAuthenticationOptions.builder()
            .roleId(VaultSystemEnvironmentPropertySource.getEnvironment().getProperty("VAULT_ROLE_ID"))
            .secretId(VaultSystemEnvironmentPropertySource.getEnvironment().getProperty("VAULT_SECRET_ID"))
            .build();
        return new AppRoleAuthentication(options, restOperations());
    }

    @Bean
    public VaultTemplate vaultTemplate() {
        return new VaultTemplate(vaultEndpoint(), clientAuthentication());
    }
}

@Service
public class SecretService {
    
    @Autowired
    private VaultTemplate vaultTemplate;
    
    // 读取静态密钥
    public Map<String, String> getDatabaseCredentials() {
        VaultResponse response = vaultTemplate.read("secret/data/database/app");
        return response.getData();
    }
    
    // 动态数据库凭据
    public DatabaseCredentials getDynamicCredentials() {
        VaultResponse response = vaultTemplate.read("database/creds/app-role");
        return response.getData().toDatabaseCredentials();
    }
    
    // Transit加密
    public String encryptSensitiveData(String plaintext) {
        TransitOperations transit = vaultTemplate.opsForTransit();
        CipherText ciphertext = transit.encrypt("app-key", PlainText.of(plaintext));
        return ciphertext.getCiphertext();
    }
}
```

### 4.2 最佳实践

1. **密钥分层策略**
   ```
   根密钥 → 主密钥 → DEK → 数据
   │         │         │
   │         │         └─ 与数据一起存储
   │         └─ KMS存储
   └─ HSM/硬件安全模块
   ```

2. **最小权限原则**
   ```hcl
   # Vault策略示例
   path "secret/data/{{identity.entity.name}}/*" {
     capabilities = ["read", "list"]
   }
   
   path "transit/encrypt/app-key" {
     capabilities = ["update"]
   }
   
   path "transit/decrypt/app-key" {
     capabilities = ["update"]
     # 仅限特定服务
     allowed_entities = ["app-service-1", "app-service-2"]
   }
   ```

3. **审计与监控**
   - 启用所有密钥操作的审计日志
   - 监控异常访问模式
   - 设置密钥即将过期的告警
   - 定期审查密钥权限

4. **灾难恢复**
   - 定期备份KMS数据（加密）
   - 测试密钥恢复流程
   - 多区域部署确保高可用
   - 维护离线恢复密钥（Shamir密封）

### 4.3 常见问题

**Q1: DEK与KEK分离的优势？**
A: 分离架构的优势：
- 性能：DEK本地加解密，无需KMS调用
- 安全：KEK泄露不直接暴露数据
- 管理：DEK可批量轮换而无需重加密数据
- 扩展：支持多KEK策略（如不同区域不同KEK）

**Q2: 如何处理密钥泄露？**
A: 应急响应流程：
1. 立即轮换受影响密钥
2. 审计密钥使用日志
3. 评估数据暴露范围
4. 重新加密敏感数据
5. 更新依赖该密钥的服务
6. 事后分析与加固

**Q3: 自托管Vault vs 托管KMS？**
A: 选择建议：

| 场景 | 推荐方案 |
|------|----------|
| 云原生、简单需求 | 云托管KMS |
| 多云/混合云 | HashiCorp Vault |
| 高动态Secret需求 | HashiCorp Vault |
| 严格合规、有限运维 | 云托管KMS |
| 复杂Secret工作流 | HashiCorp Vault |

---

## 五、形式化分析

### 5.1 密钥层次安全性

**密钥分层安全性证明**：

```
定义：
- K_root: 根密钥，安全级别 L_root
- K_kek: 密钥加密密钥，由 K_root 加密
- K_dek: 数据加密密钥，由 K_kek 加密
- D: 敏感数据，由 K_dek 加密

安全性定理：
若攻击者无法获取 K_root，则无法解密 D。

证明：
1. 攻击者拥有 Enc(K_dek, D) 和 Enc(K_kek, K_dek)
2. 要解密 D，需要 K_dek
3. 要获取 K_dek，需要解密 Enc(K_kek, K_dek)
4. 要解密 Enc(K_kek, K_dek)，需要 K_kek
5. K_kek 由 Enc(K_root, K_kek) 保护
6. 没有 K_root，无法获取 K_kek
∴ 攻击者无法解密 D

安全边界：
- K_root: 存储于HSM，永不离开
- K_kek: 存储于KMS，内存中短暂存在
- K_dek: 与密文一起存储
- 数据: 应用层处理
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [零信任架构详解](./零信任架构详解.md) - 密钥是零信任的身份凭证基础
- [OAuth2与OIDC](./OAuth2与OIDC.md) - 签名密钥管理

### 6.2 下游应用

- 数据库加密（TDE/列级）
- 应用层数据保护
- 数字签名服务
- 区块链钱包托管

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| SSL/TLS | 应用 | KMS管理TLS证书私钥 |
| 数据库加密 | 应用 | TDE密钥管理 |
| 同态加密 | 演进 | 支持密文计算的密钥管理 |
| 量子安全 | 演进 | 后量子加密算法密钥 |

---

## 七、参考资源

### 7.1 官方文档

1. [AWS KMS Documentation](https://docs.aws.amazon.com/kms/)
2. [阿里云KMS文档](https://help.aliyun.com/product/28933.html)
3. [HashiCorp Vault Docs](https://www.vaultproject.io/docs)
4. [NIST SP 800-57 - Key Management](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final)

### 7.2 开源项目

1. [HashiCorp Vault](https://www.vaultproject.io/) - 企业级Secret管理
2. [SoftHSM](https://www.opendnssec.org/softhsm/) - 软件HSM
3. [Tink](https://github.com/google/tink) - Google加密库
4. [AWS Encryption SDK](https://github.com/aws/aws-encryption-sdk)

### 7.3 学习资料

1. [Key Management in the Cloud](https://cloudsecurityalliance.org/) - CSA指南
2. [Cryptography Engineering](https://www.schneier.com/books/cryptography-engineering/) - Schneier
3. [Vault学习路径](https://learn.hashicorp.com/vault) - HashiCorp官方

### 7.4 相关文档

- [零信任架构详解](./零信任架构详解.md)
- [OAuth2与OIDC](./OAuth2与OIDC.md)
- [SAML与LDAP](./SAML与LDAP.md)

---

**维护者**：项目团队
**最后更新**：2026年
