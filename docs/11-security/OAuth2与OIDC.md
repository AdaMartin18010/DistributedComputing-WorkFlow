# OAuth2与OIDC 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

OAuth 2.0和OpenID Connect（OIDC）是现代身份验证和授权的基石协议，为应用程序提供标准化的安全访问机制，支持从单点登录到API授权的全场景身份管理需求。

---

## 一、核心概念

### 1.1 定义与原理

**OAuth 2.0**是一个授权框架，允许第三方应用获取对用户资源的有限访问权限，而无需暴露用户凭据。

**OpenID Connect (OIDC)**构建于OAuth 2.0之上，增加了身份验证层，提供用户身份信息的获取机制。

**核心区别**：

| 特性 | OAuth 2.0 | OpenID Connect |
|------|-----------|----------------|
| 主要目的 | 授权（Authorization） | 认证（Authentication） |
| 获取内容 | 访问令牌（Access Token） | ID令牌 + 访问令牌 |
| 用户信息 | 无标准方式 | 标准化用户信息（UserInfo） |
| 令牌格式 | 无规定 | JWT格式ID令牌 |
| 发现机制 | 无 | 支持Discovery文档 |

**架构角色**：

```
┌─────────────────────────────────────────────────────────────┐
│                    OAuth2/OIDC 参与方                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌──────────┐         ┌──────────┐         ┌──────────┐   │
│   │  资源所有者 │ ←─────→ │   客户端   │ ←─────→ │ 授权服务器 │   │
│   │ (Resource │         │ (Client) │         │ (AuthZ)  │   │
│   │  Owner)  │         │          │         │          │   │
│   └──────────┘         └────┬─────┘         └────┬─────┘   │
│                              │                    │         │
│                              └────────────────────┘         │
│                                         │                   │
│                                         ↓                   │
│                              ┌──────────────────┐           │
│                              │   资源服务器      │           │
│                              │ (Resource Server)│           │
│                              └──────────────────┘           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 关键特性

- **委托授权**：用户可授权第三方应用访问特定资源
- **令牌机制**：使用短期有效的令牌替代长期凭据
- **范围限定**：细粒度的权限控制（Scope）
- **安全分离**：认证与授权职责分离
- **标准化流程**：多种授权模式适应不同场景

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 第三方应用集成 | ⭐⭐⭐⭐⭐ | 社交登录、SaaS集成 |
| 单页应用(SPA) | ⭐⭐⭐⭐⭐ | 浏览器端应用安全认证 |
| 移动应用 | ⭐⭐⭐⭐⭐ | 原生应用授权流程 |
| 机器对机器 | ⭐⭐⭐⭐⭐ | 服务间API调用认证 |
| 传统服务器应用 | ⭐⭐⭐⭐ | 授权码模式为主 |

---

## 二、技术细节

### 2.1 OAuth2授权流程

**四种授权模式对比**：

```
┌──────────────────────────────────────────────────────────────────┐
│                     OAuth2 授权模式选择                            │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. 授权码模式 (Authorization Code)                              │
│     ┌─────────┐                                                 │
│     │  客户端  │ ←── 后端存储令牌                                 │
│     │ (Web App)│                                                 │
│     └────┬────┘                                                 │
│          │ 重定向到授权服务器                                    │
│          ↓                                                       │
│     ┌─────────┐     授权码        ┌─────────┐                   │
│     │  浏览器  │ ──────────────→  │ 授权服务器│                   │
│     │ (前端)   │ ←──────────────  │         │                   │
│     └─────────┘     重定向+授权码   └─────────┘                   │
│          │                                                       │
│          │ 授权码 → 后端                                         │
│          ↓                                                       │
│     ┌─────────┐                                                 │
│     │ 客户端后端│ ─────── 授权码换令牌 ─────→ 授权服务器           │
│     │ (Server)│                                                 │
│     └─────────┘                                                 │
│     【最安全，推荐用于所有服务器端应用】                            │
│                                                                  │
│  2. 简化模式 (Implicit) - 已弃用                                 │
│     直接返回令牌在URL片段，不安全，已废弃                          │
│                                                                  │
│  3. 密码凭证模式 (Resource Owner Password)                       │
│     客户端直接获取用户密码，仅用于受信任的第一方应用                │
│                                                                  │
│  4. 客户端凭证模式 (Client Credentials)                          │
│     机器对机器通信，无用户参与                                    │
│     Client ────→ 直接获取访问令牌 ────→ 资源服务器                 │
│                                                                  │
│  5. 设备授权码模式 (Device Code)                                 │
│     输入受限设备（智能电视、IoT设备）                               │
│     Device ──→ 轮询 ──→ 用户在另一设备完成授权                     │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

**授权码模式详细流程**：

```
Step 1: 授权请求
┌────────────────────────────────────────────────────────────────┐
GET /authorize?response_type=code
              &client_id=CLIENT_ID
              &redirect_uri=REDIRECT_URI
              &scope=openid profile email
              &state=RANDOM_STATE
              &code_challenge=BASE64URL(SHA256(verifier))
              &code_challenge_method=S256
Host: auth.example.com
└────────────────────────────────────────────────────────────────┘

Step 2: 用户认证与同意
[用户登录并授权应用访问]

Step 3: 授权码回调
┌────────────────────────────────────────────────────────────────┐
HTTP/1.1 302 Found
Location: REDIRECT_URI?code=AUTH_CODE&state=RANDOM_STATE
└────────────────────────────────────────────────────────────────┘

Step 4: 令牌交换 (后端服务器)
┌────────────────────────────────────────────────────────────────┐
POST /token HTTP/1.1
Host: auth.example.com
Content-Type: application/x-www-form-urlencoded

grant_type=authorization_code
&code=AUTH_CODE
&redirect_uri=REDIRECT_URI
&client_id=CLIENT_ID
&client_secret=CLIENT_SECRET
&code_verifier=PKCE_VERIFIER  ← PKCE防护
└────────────────────────────────────────────────────────────────┘

Step 5: 令牌响应
┌────────────────────────────────────────────────────────────────┐
{
  "access_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9...",
  "token_type": "Bearer",
  "expires_in": 3600,
  "refresh_token": "dGhpcyBpcyBhIHJlZnJlc2ggdG9rZW4...",
  "scope": "openid profile email",
  "id_token": "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCJ9..."  ← OIDC
}
└────────────────────────────────────────────────────────────────┘
```

### 2.2 JWT令牌

**JWT结构**：

```
Base64Url(Header) + "." + Base64Url(Payload) + "." + Base64Url(Signature)

┌─────────────────────────────────────────────────────────────────┐
│  Header（头部）                                                  │
├─────────────────────────────────────────────────────────────────┤
│  {                                                              │
│    "alg": "RS256",      ← 签名算法                              │
│    "typ": "JWT",        ← 令牌类型                              │
│    "kid": "key-2024-01" ← 密钥标识                              │
│  }                                                              │
└─────────────────────────────────────────────────────────────────┘
                              ↓ Base64Url编码
┌─────────────────────────────────────────────────────────────────┐
│  Payload（载荷）- 声明(Claims)                                   │
├─────────────────────────────────────────────────────────────────┤
│  {                                                              │
│    "iss": "https://auth.example.com",  ← 签发者                 │
│    "sub": "user-12345",                ← 主题(用户ID)            │
│    "aud": "my-app-client",             ← 受众                   │
│    "exp": 1712345678,                  ← 过期时间                │
│    "iat": 1712342078,                  ← 签发时间                │
│    "nbf": 1712342078,                  ← 生效时间                │
│    "jti": "unique-token-id",           ← 令牌唯一标识            │
│    "scope": "read write",              ← 权限范围                │
│    "email": "user@example.com",        ← 自定义声明              │
│    "name": "John Doe"                                          │
│  }                                                              │
└─────────────────────────────────────────────────────────────────┘
                              ↓ Base64Url编码
┌─────────────────────────────────────────────────────────────────┐
│  Signature（签名）                                               │
├─────────────────────────────────────────────────────────────────┤
│  RSASHA256(                                                    │
│    Base64Url(Header) + "." + Base64Url(Payload),               │
│    PrivateKey                                                  │
│  )                                                              │
└─────────────────────────────────────────────────────────────────┘
```

**JWT安全性注意事项**：

| 风险 | 防护措施 |
|------|----------|
| 令牌篡改 | 强签名算法（RS256/ES256） |
| 令牌泄露 | HTTPS传输、短期有效期 |
| 重放攻击 | `jti`声明、令牌黑名单 |
| 算法混淆 | 严格验证`alg`头 |
| 密钥泄露 | 定期轮换、HSM存储 |

### 2.3 OpenID Connect详解

**OIDC身份验证流程**：

```
┌─────────────┐                              ┌─────────────┐
│    用户     │                              │   客户端    │
│   (RP)      │                              │   (OP)      │
└──────┬──────┘                              └──────┬──────┘
       │                                            │
       │ 1. 认证请求 (response_type=code id_token)  │
       │ ─────────────────────────────────────────> │
       │                                            │
       │ 2. 用户登录与同意                          │
       │ <───────────────────────────────────────── │
       │                                            │
       │ 3. 返回授权码                              │
       │ ─────────────────────────────────────────> │
       │                                            │
       │ 4. 令牌请求 (授权码换令牌)                  │
       │ <───────────────────────────────────────── │
       │                                            │
       │ 5. 返回 ID Token + Access Token            │
       │ ─────────────────────────────────────────> │
       │                                            │
       │ 6. 可选: UserInfo请求                      │
       │ <───────────────────────────────────────── │
       │                                            │
```

**ID Token 与 Access Token 区别**：

| 特性 | ID Token | Access Token |
|------|----------|--------------|
| 用途 | 证明用户身份 | 访问受保护资源 |
| 受众 | 客户端应用 | 资源服务器 |
| 内容 | 用户声明（姓名、邮箱等） | 权限范围（Scope） |
| 验证方 | 客户端 | 资源服务器 |
| 示例场景 | 显示用户欢迎信息 | 调用API获取数据 |

**OIDC Discovery端点**：

```json
{
  "issuer": "https://auth.example.com",
  "authorization_endpoint": "https://auth.example.com/oauth2/authorize",
  "token_endpoint": "https://auth.example.com/oauth2/token",
  "userinfo_endpoint": "https://auth.example.com/oauth2/userinfo",
  "jwks_uri": "https://auth.example.com/.well-known/jwks.json",
  "scopes_supported": ["openid", "profile", "email", "offline_access"],
  "response_types_supported": ["code", "id_token", "token id_token"],
  "grant_types_supported": ["authorization_code", "refresh_token"],
  "token_endpoint_auth_methods_supported": ["client_secret_basic", "private_key_jwt"],
  "claims_supported": ["sub", "iss", "aud", "exp", "iat", "name", "email"]
}
```

### 2.4 SSO单点登录

**SSO架构模式**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    SSO 单点登录架构                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                        ┌─────────────────┐                     │
│                        │   身份提供商      │                     │
│                        │  (IdP - Keycloak │                     │
│                        │   Azure AD/Okta) │                     │
│                        └────────┬────────┘                     │
│                                 │                               │
│              ┌──────────────────┼──────────────────┐           │
│              │                  │                  │           │
│              ↓                  ↓                  ↓           │
│       ┌──────────┐      ┌──────────┐      ┌──────────┐        │
│       │ 应用 A   │      │ 应用 B   │      │ 应用 C   │        │
│       │ (SPA)    │      │ (Web)    │      │ (Mobile) │        │
│       └──────────┘      └──────────┘      └──────────┘        │
│                                                                 │
│  登录流程：                                                      │
│  1. 用户访问应用A → 未登录 → 重定向到IdP                         │
│  2. IdP认证用户 → 设置SSO会话Cookie → 返回令牌                   │
│  3. 用户访问应用B → 检测到IdP会话 → 自动获取令牌                  │
│  4. 用户无需再次输入密码                                         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**SSO会话管理**：

| 会话类型 | 存储位置 | 有效期 | 用途 |
|----------|----------|--------|------|
| IdP会话 | IdP域名Cookie | 数小时-数天 | 单点登录状态 |
| 应用会话 | 应用域名Cookie | 数分钟-数小时 | 应用内状态 |
| 刷新令牌 | 安全存储 | 数天-数月 | 静默刷新访问令牌 |

---

## 三、系统对比

### 3.1 主流OAuth2/OIDC提供商对比

| 维度 | Auth0 | Keycloak | Azure AD | Okta | AWS Cognito |
|------|-------|----------|----------|------|-------------|
| 部署方式 | SaaS | 自托管/SaaS | SaaS | SaaS | SaaS |
| 开源 | 否 | 是 | 否 | 否 | 否 |
| 免费额度 | 7,500用户 | 无限制 | Azure订阅内 | 有限试用 | 50,000 MAU |
| 社交登录 | 丰富 | 中等 | Microsoft为主 | 丰富 | 主要平台 |
| MFA支持 | 强 | 中等 | 强 | 强 | 基础 |
| 定制能力 | 中等 | 高 | 低 | 中等 | 低 |
| API管理 | 内置 | 需集成 | Azure APIM | 内置 | API Gateway |

### 3.2 选型决策树

```
OAuth2/OIDC提供商选择
│
├── 预算限制？
│   ├── 有限预算 → Keycloak (开源)
│   └── 可接受SaaS费用 → 继续评估
│
├── 主要云平台？
│   ├── AWS → AWS Cognito
│   ├── Azure → Azure AD B2C
│   └── GCP → Firebase Auth / 第三方
│
├── 企业规模？
│   ├── 初创/小团队 → Auth0 / Firebase
│   ├── 中大型企业 → Okta / Azure AD
│   └── 高度定制需求 → Keycloak
│
├── 合规要求？
│   ├── 严格合规 → Okta / Azure AD (企业版)
│   └── 一般要求 → Auth0 / Keycloak
│
└── 技术栈？
    ├── Java生态 → Keycloak (原生集成)
    ├── .NET → Azure AD
    └── Node.js/Python/Go → Auth0 / Okta
```

### 3.3 性能基准

| 指标 | Auth0 | Keycloak | Azure AD | Okta |
|------|-------|----------|----------|------|
| 认证延迟 (p99) | ~200ms | ~100ms* | ~300ms | ~250ms |
| 令牌验证延迟 | ~5ms | ~2ms* | ~5ms | ~5ms |
| 可用性 SLA | 99.99% | 自管理 | 99.99% | 99.99% |
| 并发支持 | 无限 | 取决于部署 | 无限 | 无限 |

*自托管优化后的性能

---

## 四、实践指南

### 4.1 部署配置

**Spring Boot OAuth2 资源服务器配置**：

```yaml
# application.yml
spring:
  security:
    oauth2:
      resourceserver:
        jwt:
          # 方式1: 通过JWKS URI自动获取公钥
          jwk-set-uri: https://auth.example.com/.well-known/jwks.json
          issuer-uri: https://auth.example.com
          
          # 方式2: 本地公钥（开发测试）
          # public-key-location: classpath:public-key.pem
          
      client:
        registration:
          my-client:
            client-id: ${CLIENT_ID}
            client-secret: ${CLIENT_SECRET}
            scope: openid,profile,email
            authorization-grant-type: authorization_code
            redirect-uri: "{baseUrl}/login/oauth2/code/{registrationId}"
        provider:
          my-provider:
            issuer-uri: https://auth.example.com
```

**Node.js Express 认证中间件**：

```javascript
const { auth } = require('express-oauth2-jwt-bearer');

// JWT验证中间件
const checkJwt = auth({
  audience: 'https://api.example.com',
  issuerBaseURL: 'https://auth.example.com',
  tokenSigningAlg: 'RS256'
});

// 权限检查中间件
const checkPermissions = (requiredPermissions) => {
  return (req, res, next) => {
    const permissions = req.auth?.permissions || [];
    const hasPermissions = requiredPermissions.every(p => permissions.includes(p));
    
    if (!hasPermissions) {
      return res.status(403).json({ error: 'Insufficient permissions' });
    }
    next();
  };
};

// 路由保护
app.get('/api/admin', checkJwt, checkPermissions(['read:admin']), (req, res) => {
  res.json({ message: 'Admin access granted' });
});
```

**PKCE流程实现（SPA）**：

```javascript
// PKCE辅助函数
function generatePKCE() {
  const verifier = generateRandomString(128);
  const challenge = base64URLEncode(sha256(verifier));
  return { verifier, challenge };
}

// 授权流程
async function initiateAuth() {
  const { verifier, challenge } = generatePKCE();
  
  // 存储verifier用于后续令牌交换
  sessionStorage.setItem('pkce_verifier', verifier);
  
  const params = new URLSearchParams({
    response_type: 'code',
    client_id: CLIENT_ID,
    redirect_uri: REDIRECT_URI,
    scope: 'openid profile email',
    code_challenge: challenge,
    code_challenge_method: 'S256',
    state: generateRandomString(32)
  });
  
  window.location.href = `${AUTH_SERVER}/authorize?${params}`;
}

// 回调处理
async function handleCallback(code) {
  const verifier = sessionStorage.getItem('pkce_verifier');
  
  const response = await fetch(`${AUTH_SERVER}/token`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
    body: new URLSearchParams({
      grant_type: 'authorization_code',
      client_id: CLIENT_ID,
      code: code,
      redirect_uri: REDIRECT_URI,
      code_verifier: verifier
    })
  });
  
  const tokens = await response.json();
  // 安全存储令牌
  secureStorage.set('access_token', tokens.access_token);
  secureStorage.set('id_token', tokens.id_token);
}
```

### 4.2 最佳实践

1. **始终使用PKCE**
   - 所有公共客户端（SPA、移动应用）必须使用PKCE
   - 机密客户端也建议使用PKCE增加安全性

2. **安全的令牌存储**
   ```
   浏览器端：
   - Access Token: 内存存储（短期）
   - Refresh Token: httpOnly secure cookie 或 后端代理
   
   移动应用：
   - 使用Keychain(iOS) / Keystore(Android)
   - 启用生物识别保护
   
   服务器端：
   - 加密的Redis/数据库
   - 定期清理过期令牌
   ```

3. **合理的令牌生命周期**
   | 令牌类型 | 推荐有效期 | 说明 |
   |----------|------------|------|
   | Access Token | 5-15分钟 | 短期减少泄露风险 |
   | ID Token | 与Access Token相同 | 身份验证凭证 |
   | Refresh Token | 7-30天 | 长期会话支持 |
   | 授权码 | 1-10分钟 | 一次性使用 |

4. **状态参数与CSRF防护**
   ```javascript
   // 生成随机状态参数
   const state = crypto.randomBytes(32).toString('hex');
   sessionStorage.setItem('oauth_state', state);
   
   // 回调时验证
   if (returnedState !== sessionStorage.getItem('oauth_state')) {
     throw new Error('Invalid state parameter');
   }
   ```

5. **权限设计原则**
   - 使用标准OAuth Scope（`read`, `write`, `delete`）
   - 结合资源标识（`user:read`, `order:write`）
   - 避免过宽的权限（如`admin:*`）
   - 定期审查和回收权限

### 4.3 常见问题

**Q1: 如何处理令牌刷新？**
A: 推荐实现：
```javascript
// Axios拦截器自动刷新
axios.interceptors.response.use(
  response => response,
  async error => {
    const originalRequest = error.config;
    
    if (error.response?.status === 401 && !originalRequest._retry) {
      originalRequest._retry = true;
      const newToken = await refreshAccessToken();
      originalRequest.headers['Authorization'] = `Bearer ${newToken}`;
      return axios(originalRequest);
    }
    return Promise.reject(error);
  }
);
```

**Q2: 前后端分离如何安全实现OAuth2？**
A: 推荐架构：
```
浏览器 → BFF (Backend for Frontend) → OAuth2服务器
          ↓
        资源服务器
```
BFF负责：
- 处理OAuth2流程
- 安全存储Refresh Token
- 代理API请求携带Access Token

**Q3: 如何安全退出登录？**
A: 完整退出流程：
1. 清除本地存储的令牌
2. 调用IdP的结束会话端点（RP-Initiated Logout）
3. 清除IdP会话Cookie
4. 通知所有关联应用（Back-Channel Logout）

---

## 五、形式化分析

### 5.1 安全性分析

**OAuth2安全威胁与防护**：

| 威胁 | 攻击方式 | 防护措施 |
|------|----------|----------|
| 授权码拦截 | 恶意应用注册相同scheme | PKCE、精确重定向URI匹配 |
| CSRF攻击 | 伪造授权请求 | State参数验证 |
| 令牌泄露 | XSS、网络嗅探 | HTTPS、短期令牌、HttpOnly Cookie |
| 重放攻击 | 截获令牌重复使用 | 短期令牌、Token Binding |
| 客户端冒充 | 伪造Client ID | 客户端认证（mTLS、Client Secret） |

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [零信任架构详解](./零信任架构详解.md) - OAuth2是零信任的身份基础
- [SAML与LDAP](./SAML与LDAP.md) - 企业身份源集成
- [密钥管理KMS](./密钥管理KMS.md) - 签名密钥保护

### 6.2 下游应用

- API网关认证
- 微服务间调用认证
- 第三方应用集成

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| SAML 2.0 | 替代方案 | 企业SSO的传统标准 |
| mTLS | 补充 | 双向TLS认证增强安全性 |
| JWT | 依赖 | OAuth2/OIDC的常用令牌格式 |
| UMA | 扩展 | 用户管理的资源授权 |

---

## 七、参考资源

### 7.1 官方规范

1. [RFC 6749 - The OAuth 2.0 Authorization Framework](https://tools.ietf.org/html/rfc6749)
2. [RFC 7636 - Proof Key for Code Exchange (PKCE)](https://tools.ietf.org/html/rfc7636)
3. [OpenID Connect Core 1.0](https://openid.net/specs/openid-connect-core-1_0.html)
4. [RFC 7519 - JSON Web Token (JWT)](https://tools.ietf.org/html/rfc7519)

### 7.2 开源项目

1. [Keycloak](https://www.keycloak.org/) - 开源身份与访问管理
2. [ORY Hydra](https://www.ory.sh/hydra/) - OAuth2/OIDC服务器
3. [Authing](https://authing.cn/) - 国内身份云服务
4. [casdoor](https://casdoor.org/) - 开源身份平台

### 7.3 学习资料

1. [OAuth 2.0 Simplified](https://aaronparecki.com/oauth-2-simplified/) - Aaron Parecki
2. [Auth0 Docs](https://auth0.com/docs) - 实践指南
3. [OAuth.net](https://oauth.net/) - 协议资源汇总

### 7.4 相关文档

- [零信任架构详解](./零信任架构详解.md)
- [SAML与LDAP](./SAML与LDAP.md)
- [密钥管理KMS](./密钥管理KMS.md)

---

**维护者**：项目团队
**最后更新**：2026年
