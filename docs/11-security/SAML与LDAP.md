# SAML与LDAP 专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

SAML（Security Assertion Markup Language）和 LDAP（Lightweight Directory Access Protocol）是企业级身份管理的两大基石技术，分别提供了基于断言的联邦身份认证和目录服务，支撑着全球数百万组织的企业身份基础设施。

---

## 一、核心概念

### 1.1 定义与原理

**LDAP（轻量级目录访问协议）**是一种用于访问和维护分布式目录信息服务的协议，专为读取优化，存储用户、组、设备等身份对象。

**SAML（安全断言标记语言）**是基于XML的开放标准，用于在身份提供商（IdP）和服务提供商（SP）之间交换身份验证和授权数据。

**技术定位对比**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    企业身份管理技术栈                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  身份联邦层 (Federation)                                         │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  SAML 2.0  │  OAuth2/OIDC  │  WS-Federation            │   │
│  └─────────────────────────────────────────────────────────┘   │
│                         ↓                                       │
│  身份源层 (Identity Source)                                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  LDAP/AD   │  数据库      │  HR系统      │ 云目录服务   │   │
│  └─────────────────────────────────────────────────────────┘   │
│                         ↓                                       │
│  应用集成层 (Application Integration)                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  SSO代理   │  应用原生集成  │  API网关    │  零信任    │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 关键特性

**LDAP关键特性**：
- **树形结构**：层次化的目录信息树（DIT）
- **读取优化**：针对查询操作优化设计
- **标准化模式**：定义对象类和属性的标准模式
- **分布式支持**：支持 referrals 和 chaining
- **多平台支持**：跨操作系统的企业标准

**SAML关键特性**：
- **标准化断言**：格式统一的安全声明
- **联邦身份**：跨组织边界共享身份
- **单点退出**：集中式会话注销
- **元数据驱动**：自动化信任关系建立
- **强签名支持**：XML Signature保证完整性

### 1.3 适用场景

| 场景 | LDAP适用性 | SAML适用性 | 说明 |
|------|-----------|-----------|------|
| 企业内部系统认证 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | AD/LDAP是标准选择 |
| 跨组织SSO | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | SAML是B2B联邦首选 |
| 云服务集成 | ⭐⭐ | ⭐⭐⭐⭐ | 现代SaaS广泛支持SAML |
| 移动/SPA应用 | ⭐⭐ | ⭐⭐ | 更推荐OIDC |
| 遗留系统集成 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 传统企业应用支持良好 |

---

## 二、技术细节

### 2.1 LDAP目录服务

**LDAP目录信息树（DIT）结构**：

```
                    dc=example,dc=com
                           │
          ┌────────────────┼────────────────┐
          │                │                │
    ┌─────┴─────┐    ┌─────┴─────┐    ┌─────┴─────┐
    │ou=People  │    │ ou=Groups │    │ ou=Devices│
    └─────┬─────┘    └─────┬─────┘    └─────┬─────┘
          │                │                │
    ┌─────┴─────┐    ┌─────┴─────┐    ┌─────┴─────┐
    │           │    │           │    │           │
┌───┴───┐  ┌───┴───┐│┌───┴───┐  ┌───┴───┐│┌───┴───┐  ┌───┴───┐
│uid=alice│ │uid=bob │││cn=admin│ │cn=users│││cn=ws001│ │cn=ws002│
└─────────┘  └─────────┘│└─────────┘  └─────────┘│└─────────┘  └─────────┘

DN示例：
- uid=alice,ou=People,dc=example,dc=com
- cn=admin,ou=Groups,dc=example,dc=com
```

**LDAP对象类和属性**：

```ldif
# 用户对象示例
dn: uid=alice,ou=People,dc=example,dc=com
objectClass: inetOrgPerson
objectClass: posixAccount
objectClass: shadowAccount
cn: Alice Smith
givenName: Alice
sn: Smith
uid: alice
uidNumber: 10001
gidNumber: 10000
homeDirectory: /home/alice
loginShell: /bin/bash
mail: alice@example.com
telephoneNumber: +1-555-1234
userPassword: {SSHA}encryptedpasswordhash

# 组对象示例
dn: cn=developers,ou=Groups,dc=example,dc=com
objectClass: posixGroup
cn: developers
gidNumber: 10000
memberUid: alice
memberUid: bob
description: Software Development Team
```

**LDAP操作类型**：

| 操作 | 用途 | 性能特征 |
|------|------|----------|
| Bind | 认证用户 | 低延迟，高频率 |
| Search | 查询目录 | 主要操作，优化重点 |
| Compare | 验证属性 | 比Search轻量 |
| Add | 创建条目 | 写入操作，较少 |
| Modify | 更新条目 | 写入操作，较少 |
| Delete | 删除条目 | 写入操作，最少 |

### 2.2 Active Directory详解

**AD架构组件**：

```
┌─────────────────────────────────────────────────────────────────┐
│                   Active Directory 架构                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  林 (Forest) - 安全边界                                          │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  └─ 域树 (Domain Tree)                                   │   │
│  │     ├─ 根域: corp.example.com                           │   │
│  │     │   ├─ 子域: na.corp.example.com                    │   │
│  │     │   │   └─ OU: Sales, IT, HR                        │   │
│  │     │   └─ 子域: eu.corp.example.com                    │   │
│  │     │       └─ OU: Marketing, Engineering                │   │
│  │     │                                                    │   │
│  │     └─ 信任关系 (Trusts)                                  │   │
│  │         ├─ 父子信任 (自动建立)                             │   │
│  │         ├─ 树根信任 (跨树)                                 │   │
│  │         ├─ 外部信任 (与外部域)                             │   │
│  │         └─ 林信任 (跨林)                                   │   │
│  │                                                          │   │
│  │  全局编录 (GC) - 跨域查询索引                              │   │
│  │  架构主控 (Schema Master) - 定义对象类                     │   │
│  │  域命名主控 (Domain Naming) - 管理域添加删除               │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
│  FSMO角色分布：                                                  │
│  ┌────────────────┬──────────────────────────────────────┐    │
│  │ 每个林一个      │ 架构主控、域命名主控                   │    │
│  │ 每个域一个      │ RID主控、PDC模拟器、基础结构主控        │    │
│  └────────────────┴──────────────────────────────────────┘    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**AD与标准LDAP的差异**：

| 特性 | 标准LDAP | Active Directory |
|------|----------|------------------|
| 协议 | LDAPv3 | LDAPv3 + 专有扩展 |
| 认证 | Simple/SASL | NTLM/Kerberos集成 |
| 组策略 | 无 | GPO（核心特性） |
| DNS集成 | 可选 | 必需（SRV记录） |
| 多主复制 | 部分支持 | 完整多主复制 |
| 查询范围 | 本服务器 | 全局编录跨域查询 |

### 2.3 SAML断言详解

**SAML断言类型**：

```xml
<?xml version="1.0" encoding="UTF-8"?>
<saml2:Assertion 
    xmlns:saml2="urn:oasis:names:tc:SAML:2.0:assertion"
    ID="_a75adf55-01d7-40cc-929f-dbd8372ebdfc"
    IssueInstant="2026-01-15T10:30:00Z"
    Version="2.0">
    
    <!-- 签发者 -->
    <saml2:Issuer>https://idp.example.com/metadata</saml2:Issuer>
    
    <!-- 数字签名 -->
    <ds:Signature xmlns:ds="http://www.w3.org/2000/09/xmldsig#">
        <ds:SignedInfo>...</ds:SignedInfo>
        <ds:SignatureValue>...</ds:SignatureValue>
    </ds:Signature>
    
    <!-- 主题 -->
    <saml2:Subject>
        <saml2:NameID Format="urn:oasis:names:tc:SAML:1.1:nameid-format:emailAddress">
            alice@example.com
        </saml2:NameID>
        <saml2:SubjectConfirmation Method="urn:oasis:names:tc:SAML:2.0:cm:bearer">
            <saml2:SubjectConfirmationData 
                NotOnOrAfter="2026-01-15T10:35:00Z"
                Recipient="https://sp.example.com/acs"
                InResponseTo="_4fee3b046395c84e1662c8980b6b5a0b"/>
        </saml2:SubjectConfirmation>
    </saml2:Subject>
    
    <!-- 条件 -->
    <saml2:Conditions NotBefore="2026-01-15T10:25:00Z" 
                      NotOnOrAfter="2026-01-15T10:35:00Z">
        <saml2:AudienceRestriction>
            <saml2:Audience>https://sp.example.com/metadata</saml2:Audience>
        </saml2:AudienceRestriction>
    </saml2:Conditions>
    
    <!-- 身份验证语句 -->
    <saml2:AuthnStatement AuthnInstant="2026-01-15T10:30:00Z" 
                          SessionIndex="_session123">
        <saml2:AuthnContext>
            <saml2:AuthnContextClassRef>
                urn:oasis:names:tc:SAML:2.0:ac:classes:PasswordProtectedTransport
            </saml2:AuthnContextClassRef>
        </saml2:AuthnContext>
    </saml2:AuthnStatement>
    
    <!-- 属性语句 -->
    <saml2:AttributeStatement>
        <saml2:Attribute Name="Role" NameFormat="urn:oasis:names:tc:SAML:2.0:attrname-format:basic">
            <saml2:AttributeValue xsi:type="xs:string">admin</saml2:AttributeValue>
            <saml2:AttributeValue xsi:type="xs:string">developer</saml2:AttributeValue>
        </saml2:Attribute>
        <saml2:Attribute Name="Department" NameFormat="urn:oasis:names:tc:SAML:2.0:attrname-format:basic">
            <saml2:AttributeValue xsi:type="xs:string">Engineering</saml2:AttributeValue>
        </saml2:Attribute>
    </saml2:AttributeStatement>
    
</saml2:Assertion>
```

**SAML SSO流程（SP-initiated）**：

```
┌─────────┐                           ┌─────────┐                           ┌─────────┐
│  用户   │                           │  SP     │                           │  IdP    │
│ (浏览器) │                           │ (应用)   │                           │ (身份源) │
└────┬────┘                           └────┬────┘                           └────┬────┘
     │                                     │                                     │
     │ 1. 访问受保护资源                    │                                     │
     │ ──────────────────────────────────> │                                     │
     │                                     │                                     │
     │ 2. 重定向到IdP (SAMLRequest)         │                                     │
     │ <────────────────────────────────── │                                     │
     │                                     │                                     │
     │ 3. 携带SAMLRequest请求IdP            │                                     │
     │ ───────────────────────────────────────────────────────────────────────> │
     │                                     │                                     │
     │                                     │                                     │ 4. 用户登录
     │                                     │                                     │     (如未登录)
     │                                     │                                     │
     │ 5. 生成SAMLResponse                  │                                     │
     │ <─────────────────────────────────────────────────────────────────────── │
     │                                     │                                     │
     │ 6. POST SAMLResponse到SP ACS端点     │                                     │
     │ ──────────────────────────────────> │                                     │
     │                                     │                                     │
     │ 7. 验证断言并创建会话                │                                     │
     │ <────────────────────────────────── │                                     │
     │                                     │                                     │
     │ 8. 访问受保护资源                    │                                     │
     │ ──────────────────────────────────> │                                     │
     │                                     │                                     │
```

**SAML绑定方式**：

| 绑定类型 | 机制 | 适用场景 |
|----------|------|----------|
| HTTP Redirect | URL参数传递SAMLRequest | 请求较小，SP发起 |
| HTTP POST | Form表单POST | 请求/响应较大 |
| HTTP Artifact | 传递引用而非完整消息 | 高安全性要求 |
| SOAP | WebService调用 | IdP间通信（SLO） |

### 2.4 身份提供商对比

**主流IdP技术栈对比**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    企业身份提供商架构                             │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  现代企业IdP栈                                                   │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  前端门户 (Self-Service Portal)                          │   │
│  │  - 用户自助注册/密码重置                                  │   │
│  │  - 应用目录                                               │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  身份联邦层                                               │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │   │
│  │  │  SAML   │ │  OIDC   │ │ WS-Fed  │ │  CAS    │        │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  身份源连接器                                             │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐        │   │
│  │  │   AD    │ │  LDAP   │ │  SCIM   │ │  数据库  │        │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘        │   │
│  └─────────────────────────────────────────────────────────┘   │
│                              ↓                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  附加服务                                                 │   │
│  │  MFA │ 自适应认证 │ 风控引擎 │ 审计日志                    │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 三、系统对比

### 3.1 LDAP vs Active Directory

| 维度 | OpenLDAP | Active Directory | 389 Directory |
|------|----------|------------------|---------------|
| 许可 | 开源免费 | 商业许可 | 开源免费 |
| 平台 | 跨平台 | Windows Server | Linux |
| 认证协议 | LDAP/SASL | LDAP/Kerberos/NTLM | LDAP/SASL |
| 组策略 | 无 | 完整GPO | 有限 |
| DNS集成 | 无 | 必需 | 可选 |
| 复制 | 单主 | 多主 | 多主 |
| 扩展性 | 高 | 中等 | 高 |
| 管理工具 | CLI/第三方 | ADUC/完整生态 | Web UI |

### 3.2 SAML vs OIDC

| 维度 | SAML 2.0 | OpenID Connect |
|------|----------|----------------|
| 数据格式 | XML | JSON/JWT |
| 消息大小 | 较大 | 紧凑 |
| 浏览器支持 | 需要POST/重定向 | URL友好 |
| 移动/SPA | 支持较差 | 原生支持 |
| 签名 | XML Signature | JWS |
| 加密 | XML Encryption | JWE |
| 企业采用 | 广泛（传统） | 增长（现代） |
| 配置复杂度 | 较高 | 较低 |

### 3.3 选型决策树

```
身份管理技术选型
│
├── 已有微软生态？
│   ├── 是 → Active Directory (推荐)
│   └── 否 → 继续评估
│
├── 预算限制？
│   ├── 严格限制 → OpenLDAP + Keycloak
│   └── 有预算 → 商业方案
│
├── 联邦SSO需求？
│   ├── 企业B2B → SAML 2.0
│   ├── 现代应用 → OIDC
│   └── 两者都需要 → 双协议支持IdP
│
├── 应用类型？
│   ├── 传统/遗留应用 → LDAP/SAML
│   ├── 现代Web/移动 → OIDC
│   └── 混合环境 → 统一IdP支持多协议
│
└── 部署要求？
    ├── 完全本地 → AD/OpenLDAP
    ├── 混合云 → Azure AD/混合方案
    └── 纯云 → Okta/Auth0/OneLogin
```

---

## 四、实践指南

### 4.1 LDAP部署配置

**OpenLDAP基础配置**：

```bash
# slapd.conf - OpenLDAP主配置
# 基础设置
include     /etc/ldap/schema/core.schema
include     /etc/ldap/schema/cosine.schema
include     /etc/ldap/schema/inetorgperson.schema
include     /etc/ldap/schema/nis.schema

pidfile     /var/run/slapd/slapd.pid
argsfile    /var/run/slapd/slapd.args

# 模块加载（启用额外功能）
moduleload  back_mdb
moduleload  ppolicy
moduleload  memberof
moduleload  refint

# 数据库配置
database    mdb
suffix      "dc=example,dc=com"
rootdn      "cn=admin,dc=example,dc=com"
rootpw      {SSHA}encrypted_admin_password
directory   /var/lib/ldap

# 索引优化
index   objectClass     eq
index   cn,sn,uid       pres,eq,sub
index   mail            eq,sub
index   member,memberOf eq

# 访问控制
access to attrs=userPassword
    by self write
    by anonymous auth
    by dn="cn=admin,dc=example,dc=com" write
    by * none

access to *
    by self write
    by dn="cn=admin,dc=example,dc=com" write
    by * read
```

**Spring Boot LDAP集成**：

```java
@Configuration
@EnableWebSecurity
public class LdapSecurityConfig {

    @Bean
    public ActiveDirectoryLdapAuthenticationProvider adProvider() {
        ActiveDirectoryLdapAuthenticationProvider provider = 
            new ActiveDirectoryLdapAuthenticationProvider(
                "corp.example.com",
                "ldap://dc.corp.example.com:389"
            );
        provider.setConvertSubErrorCodesToExceptions(true);
        provider.setUseAuthenticationRequestCredentials(true);
        return provider;
    }

    @Bean
    public LdapTemplate ldapTemplate() {
        return new LdapTemplate(contextSource());
    }

    @Bean
    public LdapContextSource contextSource() {
        LdapContextSource source = new LdapContextSource();
        source.setUrl("ldap://ldap.example.com:389");
        source.setBase("dc=example,dc=com");
        source.setUserDn("cn=service,dc=example,dc=com");
        source.setPassword("${LDAP_BIND_PASSWORD}");
        return source;
    }
}

// LDAP用户查询服务
@Service
public class LdapUserService {
    
    @Autowired
    private LdapTemplate ldapTemplate;
    
    public List<User> searchUsers(String query) {
        return ldapTemplate.search(
            "ou=People",
            "(cn=*" + query + "*)",
            new UserAttributesMapper()
        );
    }
    
    public User findByUsername(String username) {
        return ldapTemplate.findOne(
            query().where("uid").is(username),
            User.class
        );
    }
}
```

### 4.2 SAML配置示例

**Spring Security SAML配置**：

```java
@Configuration
@EnableWebSecurity
public class SamlSecurityConfig {

    @Bean
    public RelyingPartyRegistrationRepository relyingPartyRegistrations() {
        // 从元数据文件加载IdP配置
        RelyingPartyRegistration registration = RelyingPartyRegistrations
            .fromMetadataLocation("classpath:idp-metadata.xml")
            .registrationId("corporate-idp")
            .entityId("https://app.example.com/sp")
            .assertionConsumerServiceLocation("https://app.example.com/login/saml2/sso")
            .signingX509Credentials(c -> c.add(signingCredential()))
            .decryptionX509Credentials(c -> c.add(decryptionCredential()))
            .build();
            
        return new InMemoryRelyingPartyRegistrationRepository(registration);
    }

    @Bean
    public SecurityFilterChain filterChain(HttpSecurity http) throws Exception {
        http
            .authorizeRequests(auth -> auth
                .antMatchers("/public/**").permitAll()
                .anyRequest().authenticated()
            )
            .saml2Login(saml2 -> saml2
                .relyingPartyRegistrationRepository(relyingPartyRegistrations())
                .loginProcessingUrl("/login/saml2/sso")
                .authenticationConverter(new CustomSaml2AuthenticationConverter())
            )
            .logout(logout -> logout
                .logoutSuccessHandler(saml2LogoutSuccessHandler())
            );
        return http.build();
    }
}
```

**SAML断言属性映射**：

```yaml
# SAML属性映射配置
saml:
  attributes:
    # 标准映射
    username: "http://schemas.xmlsoap.org/ws/2005/05/identity/claims/name"
    email: "http://schemas.xmlsoap.org/ws/2005/05/identity/claims/emailaddress"
    firstName: "http://schemas.xmlsoap.org/ws/2005/05/identity/claims/givenname"
    lastName: "http://schemas.xmlsoap.org/ws/2005/05/identity/claims/surname"
    groups: "http://schemas.xmlsoap.org/claims/Group"
    
    # 自定义映射
    department: "Department"
    employeeId: "EmployeeID"
    
  # 角色映射
  role-mapping:
    "cn=admin,ou=Groups,dc=example,dc=com": ROLE_ADMIN
    "cn=developers,ou=Groups,dc=example,dc=com": ROLE_DEVELOPER
    "cn=managers,ou=Groups,dc=example,dc=com": ROLE_MANAGER
```

### 4.3 最佳实践

1. **LDAP安全最佳实践**
   - 始终启用LDAPS（LDAP over SSL/TLS）
   - 使用强密码策略（ppolicy模块）
   - 实施最小权限访问控制
   - 定期审计目录访问日志
   - 配置适当的索引优化查询性能

2. **SAML部署最佳实践**
   - 验证所有断言签名
   - 检查断言有效期（NotBefore/NotOnOrAfter）
   - 验证受众（Audience）匹配
   - 使用HTTPS传输所有消息
   - 实施单点登出（SLO）

3. **混合身份管理**
   ```
   推荐架构：
   ┌─────────────────────────────────────────┐
   │          现代IdP (Okta/Keycloak)        │
   │  ┌─────────────┐    ┌─────────────┐    │
   │  │  OIDC       │    │  SAML       │    │
   │  │  现代应用    │    │ 企业应用     │    │
   │  └─────────────┘    └─────────────┘    │
   └──────────────┬──────────────────────────┘
                  │ LDAP/LDAPS
                  ↓
   ┌─────────────────────────────────────────┐
   │       Active Directory / OpenLDAP       │
   │            权威身份源                    │
   └─────────────────────────────────────────┘
   ```

### 4.3 常见问题

**Q1: LDAP查询性能优化？**
A: 优化策略：
- 为常用查询属性创建索引
- 使用分页处理大结果集
- 限制查询范围（base/one/sub）
- 启用连接池
- 使用全局编录进行跨域查询

**Q2: SAML时钟偏移问题？**
A: 解决方案：
```xml
<!-- 调整时间容差 -->
<saml2:Conditions 
    NotBefore="2026-01-15T10:25:00Z"
    NotOnOrAfter="2026-01-15T10:35:00Z">
```
SP端配置：
```java
// 允许5分钟的时钟偏移
OpenSAMLMetadataResolver resolver = new OpenSAMLMetadataResolver();
resolver.setMaxAssertionTimeSkew(Duration.ofMinutes(5));
```

**Q3: 如何实现AD与云的同步？**
A: 同步方案：
- Azure AD Connect（微软生态）
- Okta Active Directory Agent
- OneLogin LDAP Connector
- 自定义SCIM同步服务

---

## 五、形式化分析

### 5.1 LDAP目录代数

**目录信息树（DIT）形式化**：

```
DIT ::= {Entry}
Entry ::= (DN, {Attribute})
DN ::= RDN [, RDN]*
RDN ::= AttributeType '=' AttributeValue
Attribute ::= (Type, {Value})

操作语义：
- Search(base, scope, filter): Set<Entry>
  scope ∈ {base, one, sub}
  
- Bind(dn, credentials): Boolean
  验证 dn.credentials 与存储的凭据匹配
  
- Add(entry): Unit | Error
  前置条件: entry.dn ∉ DIT
  
- Modify(dn, changes): Unit | Error
  前置条件: dn ∈ DIT
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [OAuth2与OIDC](./OAuth2与OIDC.md) - 现代联邦身份协议
- [零信任架构详解](./零信任架构详解.md) - 身份是现代安全的基础

### 6.2 下游应用

- 企业应用认证集成
- 操作系统登录
- 网络设备管理

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| SCIM | 补充 | 跨域身份管理系统，自动化用户生命周期 |
| Kerberos | 依赖 | AD使用的网络认证协议 |
| RADIUS | 并行 | 网络访问认证协议 |
| X.500 | 前身 | LDAP的基础标准 |

---

## 七、参考资源

### 7.1 官方规范

1. [RFC 4511 - LDAP Protocol](https://tools.ietf.org/html/rfc4511)
2. [SAML 2.0 Specification](http://docs.oasis-open.org/security/saml/v2.0/)
3. [Active Directory Technical Documentation](https://docs.microsoft.com/windows-server/identity/)

### 7.2 开源项目

1. [OpenLDAP](https://www.openldap.org/) - 开源LDAP实现
2. [389 Directory Server](https://directory.fedoraproject.org/) - 企业级LDAP
3. [Keycloak](https://www.keycloak.org/) - 开源IdP支持SAML/OIDC
4. [Shibboleth](https://www.shibboleth.net/) - SAML实现

### 7.3 学习资料

1. [LDAP System Administration](https://www.oreilly.com/library/view/ldap-system-administration/9780596004009/) - O'Reilly
2. [SAML Basics](https://developers.onelogin.com/saml) - OneLogin文档
3. [AD Best Practices](https://docs.microsoft.com/windows-server/identity/ad-ds/plan/best-practices) - Microsoft

### 7.4 相关文档

- [OAuth2与OIDC](./OAuth2与OIDC.md)
- [零信任架构详解](./零信任架构详解.md)
- [密钥管理KMS](./密钥管理KMS.md)

---

**维护者**：项目团队
**最后更新**：2026年
