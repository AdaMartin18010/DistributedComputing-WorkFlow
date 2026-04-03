# TLS/SSL详解

## 概述

传输层安全协议（TLS）及其前身安全套接层（SSL）是互联网安全的基石，为网络通信提供加密、认证和完整性保护。TLS 1.3是最新版本，相比之前的版本有重大改进。在分布式系统中，正确配置和使用TLS对于保护服务间通信至关重要。

---

## 一、TLS协议演进

### 1.1 版本对比

```
┌─────────────────────────────────────────────────────────────┐
│                    TLS/SSL版本演进                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  SSL 2.0 (1995)  ──▶  不安全，已废弃                         │
│       │                                                     │
│       ▼                                                     │
│  SSL 3.0 (1996)  ──▶  POODLE攻击，2015年废弃                 │
│       │                                                     │
│       ▼                                                     │
│  TLS 1.0 (1999)  ──▶  已废弃（PCI DSS 2018）                 │
│       │                                                     │
│       ▼                                                     │
│  TLS 1.1 (2006)  ──▶  已废弃                                 │
│       │                                                     │
│       ▼                                                     │
│  TLS 1.2 (2008)  ──▶  当前广泛使用（配置正确时安全）          │
│       │                                                     │
│       ▼                                                     │
│  TLS 1.3 (2018)  ──▶  推荐版本，更快更安全                    │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│  TLS 1.3主要改进：                                            │
│  • 握手速度提升（1-RTT，支持0-RTT恢复）                        │
│  • 移除不安全的算法（MD5, SHA-1, RSA key exchange等）          │
│  • 前向安全性强制（所有密钥交换使用ECDHE）                     │
│  • 加密更多握手信息（防止中间人窥探）                          │
│  • 简化握手流程，减少往返次数                                  │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 TLS 1.3握手流程

```
TLS 1.3 完整握手（1-RTT）：

客户端                            服务端
  │                                  │
  │  ClientHello                     │
  │  + 支持的密钥交换组               │
  │  + 支持的签名算法                 │
  │  + 密钥份额（Key Share）          │
  │ ────────────────────────────────▶│
  │                                  │
  │                                  │
  │  ServerHello                     │
  │  + 选定的密钥交换组               │
  │  + 服务端密钥份额                 │
  │  {EncryptedExtensions}           │
  │  {Certificate}                   │
  │  {CertificateVerify}             │
  │  {Finished}                      │
  │ ◀────────────────────────────────│
  │                                  │
  │  [Application Data]              │
  │  {Finished}                      │
  │ ────────────────────────────────▶│
  │                                  │
  │  ◄══════ 加密通信建立 ════════►   │
  │                                  │
  │  [Application Data]              │
  │ ◄═══════════════════════════════▶│

符号说明：
{ } - 加密的消息
[ ] - 受保护的应用数据

相比TLS 1.2：
• 减少1个RTT（从2-RTT变为1-RTT）
• 服务端证书加密传输
• 移除ChangeCipherSpec消息
```

### 1.3 TLS 1.3 0-RTT恢复

```
TLS 1.3 会话恢复（0-RTT）：

客户端                            服务端
  │                                  │
  │  ClientHello                     │
  │  + 预共享密钥标识（PSK）          │
  │  + 早期数据（0-RTT数据）          │
  │ ────────────────────────────────▶│
  │                                  │
  │  ServerHello                     │
  │  + 接受的PSK                     │
  │  {EncryptedExtensions}           │
  │  {Finished}                      │
  │  [Application Data]              │
  │ ◀────────────────────────────────│
  │                                  │
  │  ◄════ 0-RTT数据已发送 ══════    │
  │                                  │
  │  {Finished}                      │
  │  [Application Data]              │
  │ ────────────────────────────────▶│
  │                                  │
  │  ◄══════ 加密通信建立 ════════►   │

注意：0-RTT存在前向安全性风险和重放攻击风险
     敏感操作不应使用0-RTT数据
```

---

## 二、TLS协议详解

### 2.1 密钥交换

```
ECDHE密钥交换（TLS 1.3强制）：

客户端                                服务端
  │                                    │
  │  生成临时密钥对: a, A = a*G        │
  │  （G是曲线基点）                    │
  │                                    │
  │  A ───────────────────────────────▶│
  │  (Client Key Share)                │  生成临时密钥对: b, B = b*G
  │                                    │
  │                                    │
  │  ◀────────────────────────────── B │
  │                                    │  (Server Key Share)
  │                                    │
  │  计算共享密钥: S = a*B = a*b*G    │
  │  = 计算共享密钥: S = b*A = b*a*G ──┤
  │                                    │
  │  共享密钥S相同！                    │
  │                                    │
  │  从S派生握手密钥                     │  从S派生握手密钥
  │                                    │

特性：
• 前向安全：即使长期私钥泄露，历史会话也无法解密
• 每次握手使用新的临时密钥对
• 支持X25519, X448, P-256, P-384等曲线
```

### 2.2 证书验证链

```
证书链验证：

┌─────────────────────────────────────────────────────────────┐
│                                                             │
│  端点证书（叶子证书）                                         │
│  Subject: CN=api.example.com                                │
│  Issuer: CN=Intermediate CA 1                               │
│  Signature: [由Intermediate CA 1私钥签名]                     │
│       │                                                     │
│       ▼ 验证                                                │
│  使用Intermediate CA 1的公钥验证签名                          │
│       │                                                     │
│       ▼                                                     │
│  中间证书 1                                                  │
│  Subject: CN=Intermediate CA 1                              │
│  Issuer: CN=Root CA                                         │
│  Signature: [由Root CA私钥签名]                              │
│       │                                                     │
│       ▼ 验证                                                │
│  使用Root CA的公钥验证签名                                    │
│       │                                                     │
│       ▼                                                     │
│  根证书（自签名）                                             │
│  Subject: CN=Root CA                                        │
│  Issuer: CN=Root CA                                         │
│       │                                                     │
│       ▼                                                     │
│  检查根证书是否在系统信任存储中                                │
│                                                             │
│  ✓ 所有验证通过 → 信任链建立                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘

额外验证：
• 证书有效期（Not Before / Not After）
• 域名匹配（CN或SAN）
• 证书吊销状态（CRL或OCSP）
• 证书透明度（CT日志）
• 密钥用途和扩展密钥用途
```

---

## 三、TLS实现

### 3.1 Python TLS服务端

```python
import ssl
import socket
import logging
from pathlib import Path

class TLSServer:
    """
    TLS服务端实现
    支持TLS 1.2+，强制前向安全
    """
    
    def __init__(self, 
                 cert_file: str,
                 key_file: str,
                 ca_file: str = None,
                 require_client_cert: bool = False):
        self.cert_file = cert_file
        self.key_file = key_file
        self.ca_file = ca_file
        self.require_client_cert = require_client_cert
        self.logger = logging.getLogger(__name__)
    
    def create_ssl_context(self) -> ssl.SSLContext:
        """创建安全的SSL上下文"""
        
        # 使用默认服务端上下文（自动选择最佳TLS版本）
        context = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        
        # 加载服务端证书和私钥
        context.load_cert_chain(
            certfile=self.cert_file,
            keyfile=self.key_file
        )
        
        # 客户端证书验证（mTLS）
        if self.require_client_cert:
            context.verify_mode = ssl.CERT_REQUIRED
            if self.ca_file:
                context.load_verify_locations(self.ca_file)
        
        # TLS配置优化
        # 强制TLS 1.2+
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        
        # 仅使用安全密码套件（Python 3.10+支持）
        # 禁用弱算法
        context.set_ciphers(
            'ECDHE+AESGCM:ECDHE+CHACHA20:DHE+AESGCM:!aNULL:!MD5:!DSS'
        )
        
        # 启用会话票据（提升恢复性能）
        context.options |= ssl.OP_NO_TICKET
        
        # 启用OCSP Stapling
        context.ocsp_response_cb = self._ocsp_callback
        
        # 启用证书透明度验证
        if hasattr(context, 'maximum_version'):
            context.maximum_version = ssl.TLSVersion.MAXIMUM_SUPPORTED
        
        return context
    
    def _ocsp_callback(self, ssl_socket, ocsp_response, ocsp_cert):
        """OCSP响应回调"""
        self.logger.info(f"OCSP response received for {ocsp_cert.subject}")
        return True  # 接受响应，实际应验证响应
    
    def start_server(self, host: str = '0.0.0.0', port: int = 8443):
        """启动TLS服务器"""
        context = self.create_ssl_context()
        
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.bind((host, port))
            sock.listen(5)
            
            self.logger.info(f"TLS Server listening on {host}:{port}")
            
            with context.wrap_socket(sock, server_side=True) as ssock:
                while True:
                    try:
                        conn, addr = ssock.accept()
                        self._handle_connection(conn, addr)
                    except ssl.SSLError as e:
                        self.logger.error(f"SSL Error: {e}")
                    except Exception as e:
                        self.logger.error(f"Error: {e}")
    
    def _handle_connection(self, conn: ssl.SSLSocket, addr):
        """处理客户端连接"""
        try:
            # 获取连接信息
            cipher = conn.cipher()
            version = conn.version()
            cert = conn.getpeercert()
            
            self.logger.info(f"Connection from {addr}")
            self.logger.info(f"TLS Version: {version}")
            self.logger.info(f"Cipher: {cipher}")
            
            if cert:
                self.logger.info(f"Client cert: {cert.get('subject')}")
            
            # 处理数据
            data = conn.recv(4096)
            if data:
                response = self._process_request(data)
                conn.send(response)
                
        finally:
            conn.close()
    
    def _process_request(self, data: bytes) -> bytes:
        """处理请求（示例）"""
        return b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nOK"


# Flask应用集成TLS
from flask import Flask

class FlaskTLSServer:
    """Flask应用TLS配置"""
    
    @staticmethod
    def create_app():
        app = Flask(__name__)
        
        @app.route('/')
        def hello():
            return 'Secure Hello World!'
        
        return app
    
    @staticmethod
    def run_tls(app, cert_file: str, key_file: str, 
                host: str = '0.0.0.0', port: int = 8443):
        """以TLS模式运行Flask应用"""
        
        context = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        context.load_cert_chain(cert_file, key_file)
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        
        # 启用HSTS
        @app.after_request
        def add_security_headers(response):
            response.headers['Strict-Transport-Security'] = \
                'max-age=31536000; includeSubDomains; preload'
            response.headers['X-Content-Type-Options'] = 'nosniff'
            return response
        
        app.run(host=host, port=port, ssl_context=context, threaded=True)
```

### 3.2 Python TLS客户端

```python
import ssl
import urllib.request
import certifi
from typing import Optional
import socket

class TLSClient:
    """
    安全TLS客户端
    支持证书固定、主机名验证
    """
    
    def __init__(self, 
                 verify_mode: ssl.VerifyMode = ssl.CERT_REQUIRED,
                 ca_certs: str = None,
                 check_hostname: bool = True):
        self.verify_mode = verify_mode
        self.ca_certs = ca_certs or certifi.where()  # 使用certifi的CA包
        self.check_hostname = check_hostname
        self.pinned_cert: Optional[bytes] = None
    
    def set_certificate_pin(self, cert_hash: bytes):
        """
        设置证书固定（Certificate Pinning）
        
        Args:
            cert_hash: 预期证书公钥的SHA256哈希
        """
        self.pinned_cert = cert_hash
    
    def create_context(self) -> ssl.SSLContext:
        """创建安全客户端SSL上下文"""
        
        context = ssl.create_default_context()
        
        # 配置验证
        context.check_hostname = self.check_hostname
        context.verify_mode = self.verify_mode
        
        # 加载CA证书
        context.load_verify_locations(self.ca_certs)
        
        # 强制TLS 1.2+
        context.minimum_version = ssl.TLSVersion.TLSv1_2
        
        # 仅使用安全密码套件
        context.set_ciphers('ECDHE+AESGCM:ECDHE+CHACHA20:!aNULL:!MD5:!DSS')
        
        # 证书固定验证
        if self.pinned_cert:
            context.load_default_certs()
            # 自定义验证回调
            context.verify_flags = ssl.VERIFY_DEFAULT
        
        return context
    
    def secure_request(self, url: str, 
                      method: str = 'GET',
                      data: bytes = None,
                      headers: dict = None) -> bytes:
        """
        发送安全HTTPS请求
        """
        context = self.create_context()
        
        req = urllib.request.Request(
            url,
            data=data,
            method=method,
            headers=headers or {}
        )
        
        with urllib.request.urlopen(req, context=context) as response:
            return response.read()
    
    def connect_with_pinning(self, host: str, port: int = 443) -> ssl.SSLSocket:
        """
        使用证书固定的连接
        """
        context = self.create_context()
        
        with socket.create_connection((host, port)) as sock:
            with context.wrap_socket(sock, server_hostname=host) as ssock:
                # 获取对端证书
                cert = ssock.getpeercert(binary_form=True)
                
                # 验证证书固定
                if self.pinned_cert:
                    import hashlib
                    cert_hash = hashlib.sha256(cert).digest()
                    if cert_hash != self.pinned_cert:
                        raise ssl.SSLError(
                            "Certificate pinning failed! "
                            "Possible MITM attack."
                        )
                
                return ssock


# 使用示例
if __name__ == "__main__":
    # 基本TLS客户端
    client = TLSClient()
    
    try:
        # 发送HTTPS请求
        response = client.secure_request('https://httpbin.org/get')
        print(f"Response: {response[:200]}...")
    except ssl.SSLError as e:
        print(f"TLS Error: {e}")
    
    # 证书固定示例
    # 首先获取正确证书的哈希
    # openssl s_client -connect api.example.com:443 -servername api.example.com \
    #   | openssl x509 -pubkey -noout | openssl pkey -pubin -outform der \
    #   | openssl dgst -sha256 -binary | base64
```

### 3.3 gRPC TLS配置

```python
import grpc
from concurrent import futures

class GRPCSecurity:
    """
    gRPC TLS安全配置
    """
    
    @staticmethod
    def create_secure_server_credentials(
            server_cert_path: str,
            server_key_path: str,
            ca_cert_path: str = None) -> grpc.ServerCredentials:
        """
        创建服务端TLS凭证
        
        如果提供CA证书，启用mTLS
        """
        with open(server_key_path, 'rb') as f:
            private_key = f.read()
        with open(server_cert_path, 'rb') as f:
            certificate_chain = f.read()
        
        if ca_cert_path:
            # mTLS模式
            with open(ca_cert_path, 'rb') as f:
                root_certificates = f.read()
            
            credentials = grpc.ssl_server_credentials(
                private_key_certificate_chain_pairs=[
                    (private_key, certificate_chain)
                ],
                root_certificates=root_certificates,
                require_client_auth=True
            )
        else:
            # 仅服务端认证
            credentials = grpc.ssl_server_credentials(
                private_key_certificate_chain_pairs=[
                    (private_key, certificate_chain)
                ]
            )
        
        return credentials
    
    @staticmethod
    def create_secure_channel_credentials(
            ca_cert_path: str = None,
            client_cert_path: str = None,
            client_key_path: str = None) -> grpc.ChannelCredentials:
        """
        创建客户端TLS凭证
        """
        if ca_cert_path:
            with open(ca_cert_path, 'rb') as f:
                root_certificates = f.read()
            
            if client_cert_path and client_key_path:
                # mTLS模式
                with open(client_cert_path, 'rb') as f:
                    client_certificate = f.read()
                with open(client_key_path, 'rb') as f:
                    client_key = f.read()
                
                credentials = grpc.ssl_channel_credentials(
                    root_certificates=root_certificates,
                    private_key=client_key,
                    certificate_chain=client_certificate
                )
            else:
                # 仅验证服务端
                credentials = grpc.ssl_channel_credentials(
                    root_certificates=root_certificates
                )
        else:
            # 使用系统默认CA
            credentials = grpc.ssl_channel_credentials()
        
        return credentials
    
    @staticmethod
    def create_secure_channel(target: str, 
                              credentials: grpc.ChannelCredentials,
                              options: dict = None) -> grpc.Channel:
        """
        创建安全gRPC通道
        """
        default_options = [
            ('grpc.ssl_target_name_override', ''),  # 禁用覆盖
            ('grpc.default_authority', ''),
        ]
        
        channel = grpc.secure_channel(
            target,
            credentials,
            options=default_options + (options or [])
        )
        
        return channel
```

---

## 四、TLS安全加固

### 4.1 安全配置检查清单

```python
class TLSSecurityChecker:
    """
    TLS安全配置检查
    """
    
    # 不安全的密码套件（必须禁用）
    INSECURE_CIPHERS = [
        'NULL',
        'aNULL',  # 匿名认证
        'eNULL',  # 无加密
        'EXPORT',  # 出口级弱加密
        'DES',
        'MD5',
        'RC4',
        '3DES',
    ]
    
    # 推荐的密码套件（按优先级排序）
    RECOMMENDED_CIPHERS = [
        'TLS_AES_256_GCM_SHA384',      # TLS 1.3
        'TLS_CHACHA20_POLY1305_SHA256', # TLS 1.3
        'TLS_AES_128_GCM_SHA256',      # TLS 1.3
        'ECDHE-ECDSA-AES256-GCM-SHA384', # TLS 1.2
        'ECDHE-RSA-AES256-GCM-SHA384',
        'ECDHE-ECDSA-CHACHA20-POLY1305',
        'ECDHE-RSA-CHACHA20-POLY1305',
        'ECDHE-ECDSA-AES128-GCM-SHA256',
        'ECDHE-RSA-AES128-GCM-SHA256',
        'DHE-RSA-AES256-GCM-SHA384',
        'DHE-RSA-AES128-GCM-SHA256',
    ]
    
    @classmethod
    def check_ssl_config(cls, context: ssl.SSLContext) -> dict:
        """检查SSL配置安全性"""
        issues = []
        warnings = []
        
        # 检查TLS版本
        if hasattr(context, 'minimum_version'):
            min_version = context.minimum_version
            if min_version.value < ssl.TLSVersion.TLSv1_2.value:
                issues.append(f"TLS版本过低: {min_version.name}")
        
        # 检查证书验证
        if context.verify_mode == ssl.CERT_NONE:
            issues.append("证书验证已禁用！")
        elif context.verify_mode == ssl.CERT_OPTIONAL:
            warnings.append("证书验证为可选模式")
        
        # 检查主机名验证
        if not context.check_hostname and context.verify_mode != ssl.CERT_NONE:
            warnings.append("主机名验证已禁用")
        
        return {
            'secure': len(issues) == 0,
            'issues': issues,
            'warnings': warnings
        }
    
    @classmethod
    def scan_server(cls, host: str, port: int = 443) -> dict:
        """
        扫描服务器TLS配置
        （需要nassl或sslscan工具）
        """
        import subprocess
        
        try:
            result = subprocess.run(
                ['openssl', 's_client', '-connect', f'{host}:{port}',
                 '-tls1_3', '-status'],
                input=b'',
                capture_output=True,
                timeout=10
            )
            
            output = result.stderr.decode()
            
            # 解析输出
            info = {
                'protocol': None,
                'cipher': None,
                'certificate': None,
                'ocsp_stapling': 'OCSP response' in output,
            }
            
            for line in output.split('\n'):
                if 'Protocol  :' in line:
                    info['protocol'] = line.split(':')[1].strip()
                elif 'Cipher    :' in line:
                    info['cipher'] = line.split(':')[1].strip()
            
            return info
            
        except Exception as e:
            return {'error': str(e)}
```

### 4.2 HSTS与安全头部

```
HTTP Strict Transport Security (HSTS)

┌─────────────────────────────────────────────────────────────┐
│                                                             │
│  首次访问（HTTP）：                                           │
│  ┌─────────┐  http://example.com  ┌─────────┐               │
│  │  浏览器  │ ───────────────────▶ │  服务器  │               │
│  └─────────┘                     └─────────┘               │
│                                       │                     │
│                                       ▼                     │
│                            301 重定向到 HTTPS               │
│                                       │                     │
│  ┌─────────┐  https://example.com   │                     │
│  │  浏览器  │ ◀──────────────────────┘                     │
│  └─────────┘                                               │
│                                       │                     │
│                                       ▼                     │
│                            设置HSTS头部                      │
│  Strict-Transport-Security: max-age=31536000;               │
│                             includeSubDomains;              │
│                             preload                         │
│                                                             │
│  后续访问：                                                  │
│  ┌─────────┐                                               │
│  │  浏览器  │  自动将http转换为https（无需服务器重定向）      │
│  │ (HSTS)  │                                               │
│  └─────────┘                                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘

其他安全头部：
• X-Frame-Options: DENY                    # 防止点击劫持
• X-Content-Type-Options: nosniff          # 防止MIME嗅探
• Content-Security-Policy: ...             # CSP策略
• Referrer-Policy: strict-origin-when-cross-origin
```

---

## 五、TLS故障排查

### 5.1 常见问题

```python
class TLSDebugger:
    """
    TLS连接调试工具
    """
    
    @staticmethod
    def diagnose_connection(host: str, port: int = 443) -> dict:
        """
        诊断TLS连接问题
        """
        results = {
            'host': host,
            'port': port,
            'tests': []
        }
        
        # 测试1: 基本连接
        try:
            context = ssl.create_default_context()
            with socket.create_connection((host, port), timeout=10) as sock:
                with context.wrap_socket(sock, server_hostname=host) as ssock:
                    results['tests'].append({
                        'name': 'TLS Connection',
                        'status': 'PASS',
                        'version': ssock.version(),
                        'cipher': ssock.cipher(),
                        'cert': ssock.getpeercert()
                    })
        except ssl.SSLError as e:
            results['tests'].append({
                'name': 'TLS Connection',
                'status': 'FAIL',
                'error': str(e)
            })
        except Exception as e:
            results['tests'].append({
                'name': 'TLS Connection',
                'status': 'FAIL',
                'error': f"Network error: {e}"
            })
        
        # 测试2: 证书过期
        # 测试3: 主机名匹配
        # 测试4: 支持的TLS版本
        
        return results
    
    @staticmethod
    def get_cert_info(host: str, port: int = 443) -> dict:
        """获取证书详细信息"""
        import OpenSSL.SSL
        
        context = OpenSSL.SSL.Context(OpenSSL.SSL.TLSv1_2_METHOD)
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        
        connection = OpenSSL.SSL.Connection(context, sock)
        connection.set_connect_state()
        connection.set_tlsext_host_name(host.encode())
        
        sock.connect((host, port))
        connection.do_handshake()
        
        cert = connection.get_peer_certificate()
        
        info = {
            'subject': dict(cert.get_subject().get_components()),
            'issuer': dict(cert.get_issuer().get_components()),
            'serial_number': cert.get_serial_number(),
            'not_before': cert.get_notBefore().decode(),
            'not_after': cert.get_notAfter().decode(),
            'fingerprint': cert.digest('sha256').decode(),
        }
        
        sock.close()
        return info
```

---

## 六、最佳实践

1. **使用TLS 1.3**，最低TLS 1.2
2. **启用证书固定**对高安全性要求应用
3. **配置OCSP Stapling**提高性能和隐私
4. **使用强密码套件**，定期审查
5. **监控证书过期**，设置告警
6. **启用HSTS**防止降级攻击
7. **定期轮换证书**（建议90天）

---

## 参考资源

- [RFC 8446: TLS 1.3](https://tools.ietf.org/html/rfc8446)
- [Mozilla SSL Configuration Generator](https://ssl-config.mozilla.org/)
- [Qualys SSL Labs](https://www.ssllabs.com/ssltest/)
- [OWASP TLS Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/Transport_Layer_Protection_Cheat_Sheet.html)
