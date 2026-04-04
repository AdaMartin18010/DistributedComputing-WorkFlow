# 分布式计算知识图谱

本目录包含分布式计算知识库的 RDF/图数据库形式知识图谱。

## 📁 文件结构

```
knowledge-graph/
├── README.md                    # 本文件
├── schema.md                    # 知识图谱本体定义（Schema/Ontology）
├── core-concepts.ttl            # 核心概念RDF数据（Turtle格式）
├── visualization-config.json    # D3.js/Cytoscape可视化配置
├── interactive-graph.md         # Mermaid格式交互式图谱
├── sparql-queries.md            # SPARQL查询示例
├── extract_rdf.py               # Markdown转RDF提取脚本
├── stats.py                     # 图谱统计脚本
└── update-workflow.md           # 知识图谱更新工作流文档
```

## 📊 知识图谱统计

| 指标 | 数量 |
|------|------|
| 实体总数 | 180+ |
| 关系总数 | 320+ |
| 唯一谓词 | 25+ |
| 定理 | 8 |
| 算法 | 25+ |
| 系统 | 30+ |
| 论文 | 10+ |
| 人物 | 12 |
| 设计模式 | 20+ |
| 协议 | 15+ |

### 覆盖领域

- ✅ 分布式理论基础（CAP、FLP、一致性模型）
- ✅ 共识算法（Paxos、Raft、PBFT等）
- ✅ 存储系统（etcd、Redis、Cassandra、TiDB等）
- ✅ 消息队列（Kafka、RabbitMQ、RocketMQ等）
- ✅ 云原生技术（Kubernetes、Istio、Prometheus等）
- ✅ 事务处理（2PC、Saga、TCC等）
- ✅ 设计模式（熔断、限流、CQRS等）
- ✅ 安全认证（OAuth、TLS、零信任等）

## 🚀 快速开始

### 查看交互式图谱

打开 `interactive-graph.md`，使用支持 Mermaid 的编辑器查看：

- **VS Code**: 安装 Markdown Preview Mermaid Support 插件
- **GitHub/GitLab**: 直接渲染显示
- **在线**: https://mermaid.live

### 运行 SPARQL 查询

使用支持 SPARQL 的工具查询知识图谱：

```bash
# 使用 Apache Jena
sparql --data=core-concepts.ttl --query=query.sparql

# 使用 rdflib (Python)
python -c "
import rdflib
g = rdflib.Graph()
g.parse('core-concepts.ttl', format='turtle')
results = g.query('SELECT ?s ?p ?o WHERE { ?s ?p ?o } LIMIT 10')
for row in results:
    print(row)
"
```

### 生成统计报告

```bash
python stats.py -i core-concepts.ttl -o stats.json
```

## 📖 Schema 定义

知识图谱使用以下核心类：

| 类 | 描述 | 示例 |
|---|------|------|
| `:Theorem` | 理论定理 | CAP定理、FLP不可能性 |
| `:Algorithm` | 算法 | Paxos、Raft、PBFT |
| `:System` | 系统/工具 | etcd、Kubernetes、Kafka |
| `:Protocol` | 协议 | 2PC、Gossip、SWIM |
| `:Pattern` | 设计模式 | Circuit Breaker、Saga |
| `:Paper` | 学术论文 | Raft论文、Spanner论文 |
| `:Person` | 人物 | Leslie Lamport、Jeff Dean |

### 核心关系

| 关系 | 描述 | 示例 |
|-----|------|------|
| `:isA` | 是一种 | Raft isA ConsensusAlgorithm |
| `:implements` | 实现 | etcd implements Raft |
| `:uses` | 使用 | Kubernetes uses etcd |
| `:extends` | 扩展 | MultiPaxos extends Paxos |
| `:dependsOn` | 依赖 | TiDB dependsOn TiKV |
| `:relatedTo` | 相关 | CAP relatedTo PACELC |
| `:proposes` | 提出 | Lamport proposes Paxos |
| `:proves` | 证明 | Gilbert proves CAPTheorem |

## 🔧 工具脚本

### 从 Markdown 提取 RDF

```bash
# 提取所有文档
python extract_rdf.py -i ../../ -o extracted.ttl -v

# 仅试运行
python extract_rdf.py --dry-run
```

### 统计信息

```bash
python stats.py -i core-concepts.ttl -v
```

## 📝 更新工作流

1. **创建/修改文档**: 添加 YAML Frontmatter，遵循内容规范
2. **提取 RDF**: 运行提取脚本
3. **合并数据**: 合并到 `core-concepts.ttl`
4. **生成可视化**: 更新 Mermaid 和 D3 配置
5. **验证**: 检查链接完整性和语法
6. **提交**: Git 提交变更

详细流程见 [update-workflow.md](./update-workflow.md)

## 🌐 命名空间

```turtle
@prefix : <http://distributedcomputing.org/ontology#> .
@prefix sys: <http://distributedcomputing.org/system#> .
@prefix person: <http://distributedcomputing.org/person#> .
@prefix paper: <http://distributedcomputing.org/paper#> .
```

## 📚 参考资料

- [RDF 1.1 Concepts](https://www.w3.org/TR/rdf11-concepts/)
- [Turtle - Terse RDF Triple Language](https://www.w3.org/TR/turtle/)
- [SPARQL 1.1 Query Language](https://www.w3.org/TR/sparql11-query/)
- [OWL 2 Web Ontology Language](https://www.w3.org/TR/owl2-overview/)

## 🤝 贡献

欢迎通过 Pull Request 贡献知识图谱内容：

1. 确保新实体有唯一 URI
2. 添加完整的元数据（name, category, difficulty等）
3. 建立适当的关系连接
4. 运行验证脚本
5. 更新统计信息

## 📄 许可证

与主项目相同许可证。

---

**维护者**: DistributedComputing-WorkFlow 团队  
**最后更新**: 2026-04-04
