# 知识图谱可视化工具快速启动指南

**文档版本**：v1.0  
**创建时间**：2025年1月  
**状态**：✅ **开发指南**

---

## 📋 快速开始

本文档提供知识图谱可视化工具的快速启动指南，帮助开发者快速开始开发。

---

## 一、环境准备

### 1.1 前端环境

**要求**：
- Node.js 18+
- npm 9+ 或 yarn 1.22+

**安装**：
```bash
cd tools/knowledge-graph/frontend
npm install
```

### 1.2 后端环境

**要求**：
- Python 3.10+
- pip 23+

**安装**：
```bash
cd tools/knowledge-graph/backend
pip install -r requirements.txt
```

### 1.3 数据库环境

**Neo4j**（图数据库）：
```bash
# 使用Docker运行Neo4j
docker run -d \
  --name neo4j \
  -p 7474:7474 -p 7687:7687 \
  -e NEO4J_AUTH=neo4j/password \
  neo4j:5.15
```

**MongoDB**（文档数据库）：
```bash
# 使用Docker运行MongoDB
docker run -d \
  --name mongodb \
  -p 27017:27017 \
  mongo:7.0
```

---

## 二、开发启动

### 2.1 启动后端服务

```bash
cd tools/knowledge-graph/backend
python -m uvicorn app.main:app --reload --port 8000
```

**验证**：
- API文档：http://localhost:8000/docs
- 健康检查：http://localhost:8000/health

### 2.2 启动前端服务

```bash
cd tools/knowledge-graph/frontend
npm run dev
```

**访问**：
- 前端应用：http://localhost:5173

---

## 三、开发任务

### 3.1 第一阶段：基础框架（2周）

**前端任务**：
- [ ] 完成GraphViewer基础组件
- [ ] 实现D3.js力导向图布局
- [ ] 实现节点和边的渲染

**后端任务**：
- [ ] 完成基础API框架
- [ ] 实现节点查询API
- [ ] 实现关系查询API

### 3.2 第二阶段：核心功能（2周）

**前端任务**：
- [ ] 实现搜索功能
- [ ] 实现过滤功能
- [ ] 实现节点详情展示

**后端任务**：
- [ ] 实现搜索API
- [ ] 实现过滤API
- [ ] 实现数据导入功能

### 3.3 第三阶段：高级功能（2周）

**前端任务**：
- [ ] 实现导出功能
- [ ] 实现交互优化
- [ ] 实现性能优化

**后端任务**：
- [ ] 实现缓存机制
- [ ] 实现性能优化
- [ ] 完善测试

---

## 四、开发规范

### 4.1 代码规范

**前端**：
- 使用ESLint进行代码检查
- 使用Prettier进行代码格式化
- 遵循React最佳实践

**后端**：
- 使用Black进行代码格式化
- 使用Pylint进行代码检查
- 遵循PEP 8规范

### 4.2 Git工作流

```bash
# 创建功能分支
git checkout -b feature/your-feature

# 提交更改
git add .
git commit -m "feat: your feature description"

# 推送分支
git push origin feature/your-feature

# 创建Pull Request
```

### 4.3 测试

**前端测试**：
```bash
npm run test
```

**后端测试**：
```bash
pytest
```

---

## 五、相关文档

- [架构设计](../../docs/08-ENHANCEMENT/工具化开发/P4-知识图谱可视化工具-架构设计.md)
- [实现文档](IMPLEMENTATION.md)
- [README](README.md)

---

**维护者**：项目团队  
**最后更新**：2025年1月
