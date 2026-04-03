# MLOps实践专题文档

**文档版本**：v1.0
**创建时间**：2026年
**最后更新**：2026年
**状态**：🔄 编写中

---

## 📋 执行摘要

MLOps（机器学习运维）是将DevOps最佳实践应用于机器学习领域的工程学科，旨在实现ML模型的快速、可靠、可重复的部署和运维。本文档深入分析ML生命周期管理、模型版本控制、A/B测试、模型监控和CI/CD for ML等核心实践。

---

## 一、核心概念

### 1.1 定义与原理

**MLOps** 是一门工程学科，结合了机器学习、软件工程和数据工程的实践，旨在自动化和监控机器学习系统的整个生命周期。

**核心原理**：

- **自动化**：自动化ML流水线的各个环节
- **可复现性**：确保实验和结果可复现
- **可观测性**：全面监控模型和数据
- **协作**：促进跨团队协作
- **持续集成/部署**：快速迭代和部署

**MLOps成熟度模型**：

```
Level 5: AI驱动自动化
    │
Level 4: 全自动化CD4ML
    │
Level 3: 自动化CI/CD
    │
Level 2: 可复现流程
    │
Level 1: 手动流程
```

### 1.2 关键特性

| 特性 | 描述 | DevOps对比 |
|------|------|------------|
| **数据版本控制** | 数据集版本化管理 | 代码版本控制 |
| **模型版本控制** | 模型artifact版本化 | 应用版本控制 |
| **实验追踪** | 记录实验参数和结果 | 构建日志 |
| **模型注册** | 中心化模型管理 | Artifact仓库 |
| **特征存储** | 特征版本化和共享 | 配置中心 |
| **模型监控** | 性能和数据漂移检测 | 应用监控 |
| **自动重训练** | 触发式模型更新 | 自动部署 |

### 1.3 适用场景

| 场景 | 适用性 | 说明 |
|------|--------|------|
| 生产级ML服务 | ⭐⭐⭐⭐⭐ | 必须实施MLOps |
| 多模型管理 | ⭐⭐⭐⭐⭐ | 统一管理平台 |
| 快速迭代实验 | ⭐⭐⭐⭐⭐ | 追踪和对比实验 |
| 团队协作开发 | ⭐⭐⭐⭐⭐ | 标准化流程 |
| 合规审计要求 | ⭐⭐⭐⭐ | 完整追溯链 |
| 原型验证 | ⭐⭐ | 可能过度工程 |

---

## 二、技术细节

### 2.1 ML生命周期管理

**ML生命周期**：

```
┌─────────────────────────────────────────────────────────────────┐
│                     ML生命周期                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐    │
│   │  数据准备 │──►│ 模型开发 │──►│ 模型部署 │──►│ 模型监控 │    │
│   │ ──────── │   │ ──────── │   │ ──────── │   │ ──────── │    │
│   │ 数据收集 │   │ 特征工程 │   │ 打包封装 │   │ 性能监控 │    │
│   │ 数据验证 │   │ 模型训练 │   │ 服务部署 │   │ 漂移检测 │    │
│   │ 数据版本 │   │ 超参调优 │   │ A/B测试 │   │ 告警触发 │    │
│   └────┬─────┘   └────┬─────┘   └────┬─────┘   └────┬─────┘    │
│        │              │              │              │          │
│        └──────────────┴──────────────┴──────────────┘          │
│                       │                                         │
│                       ▼                                         │
│              ┌─────────────────┐                                │
│              │   反馈循环      │                                │
│              │   ───────────  │                                │
│              │   触发重训练    │                                │
│              │   模型更新      │                                │
│              └─────────────────┘                                │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**ML元数据追踪**：

```python
# MLflow追踪示例
import mlflow
from mlflow.models.signature import infer_signature

mlflow.set_experiment("fraud_detection")

with mlflow.start_run(run_name="xgboost_v1"):
    # 记录参数
    mlflow.log_param("model_type", "xgboost")
    mlflow.log_param("n_estimators", 100)
    mlflow.log_param("max_depth", 6)
    mlflow.log_param("learning_rate", 0.1)

    # 训练模型
    model = XGBClassifier(**params)
    model.fit(X_train, y_train)

    # 评估
    accuracy = model.score(X_test, y_test)
    precision = precision_score(y_test, y_pred)
    recall = recall_score(y_test, y_pred)

    # 记录指标
    mlflow.log_metric("accuracy", accuracy)
    mlflow.log_metric("precision", precision)
    mlflow.log_metric("recall", recall)

    # 记录模型
    signature = infer_signature(X_train, model.predict(X_train))
    mlflow.xgboost.log_model(model, "model", signature=signature)

    # 记录artifact
    mlflow.log_artifact("confusion_matrix.png")
    mlflow.log_artifact("feature_importance.json")
```

### 2.2 模型版本控制

**DVC (Data Version Control)**：

```
┌─────────────────────────────────────────────────────────────────┐
│                      DVC工作流                                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Git Repo                       Remote Storage                  │
│   ────────                       ─────────────                  │
│                                                                  │
│   .dvc/                          s3://ml-artifacts/             │
│   ├── .gitignore                 ├── data/                      │
│   ├── data.csv.dvc               │   └── raw_data_v1.csv       │
│   └── model.pkl.dvc              ├── models/                    │
│                                  │   ├── model_v1.pkl          │
│   data.csv  ─────────────────────►│   └── model_v2.pkl          │
│   (pointer)                      └── metrics/                   │
│                                      └── validation.json        │
│                                                                  │
│   工作流程:                                                      │
│   1. dvc add data.csv ──► 创建.dvc文件                         │
│   2. git add data.csv.dvc .gitignore                           │
│   3. dvc push ──► 上传到远程存储                                │
│   4. git commit/push ──► 版本化指针                            │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**DVC配置示例**：

```yaml
# .dvc/config
[core]
    autostage = true
['remote "s3-remote"']
    url = s3://my-ml-bucket/dvc-storage
    region = us-east-1
['remote "gs-remote"']
    url = gs://my-ml-bucket/dvc-storage
[feature]
    machine = true
```

```bash
# DVC常用命令
dvc init                          # 初始化
dvc remote add -d s3 s3://bucket  # 添加远程存储
dvc add data/training.csv         # 追踪数据文件
dvc add models/model.pkl          # 追踪模型文件
dvc push                          # 推送到远程
dvc pull                          # 从远程拉取
dvc checkout v1.0                 # 切换到版本
dvc metrics show                  # 查看指标
dvc params diff                   # 参数对比
```

**MLflow Model Registry**：

```python
import mlflow
from mlflow.tracking import MlflowClient

client = MlflowClient()

# 注册模型
model_name = "fraud_detection_model"
result = mlflow.register_model(
    model_uri=f"runs:/{run_id}/model",
    name=model_name
)

# 添加版本标签
client.set_model_version_tag(
    name=model_name,
    version=result.version,
    key="validation_status",
    value="approved"
)

# 阶段转换
client.transition_model_version_stage(
    name=model_name,
    version=result.version,
    stage="Staging"
)

# 设置别名（推荐方式）
client.set_registered_model_alias(
    name=model_name,
    alias="champion",
    version=result.version
)
```

**模型版本状态流转**：

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│  None    │───►│ Staging  │───►│Production│───►│ Archived │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
      │              │              │                │
      │              ▼              ▼                │
      │         [Testing]      [Monitoring]          │
      │              │              │                │
      └──────────────┴──────────────┴────────────────┘
                     [Rollback if issues]
```

### 2.3 A/B测试

**A/B测试架构**：

```
┌─────────────────────────────────────────────────────────────────┐
│                      A/B测试架构                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Traffic                        Traffic Splitter               │
│   ───────                        ───────────────                │
│      │                                   │                      │
│      │         ┌─────────────────────────┼─────────────────┐   │
│      │         │                         │                 │   │
│      │    90%  │                    10%  │                 │   │
│      │         ▼                         ▼                 │   │
│      │  ┌─────────────┐           ┌─────────────┐          │   │
│      │  │ Model A     │           │ Model B     │          │   │
│      │  │ (Champion)  │           │ (Challenger)│          │   │
│      │  │ ─────────── │           │ ─────────── │          │   │
│      │  │ v1.0        │           │ v1.1        │          │   │
│      │  │ Latency: 5ms│           │ Latency: 4ms│          │   │
│      └─►│ Accuracy:92%│           │ Accuracy:94%│          │   │
│         └──────┬──────┘           └──────┬──────┘          │   │
│                │                         │                 │   │
│                └───────────┬─────────────┘                 │   │
│                            │                               │   │
│                            ▼                               │   │
│                   ┌─────────────────┐                      │   │
│                   │  Metrics Store  │                      │   │
│                   │ ─────────────── │                      │   │
│                   │ • Response logs │                      │   │
│                   │ • Business KPIs │                      │   │
│                   │ • Model metrics │                      │   │
│                   └────────┬────────┘                      │   │
│                            │                               │   │
│                            ▼                               │   │
│                   ┌─────────────────┐                      │   │
│                   │  Statistical    │                      │   │
│                   │  Analysis       │                      │   │
│                   │ (p-value < 0.05)│                      │   │
│                   └─────────────────┘                      │   │
│                                                             │   │
└─────────────────────────────────────────────────────────────────┘
```

**A/B测试实现(Kubernetes + Istio)**：

```yaml
# VirtualService for A/B testing
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: model-routing
spec:
  hosts:
    - model-service
  http:
    - match:
        - headers:
            x-ab-test:
              exact: "b"
      route:
        - destination:
            host: model-service
            subset: v2
          weight: 100
    - route:
        - destination:
            host: model-service
            subset: v1
          weight: 90
        - destination:
            host: model-service
            subset: v2
          weight: 10
---
# DestinationRule
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: model-versions
spec:
  host: model-service
  subsets:
    - name: v1
      labels:
        version: v1.0
    - name: v2
      labels:
        version: v1.1
```

**A/B测试分析**：

```python
import numpy as np
from scipy import stats

def ab_test_analysis(control_metrics, treatment_metrics, metric_name):
    """
    A/B测试统计分析
    """
    control = np.array(control_metrics)
    treatment = np.array(treatment_metrics)

    # 描述统计
    control_mean = np.mean(control)
    treatment_mean = np.mean(treatment)
    lift = (treatment_mean - control_mean) / control_mean * 100

    # 统计检验
    t_stat, p_value = stats.ttest_ind(treatment, control)

    # 置信区间
    diff_mean = treatment_mean - control_mean
    se = np.sqrt(
        np.var(control, ddof=1)/len(control) +
        np.var(treatment, ddof=1)/len(treatment)
    )
    ci_low = diff_mean - 1.96 * se
    ci_high = diff_mean + 1.96 * se

    # 统计功效
    effect_size = diff_mean / np.sqrt(
        (np.var(control) + np.var(treatment)) / 2
    )

    result = {
        "metric": metric_name,
        "control_mean": control_mean,
        "treatment_mean": treatment_mean,
        "relative_lift": f"{lift:+.2f}%",
        "p_value": p_value,
        "significant": p_value < 0.05,
        "ci_95": (ci_low, ci_high),
        "effect_size": effect_size,
        "recommendation": "promote" if p_value < 0.05 and lift > 0 else "keep"
    }

    return result

# 使用示例
control_ctr = [0.02, 0.021, 0.019, 0.022, 0.02]  # 对照组CTR
treatment_ctr = [0.023, 0.025, 0.024, 0.026, 0.025]  # 实验组CTR

result = ab_test_analysis(control_ctr, treatment_ctr, "CTR")
print(f"Relative Lift: {result['relative_lift']}")
print(f"P-value: {result['p_value']:.4f}")
print(f"Recommendation: {result['recommendation']}")
```

### 2.4 模型监控

**监控体系**：

```
┌─────────────────────────────────────────────────────────────────┐
│                      模型监控体系                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    Data Quality                          │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐        │   │
│  │  │Schema Check│  │Missing Val │  │ Range Check│        │   │
│  │  │Type Mismatch│  │Null Rate   │  │Outliers    │        │   │
│  │  └────────────┘  └────────────┘  └────────────┘        │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│  ┌─────────────────────────┴───────────────────────────────┐   │
│  │                    Data Drift                            │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐        │   │
│  │  │  PSI       │  │  KS Test   │  │ Wasserstein│        │   │
│  │  │(Population │  │(Distribution│  │  Distance  │        │   │
│  │  │ Stability) │  │  Test)     │  │            │        │   │
│  │  └────────────┘  └────────────┘  └────────────┘        │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│  ┌─────────────────────────┴───────────────────────────────┐   │
│  │                    Concept Drift                         │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐        │   │
│  │  │Prediction  │  │ Label Shift│  │ Error Rate │        │   │
│  │  │Distribution│  │            │  │ Trend      │        │   │
│  │  └────────────┘  └────────────┘  └────────────┘        │   │
│  └─────────────────────────┬───────────────────────────────┘   │
│                            │                                    │
│  ┌─────────────────────────┴───────────────────────────────┐   │
│  │                    Performance                           │   │
│  │  ┌────────────┐  ┌────────────┐  ┌────────────┐        │   │
│  │  │Latency P99 │  │ Throughput │  │  Error Rate│        │   │
│  │  │CPU/Memory  │  │ GPU Util   │  │ Queue Depth│        │   │
│  │  └────────────┘  └────────────┘  └────────────┘        │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**漂移检测算法**：

| 算法 | 类型 | 适用场景 | 敏感度 |
|------|------|----------|--------|
| **PSI** | 分布对比 | 特征分布 | 中 |
| **KS Test** | 统计检验 | 连续特征 | 高 |
| **Chi-Square** | 统计检验 | 离散特征 | 中 |
| **Wasserstein** | 距离度量 | 整体分布 | 高 |
| **KL Divergence** | 信息论 | 概率分布 | 高 |
| **Drift Detection Method (DDM)** | 在线检测 | 概念漂移 | 高 |

**Evidently AI监控示例**：

```python
from evidently import ColumnMapping
from evidently.report import Report
from evidently.metric_preset import DataDriftPreset, TargetDriftPreset
from evidently.metrics import *

# 定义列映射
column_mapping = ColumnMapping(
    target='target',
    prediction='prediction',
    numerical_features=['feature_1', 'feature_2'],
    categorical_features=['category']
)

# 数据漂移报告
data_drift_report = Report(metrics=[
    DataDriftPreset(),
])

data_drift_report.run(
    reference_data=reference_df,
    current_data=current_df,
    column_mapping=column_mapping
)

# 保存报告
data_drift_report.save_html("data_drift_report.html")

# 获取指标摘要
drift_metrics = data_drift_report.as_dict()
print(f"Drift detected: {drift_metrics['metrics'][0]['result']['dataset_drift']}")

# 概念漂移报告
concept_drift_report = Report(metrics=[
    TargetDriftPreset(),
    ColumnDriftMetric(column_name='prediction'),
    RegressionErrorMetric()
])

concept_drift_report.run(
    reference_data=reference_df,
    current_data=current_df,
    column_mapping=column_mapping
)
```

**自定义监控服务**：

```python
import numpy as np
from scipy.stats import ks_2samp, chi2_contingency
from dataclasses import dataclass
from typing import Dict, List
import logging

@dataclass
class DriftReport:
    feature_name: str
    drift_detected: bool
    p_value: float
    statistic: float
    threshold: float

class DriftDetector:
    def __init__(self, threshold: float = 0.05):
        self.threshold = threshold
        self.reference_stats = {}

    def fit_reference(self, reference_data: pd.DataFrame):
        """学习参考分布"""
        for column in reference_data.columns:
            if reference_data[column].dtype in ['int64', 'float64']:
                self.reference_stats[column] = {
                    'type': 'numerical',
                    'data': reference_data[column].values
                }
            else:
                self.reference_stats[column] = {
                    'type': 'categorical',
                    'distribution': reference_data[column].value_counts(normalize=True).to_dict()
                }

    def detect_drift(self, current_data: pd.DataFrame) -> List[DriftReport]:
        """检测数据漂移"""
        reports = []

        for column, ref_stats in self.reference_stats.items():
            if ref_stats['type'] == 'numerical':
                # KS检验
                statistic, p_value = ks_2samp(
                    ref_stats['data'],
                    current_data[column].values
                )
            else:
                # Chi-Square检验
                current_dist = current_data[column].value_counts(normalize=True)
                categories = set(ref_stats['distribution'].keys()) | set(current_dist.index)

                ref_counts = [ref_stats['distribution'].get(c, 0) * len(ref_stats['data'])
                             for c in categories]
                curr_counts = [current_dist.get(c, 0) * len(current_data)
                              for c in categories]

                _, p_value, _, _ = chi2_contingency([ref_counts, curr_counts])
                statistic = 0  # Chi-square统计量

            reports.append(DriftReport(
                feature_name=column,
                drift_detected=p_value < self.threshold,
                p_value=p_value,
                statistic=statistic,
                threshold=self.threshold
            ))

        return reports

# 使用示例
detector = DriftDetector(threshold=0.05)
detector.fit_reference(reference_df)

drift_reports = detector.detect_drift(current_df)
for report in drift_reports:
    if report.drift_detected:
        logging.warning(
            f"Drift detected in {report.feature_name}: "
            f"p-value={report.p_value:.4f}"
        )
```

### 2.5 CI/CD for ML

**MLOps流水线**：

```
┌─────────────────────────────────────────────────────────────────┐
│                      MLOps CI/CD流水线                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Git Push                                                       │
│     │                                                           │
│     ▼                                                           │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐  │
│  │   CI     │───►│   CT     │───►│   CD     │───►│  Monitor │  │
│  │ ──────── │    │ ──────── │    │ ──────── │    │ ──────── │  │
│  │ Code Test│    │Data Test │    │Deploy    │    │ Feedback │  │
│  │ Lint     │    │Model Test│    │Staging   │    │ Trigger  │  │
│  │ Unit Test│    │Val. Perf │    │Prod A/B  │    │ Retrain  │  │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘  │
│       │              │              │              │            │
│       ▼              ▼              ▼              ▼            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                    Artifact Store                        │   │
│  │  Git ──► DVC ──► MLflow ──► Docker Registry ──► K8s    │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**GitHub Actions MLOps Pipeline**：

```yaml
# .github/workflows/mlops-pipeline.yml
name: MLOps Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  # 1. 代码质量检查
  lint-and-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.9'

      - name: Install dependencies
        run: |
          pip install -r requirements.txt
          pip install black flake8 pytest

      - name: Lint with flake8
        run: flake8 src/ --max-line-length=100

      - name: Format check with black
        run: black --check src/

      - name: Unit tests
        run: pytest tests/unit/ -v

  # 2. 数据验证
  data-validation:
    runs-on: ubuntu-latest
    needs: lint-and-test
    steps:
      - uses: actions/checkout@v3

      - name: Pull DVC data
        run: |
          pip install dvc[s3]
          dvc pull

      - name: Validate data schema
        run: |
          python scripts/validate_data.py \
            --data-path data/training.csv \
            --schema schema/training_schema.json

      - name: Data drift check
        run: |
          python scripts/check_drift.py \
            --reference data/reference.csv \
            --current data/training.csv

  # 3. 模型训练与验证
  train-and-validate:
    runs-on: ubuntu-latest
    needs: data-validation
    steps:
      - uses: actions/checkout@v3

      - name: Setup MLflow
        run: |
          export MLFLOW_TRACKING_URI=http://mlflow-server:5000

      - name: Train model
        run: |
          python src/train.py \
            --config configs/model_config.yaml \
            --experiment-name ${{ github.ref_name }}

      - name: Model validation tests
        run: |
          pytest tests/model/ -v \
            --model-path models/latest

      - name: Performance check
        run: |
          python scripts/check_performance.py \
            --threshold 0.85

  # 4. 构建与部署
  build-and-deploy:
    runs-on: ubuntu-latest
    needs: train-and-validate
    if: github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v3

      - name: Build Docker image
        run: |
          docker build -t ml-model:${{ github.sha }} .
          docker tag ml-model:${{ github.sha }} ml-model:latest

      - name: Push to registry
        run: |
          echo ${{ secrets.DOCKER_PASSWORD }} | docker login -u ${{ secrets.DOCKER_USERNAME }} --password-stdin
          docker push ml-model:${{ github.sha }}

      - name: Deploy to staging
        run: |
          kubectl set image deployment/model-serving \
            model=ml-model:${{ github.sha }} \
            -n staging

      - name: Run smoke tests
        run: |
          pytest tests/integration/ -v \
            --endpoint https://staging.api.example.com

      - name: Deploy to production (canary)
        run: |
          kubectl apply -f k8s/canary-deployment.yaml
```

**Kubeflow Pipeline CI/CD**：

```python
import kfp
from kfp import dsl
from kfp.components import create_component_from_func

@create_component_from_func
def data_validation_op(data_path: str) -> str:
    """数据验证组件"""
    import great_expectations as ge

    df = ge.read_csv(data_path)
    results = df.validate(expectation_suite="suite.json")

    if not results.success:
        raise ValueError("Data validation failed!")
    return "validation_passed"

@create_component_from_func
def train_model_op(data_path: str, model_output: str) -> str:
    """模型训练组件"""
    import mlflow

    with mlflow.start_run():
        # 训练逻辑
        model.fit(...)
        mlflow.sklearn.log_model(model, "model")
        return mlflow.active_run().info.run_id

@create_component_from_func
def model_tests_op(run_id: str) -> str:
    """模型测试组件"""
    # 加载模型并运行测试
    model = mlflow.sklearn.load_model(f"runs:/{run_id}/model")

    # 公平性测试
    # 性能测试
    # 压力测试
    return "tests_passed"

@create_component_from_func
def deploy_op(run_id: str, environment: str):
    """部署组件"""
    # 部署逻辑
    pass

@dsl.pipeline(
    name='MLOps CI/CD Pipeline',
    description='End-to-end ML pipeline with CI/CD'
)
def mlops_pipeline(
    data_path: str = 'gs://bucket/data',
    environment: str = 'staging'
):
    # 数据验证
    validation = data_validation_op(data_path)

    # 模型训练
    train = train_model_op(data_path, '/tmp/model')
    train.after(validation)

    # 模型测试
    test = model_tests_op(train.output)

    # 部署
    deploy = deploy_op(train.output, environment)
    deploy.after(test)

# 编译
kfp.compiler.Compiler().compile(mlops_pipeline, 'mlops_pipeline.yaml')
```

---

## 三、系统对比

### 3.1 MLOps工具对比

| 工具 | 类型 | 实验追踪 | 模型注册 | 数据版本 | 部署 | 监控 |
|------|------|----------|----------|----------|------|------|
| **MLflow** | 开源 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| **DVC** | 开源 | ⭐⭐ | ⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐ |
| **Kubeflow** | 开源 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **Weights & Biases** | SaaS | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| **Azure ML** | 云 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| **SageMaker** | 云 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

### 3.2 性能基准

| 指标 | 手动流程 | 基础MLOps | 高级MLOps |
|------|----------|-----------|-----------|
| **部署频率** | 周/月 | 天 | 小时/实时 |
| **实验追踪** | 手动记录 | 自动记录 | 自动+智能分析 |
| **模型回滚时间** | 小时 | 分钟 | 秒级 |
| **漂移检测** | 无 | 日级 | 实时 |
| **团队效率** | 基准 | 2-3x | 5-10x |

### 3.3 选型决策树

```
MLOps工具选型
├── 云服务提供商？
│   ├── AWS ──► SageMaker
│   ├── Azure ──► Azure ML
│   ├── GCP ──► Vertex AI
│   └── 多云 ──► 开源方案
├── 团队规模？
│   ├── 小团队(<5) ──► MLflow + DVC
│   ├── 中团队(5-20) ──► MLflow + Kubeflow
│   └── 大团队(>20) ──► 企业级平台
├── 实时性要求？
│   ├── 实时在线学习 ──► 流式MLOps方案
│   └── 批处理为主 ──► 标准MLOps方案
└── 预算？
    ├── 有限 ──► 开源方案
    └── 充足 ──► 商业方案/SaaS
```

---

## 四、实践指南

### 4.1 部署配置

**MLflow Tracking Server**：

```yaml
# docker-compose.mlflow.yml
version: '3.8'
services:
  mlflow:
    image: mlflow/mlflow:latest
    ports:
      - "5000:5000"
    environment:
      - MLFLOW_TRACKING_URI=sqlite:///mlflow.db
      - MLFLOW_DEFAULT_ARTIFACT_ROOT=s3://mlflow-artifacts
      - AWS_ACCESS_KEY_ID=${AWS_ACCESS_KEY_ID}
      - AWS_SECRET_ACCESS_KEY=${AWS_SECRET_ACCESS_KEY}
    command: >
      mlflow server
      --backend-store-uri sqlite:///mlflow.db
      --default-artifact-root s3://mlflow-artifacts
      --host 0.0.0.0
      --port 5000

  postgres:
    image: postgres:13
    environment:
      POSTGRES_USER: mlflow
      POSTGRES_PASSWORD: mlflow
      POSTGRES_DB: mlflow
    volumes:
      - postgres_data:/var/lib/postgresql/data

  minio:
    image: minio/minio
    ports:
      - "9000:9000"
      - "9001:9001"
    environment:
      MINIO_ROOT_USER: minio
      MINIO_ROOT_PASSWORD: minio123
    command: server /data --console-address ":9001"
    volumes:
      - minio_data:/data

volumes:
  postgres_data:
  minio_data:
```

### 4.2 最佳实践

1. **版本控制策略**

   ```bash
   # Git分支策略
   main        # 生产分支
   ├── develop # 开发分支
   ├── feature/data-pipeline
   ├── feature/model-architecture
   └── hotfix/critical-bug

   # DVC数据版本
   data/
   ├── raw.dvc           # 原始数据
   ├── processed.dvc     # 处理后数据
   └── features.dvc      # 特征数据
   ```

2. **实验管理规范**

   ```python
   # 命名规范: <project>/<experiment>/<run_name>
   mlflow.set_experiment("fraud_detection/xgboost")

   with mlflow.start_run(run_name="v1.2.0-feature-engineering"):
       mlflow.set_tag("version", "1.2.0")
       mlflow.set_tag("author", "data-scientist-a")
       mlflow.set_tag("stage", "development")
   ```

3. **模型测试金字塔**

   ```
       /\
      /  \
     / E2E\      # 端到端测试
    /──────\
   /Integration\  # 集成测试

  /────────────\
 /   Unit Test  \ # 单元测试（数据、模型）
/────────────────\

   ```

4. **监控告警配置**
   ```yaml
   # 告警规则
   alerts:
     - name: data_drift
       condition: psi > 0.2
       severity: warning
       channels: [slack, email]

     - name: performance_degradation
       condition: accuracy < 0.85
       severity: critical
       channels: [pagerduty, slack]

     - name: prediction_latency
       condition: p99_latency > 100ms
       severity: warning
       channels: [slack]
   ```

### 4.3 常见问题

**Q1: 实验难以复现？**
A:

- 使用DVC锁定数据版本
- 记录完整的随机种子
- 容器化执行环境
- 保存完整的依赖列表

**Q2: 模型版本混乱？**
A:

- 使用语义化版本（SemVer）
- 建立模型生命周期流程
- 限制同时运行的版本数
- 定期归档旧版本

**Q3: 漂移检测误报？**
A:

- 调整漂移阈值
- 使用滑动窗口而非固定参考
- 排除季节性因素
- 多指标综合判断

**Q4: CI/CD流水线慢？**
A:

- 并行化独立任务
- 缓存依赖和数据
- 增量训练而非全量
- 使用轻量级测试筛选

---

## 五、形式化分析

### 5.1 模型性能边界

**正确性保证**：

```
定义:
- 训练数据分布: P_train(X, Y)
- 测试数据分布: P_test(X, Y)
- 部署数据分布: P_deploy(X, Y)

泛化误差: R(f) = E_{(x,y)~P}[L(f(x), y)]

分布偏移类型:
1. 协变量偏移: P_train(X) ≠ P_deploy(X), P(Y|X)相同
2. 概念漂移: P(Y|X)变化
3. 标签偏移: P_train(Y) ≠ P_deploy(Y)

监控目标: 检测 P_train ≠ P_deploy
```

### 5.2 CI/CD可靠性

**部署正确性**：

```
部署流程 D: Model × Config → Service

正确性条件:
1. 功能正确: ∀x, D(M, C)(x) = M(x)
2. 性能保证: Latency(D(M, C)) < SLA
3. 回滚安全: Rollback ∘ Deploy = Identity
```

---

## 六、与其他主题的关联

### 6.1 上游依赖

- [Kubeflow](./Kubeflow.md) - ML平台
- [特征平台](./特征平台.md) - 特征管理
- [模型服务与推理优化](./模型服务与推理优化.md) - 部署环节

### 6.2 下游应用

- [监控告警](../07-observability/monitoring.md)

### 6.3 相关概念

| 概念 | 关系 | 说明 |
|------|------|------|
| DevOps | 基础 | 方法论来源 |
| DataOps | 并行 | 数据管道自动化 |
| GitOps | 扩展 | K8s部署模式 |

---

## 七、参考资源

### 7.1 官方文档

1. [MLflow文档](https://mlflow.org/docs/latest/index.html)
2. [DVC文档](https://dvc.org/doc)
3. [Kubeflow文档](https://www.kubeflow.org/docs/)
4. [Evidently AI](https://docs.evidentlyai.com/)

### 7.2 学术论文

1. [Machine Learning: The High Interest Credit Card of Technical Debt](https://research.google/pubs/pub43146/) - Google, 2014
2. [Hidden Technical Debt in Machine Learning Systems](https://papers.nips.cc/paper/2015/hash/86df7dcfd896fcaf2674f757a2463eba-Abstract.html) - NIPS 2015

### 7.3 学习资料

1. [MLOps Specialization (DeepLearning.AI)](https://www.coursera.org/specializations/machine-learning-engineering-for-production-mlops)
2. [Made With ML](https://madewithml.com/) - 实践课程
3. [MLOps Community](https://mlops.community/) - 社区资源

### 7.4 相关文档

- [Kubeflow](./Kubeflow.md) - ML平台实践
- [特征平台](./特征平台.md) - 特征管理
- [模型服务与推理优化](./模型服务与推理优化.md) - 部署环节

---

**维护者**：项目团队
**最后更新**：2026年
