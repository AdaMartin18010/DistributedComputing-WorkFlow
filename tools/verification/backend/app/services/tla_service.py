"""
TLA+验证服务
"""

from typing import Optional, Dict, List
from app.api.tla import TLAVerifyResponse
from app.engines.tla_engine import TLAEngine


class TLAService:
    """TLA+验证服务类"""
    
    def __init__(self):
        """初始化服务"""
        self.engine = TLAEngine()
        self.tasks = {}  # 任务存储（实际应该使用数据库或Redis）
    
    async def verify(
        self,
        model: str,
        properties: Optional[List[str]] = None,
        config: Optional[Dict] = None
    ) -> TLAVerifyResponse:
        """
        验证TLA+模型
        
        Args:
            model: TLA+模型代码
            properties: 要验证的属性列表
            config: 验证配置
        
        Returns:
            TLAVerifyResponse对象
        """
        # 调用验证引擎
        result = self.engine.verify(model, properties, config)
        
        return TLAVerifyResponse(
            status=result["status"],
            result=result.get("result"),
            error=result.get("error"),
            counter_example=result.get("counter_example")
        )
    
    async def get_status(self, task_id: str) -> Dict:
        """
        获取验证任务状态
        
        Args:
            task_id: 任务ID
        
        Returns:
            任务状态
        """
        # 从任务存储中获取状态
        task = self.tasks.get(task_id, {"status": "not_found", "progress": 0})
        return task
