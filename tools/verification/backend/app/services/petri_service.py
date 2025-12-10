"""
Petri网分析服务
"""

from typing import Optional, Dict
from app.api.petri import PetriAnalyzeResponse
from app.engines.petri_engine import PetriEngine


class PetriService:
    """Petri网分析服务类"""
    
    def __init__(self):
        """初始化服务"""
        self.engine = PetriEngine()
    
    async def analyze(
        self,
        model: str,
        analysis_type: str,
        config: Optional[Dict] = None
    ) -> PetriAnalyzeResponse:
        """
        分析Petri网
        
        Args:
            model: Petri网模型
            analysis_type: 分析类型（reachability, deadlock, boundedness, liveness）
            config: 分析配置
        
        Returns:
            PetriAnalyzeResponse对象
        """
        # 调用分析引擎
        result = self.engine.analyze(model, analysis_type, config)
        
        return PetriAnalyzeResponse(
            status=result["status"],
            result=result.get("result"),
            error=result.get("error")
        )
