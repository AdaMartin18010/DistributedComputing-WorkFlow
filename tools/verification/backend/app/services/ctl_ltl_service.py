"""
CTL/LTL验证服务
"""

from typing import Optional, Dict
from app.api.ctl_ltl import CTLLTLVerifyResponse
from app.engines.ctl_ltl_engine import CTLLTLEngine


class CTLLTLService:
    """CTL/LTL验证服务类"""
    
    def __init__(self):
        """初始化服务"""
        self.engine = CTLLTLEngine()
    
    async def verify(
        self,
        model: str,
        formula: str,
        logic_type: str,
        tool: str = "nusmv"
    ) -> CTLLTLVerifyResponse:
        """
        验证CTL/LTL公式
        
        Args:
            model: 模型代码
            formula: CTL/LTL公式
            logic_type: 逻辑类型（CTL或LTL）
            tool: 使用的工具（nusmv或spin）
        
        Returns:
            CTLLTLVerifyResponse对象
        """
        # 调用验证引擎
        result = self.engine.verify(model, formula, logic_type, tool)
        
        return CTLLTLVerifyResponse(
            status=result["status"],
            result=result.get("result"),
            error=result.get("error"),
            counter_example=result.get("counter_example")
        )
