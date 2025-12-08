"""
CTL/LTL验证API
"""

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from typing import Optional

from app.services.ctl_ltl_service import CTLLTLService

router = APIRouter()
ctl_ltl_service = CTLLTLService()


class CTLLTLVerifyRequest(BaseModel):
    """CTL/LTL验证请求模型"""
    model: str
    formula: str
    logic_type: str  # "CTL" or "LTL"
    tool: Optional[str] = "nusmv"  # "nusmv" or "spin"


class CTLLTLVerifyResponse(BaseModel):
    """CTL/LTL验证响应模型"""
    status: str
    result: Optional[dict] = None
    error: Optional[str] = None
    counter_example: Optional[dict] = None


@router.post("/verify", response_model=CTLLTLVerifyResponse)
async def verify_ctl_ltl(request: CTLLTLVerifyRequest):
    """
    验证CTL/LTL公式
    
    - **model**: 模型代码
    - **formula**: CTL/LTL公式
    - **logic_type**: 逻辑类型（CTL或LTL）
    - **tool**: 使用的工具（nusmv或spin）
    """
    try:
        result = await ctl_ltl_service.verify(
            model=request.model,
            formula=request.formula,
            logic_type=request.logic_type,
            tool=request.tool
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
