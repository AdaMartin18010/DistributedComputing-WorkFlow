"""
TLA+验证API
"""

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from typing import Optional

from app.services.tla_service import TLAService

router = APIRouter()
tla_service = TLAService()


class TLAVerifyRequest(BaseModel):
    """TLA+验证请求模型"""
    model: str
    properties: Optional[list] = None
    config: Optional[dict] = None


class TLAVerifyResponse(BaseModel):
    """TLA+验证响应模型"""
    status: str
    result: Optional[dict] = None
    error: Optional[str] = None
    counter_example: Optional[dict] = None


@router.post("/verify", response_model=TLAVerifyResponse)
async def verify_tla(request: TLAVerifyRequest):
    """
    验证TLA+模型
    
    - **model**: TLA+模型代码
    - **properties**: 要验证的属性列表
    - **config**: 验证配置
    """
    try:
        result = await tla_service.verify(
            model=request.model,
            properties=request.properties,
            config=request.config
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/status/{task_id}")
async def get_verification_status(task_id: str):
    """获取验证任务状态"""
    try:
        status = await tla_service.get_status(task_id)
        return status
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
