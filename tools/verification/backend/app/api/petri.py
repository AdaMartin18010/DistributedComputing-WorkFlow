"""
Petri网分析API
"""

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from typing import Optional, List

from app.services.petri_service import PetriService

router = APIRouter()
petri_service = PetriService()


class PetriAnalyzeRequest(BaseModel):
    """Petri网分析请求模型"""
    model: str
    analysis_type: str  # "reachability", "deadlock", "boundedness", "liveness"
    config: Optional[dict] = None


class PetriAnalyzeResponse(BaseModel):
    """Petri网分析响应模型"""
    status: str
    result: Optional[dict] = None
    error: Optional[str] = None


@router.post("/analyze", response_model=PetriAnalyzeResponse)
async def analyze_petri(request: PetriAnalyzeRequest):
    """
    分析Petri网
    
    - **model**: Petri网模型
    - **analysis_type**: 分析类型（reachability, deadlock, boundedness, liveness）
    - **config**: 分析配置
    """
    try:
        result = await petri_service.analyze(
            model=request.model,
            analysis_type=request.analysis_type,
            config=request.config
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
