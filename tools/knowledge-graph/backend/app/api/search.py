"""
知识图谱搜索API
"""

from fastapi import APIRouter, HTTPException, Query
from typing import Optional, List
from pydantic import BaseModel

from app.services.search_service import SearchService

router = APIRouter()
search_service = SearchService()


class SearchResult(BaseModel):
    """搜索结果模型"""
    id: str
    type: str
    label: str
    score: float
    properties: dict


class SearchResponse(BaseModel):
    """搜索响应模型"""
    results: List[SearchResult]
    total: int
    page: int
    page_size: int


@router.get("/", response_model=SearchResponse)
async def search(
    q: str = Query(..., description="搜索关键词"),
    node_types: Optional[List[str]] = Query(None),
    page: int = Query(1, ge=1),
    page_size: int = Query(20, ge=1, le=100)
):
    """
    搜索知识图谱
    
    - **q**: 搜索关键词
    - **node_types**: 节点类型过滤
    - **page**: 页码
    - **page_size**: 每页数量
    """
    try:
        results = await search_service.search(
            query=q,
            node_types=node_types,
            page=page,
            page_size=page_size
        )
        return results
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/advanced")
async def advanced_search(
    query: str = Query(..., description="搜索查询（支持高级语法）"),
    filters: Optional[dict] = Query(None),
    page: int = Query(1, ge=1),
    page_size: int = Query(20, ge=1, le=100)
):
    """高级搜索"""
    try:
        results = await search_service.advanced_search(
            query=query,
            filters=filters,
            page=page,
            page_size=page_size
        )
        return results
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
