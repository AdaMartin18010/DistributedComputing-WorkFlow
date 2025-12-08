"""
搜索数据模型
"""

from pydantic import BaseModel
from typing import List, Dict


class SearchResult(BaseModel):
    """搜索结果模型"""
    id: str
    type: str
    label: str
    score: float
    properties: Dict = {}


class SearchResponse(BaseModel):
    """搜索响应模型"""
    results: List[SearchResult]
    total: int
    page: int
    page_size: int
