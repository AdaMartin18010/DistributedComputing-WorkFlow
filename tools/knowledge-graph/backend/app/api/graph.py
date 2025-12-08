"""
知识图谱查询API
"""

from fastapi import APIRouter, HTTPException, Query
from typing import Optional, List
from pydantic import BaseModel

from app.services.graph_service import GraphService

router = APIRouter()
graph_service = GraphService()


class NodeResponse(BaseModel):
    """节点响应模型"""
    id: str
    type: str
    label: str
    properties: dict


class EdgeResponse(BaseModel):
    """边响应模型"""
    id: str
    source: str
    target: str
    type: str
    properties: dict


class GraphResponse(BaseModel):
    """图谱响应模型"""
    nodes: List[NodeResponse]
    edges: List[EdgeResponse]


@router.get("/", response_model=GraphResponse)
async def get_graph(
    limit: Optional[int] = Query(100, ge=1, le=1000),
    node_types: Optional[List[str]] = Query(None),
    edge_types: Optional[List[str]] = Query(None)
):
    """
    获取知识图谱
    
    - **limit**: 返回节点数量限制
    - **node_types**: 节点类型过滤
    - **edge_types**: 边类型过滤
    """
    try:
        graph = await graph_service.get_graph(
            limit=limit,
            node_types=node_types,
            edge_types=edge_types
        )
        return graph
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/nodes/{node_id}", response_model=NodeResponse)
async def get_node(node_id: str):
    """获取单个节点"""
    try:
        node = await graph_service.get_node(node_id)
        if not node:
            raise HTTPException(status_code=404, detail="Node not found")
        return node
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/nodes/{node_id}/neighbors")
async def get_neighbors(
    node_id: str,
    depth: int = Query(1, ge=1, le=5),
    limit: int = Query(50, ge=1, le=200)
):
    """获取节点的邻居节点"""
    try:
        neighbors = await graph_service.get_neighbors(
            node_id=node_id,
            depth=depth,
            limit=limit
        )
        return neighbors
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/path")
async def get_path(
    source: str = Query(..., description="源节点ID"),
    target: str = Query(..., description="目标节点ID"),
    max_depth: int = Query(5, ge=1, le=10)
):
    """获取两个节点之间的路径"""
    try:
        path = await graph_service.get_path(
            source=source,
            target=target,
            max_depth=max_depth
        )
        return path
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
