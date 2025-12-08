"""
知识图谱更新API
"""

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
from typing import Optional, List, Dict

from app.services.update_service import UpdateService

router = APIRouter()
update_service = UpdateService()


class NodeCreate(BaseModel):
    """节点创建模型"""
    id: Optional[str] = None
    type: str
    label: str
    properties: Dict = {}


class NodeUpdate(BaseModel):
    """节点更新模型"""
    label: Optional[str] = None
    properties: Optional[Dict] = None


class EdgeCreate(BaseModel):
    """边创建模型"""
    source: str
    target: str
    type: str
    properties: Dict = {}


@router.post("/nodes")
async def create_node(node: NodeCreate):
    """创建节点"""
    try:
        result = await update_service.create_node(node)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.put("/nodes/{node_id}")
async def update_node(node_id: str, node: NodeUpdate):
    """更新节点"""
    try:
        result = await update_service.update_node(node_id, node)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.delete("/nodes/{node_id}")
async def delete_node(node_id: str):
    """删除节点"""
    try:
        result = await update_service.delete_node(node_id)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/edges")
async def create_edge(edge: EdgeCreate):
    """创建边"""
    try:
        result = await update_service.create_edge(edge)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.delete("/edges/{edge_id}")
async def delete_edge(edge_id: str):
    """删除边"""
    try:
        result = await update_service.delete_edge(edge_id)
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
