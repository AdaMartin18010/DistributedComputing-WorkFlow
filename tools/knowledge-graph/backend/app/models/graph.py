"""
知识图谱数据模型
"""

from pydantic import BaseModel
from typing import List, Dict, Optional


class Node(BaseModel):
    """节点模型"""
    id: str
    type: str
    label: str
    properties: Dict = {}


class Edge(BaseModel):
    """边模型"""
    id: str
    source: str
    target: str
    type: str
    properties: Dict = {}


class Graph(BaseModel):
    """图谱模型"""
    nodes: List[Node]
    edges: List[Edge]
