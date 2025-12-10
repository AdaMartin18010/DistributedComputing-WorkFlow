"""
知识图谱更新服务
"""

from typing import Dict
import uuid as uuid_module
from app.api.update import NodeCreate, NodeUpdate, EdgeCreate
from app.db.neo4j_client import neo4j_client


class UpdateService:
    """更新服务类"""
    
    def __init__(self):
        """初始化服务"""
        self.db = neo4j_client
    
    async def create_node(self, node: NodeCreate) -> Dict:
        """
        创建节点
        
        Args:
            node: 节点创建模型
        
        Returns:
            创建结果
        """
        node_id = node.id or str(uuid_module.uuid4())
        result = self.db.create_node(
            node_id=node_id,
            node_type=node.type,
            label=node.label,
            properties=node.properties
        )
        return {"id": result["id"], "status": "created", "data": result}
    
    async def update_node(self, node_id: str, node: NodeUpdate) -> Dict:
        """
        更新节点
        
        Args:
            node_id: 节点ID
            node: 节点更新模型
        
        Returns:
            更新结果
        """
        result = self.db.update_node(
            node_id=node_id,
            label=node.label,
            properties=node.properties
        )
        return {"id": node_id, "status": "updated", "data": result}
    
    async def delete_node(self, node_id: str) -> Dict:
        """
        删除节点
        
        Args:
            node_id: 节点ID
        
        Returns:
            删除结果
        """
        success = self.db.delete_node(node_id)
        return {"id": node_id, "status": "deleted" if success else "not_found"}
    
    async def create_edge(self, edge: EdgeCreate) -> Dict:
        """
        创建边
        
        Args:
            edge: 边创建模型
        
        Returns:
            创建结果
        """
        result = self.db.create_edge(
            source=edge.source,
            target=edge.target,
            edge_type=edge.type,
            properties=edge.properties
        )
        return {"id": str(result["id"]), "status": "created", "data": result}
    
    async def delete_edge(self, edge_id: str) -> Dict:
        """
        删除边
        
        Args:
            edge_id: 边ID
        
        Returns:
            删除结果
        """
        success = self.db.delete_edge(int(edge_id))
        return {"id": edge_id, "status": "deleted" if success else "not_found"}
