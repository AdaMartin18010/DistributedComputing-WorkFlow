"""
知识图谱服务
"""

from typing import Optional, List, Dict
from app.models.graph import Node, Edge, Graph
from app.db.neo4j_client import neo4j_client


class GraphService:
    """知识图谱服务类"""
    
    def __init__(self):
        """初始化服务"""
        self.db = neo4j_client
    
    async def get_graph(
        self,
        limit: int = 100,
        node_types: Optional[List[str]] = None,
        edge_types: Optional[List[str]] = None
    ) -> Graph:
        """
        获取知识图谱
        
        Args:
            limit: 节点数量限制
            node_types: 节点类型过滤
            edge_types: 边类型过滤
        
        Returns:
            Graph对象
        """
        # 从Neo4j获取节点和边
        nodes_data = self.db.get_nodes(limit=limit, node_types=node_types)
        edges_data = self.db.get_edges(edge_types=edge_types)
        
        # 转换为模型对象
        nodes = [
            Node(
                id=node["id"],
                type=node["type"],
                label=node["label"],
                properties=node.get("properties", {})
            )
            for node in nodes_data
        ]
        
        edges = [
            Edge(
                id=str(edge["id"]),
                source=edge["source"],
                target=edge["target"],
                type=edge["type"],
                properties=edge.get("properties", {})
            )
            for edge in edges_data
        ]
        
        return Graph(nodes=nodes, edges=edges)
    
    async def get_node(self, node_id: str) -> Optional[Node]:
        """
        获取单个节点
        
        Args:
            node_id: 节点ID
        
        Returns:
            Node对象或None
        """
        node_data = self.db.get_node(node_id)
        if not node_data:
            return None
        
        return Node(
            id=node_data["id"],
            type=node_data["type"],
            label=node_data["label"],
            properties=node_data.get("properties", {})
        )
    
    async def get_neighbors(
        self,
        node_id: str,
        depth: int = 1,
        limit: int = 50
    ) -> Graph:
        """
        获取节点的邻居节点
        
        Args:
            node_id: 节点ID
            depth: 搜索深度
            limit: 返回数量限制
        
        Returns:
            Graph对象
        """
        result = self.db.get_neighbors(node_id, depth=depth, limit=limit)
        
        nodes = [
            Node(
                id=node["id"],
                type=node["type"],
                label=node["label"],
                properties=node.get("properties", {})
            )
            for node in result["nodes"]
        ]
        
        edges = [
            Edge(
                id=str(edge["id"]),
                source=edge["source"],
                target=edge["target"],
                type=edge["type"],
                properties=edge.get("properties", {})
            )
            for edge in result["edges"]
        ]
        
        return Graph(nodes=nodes, edges=edges)
    
    async def get_path(
        self,
        source: str,
        target: str,
        max_depth: int = 5
    ) -> List[Node]:
        """
        获取两个节点之间的路径
        
        Args:
            source: 源节点ID
            target: 目标节点ID
            max_depth: 最大深度
        
        Returns:
            路径节点列表
        """
        path_ids = self.db.get_path(source, target, max_depth=max_depth)
        
        # 获取路径上的所有节点
        nodes = []
        for node_id in path_ids:
            node = await self.get_node(node_id)
            if node:
                nodes.append(node)
        
        return nodes
