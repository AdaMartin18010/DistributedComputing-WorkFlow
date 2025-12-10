"""
Neo4j图数据库客户端
"""

from neo4j import GraphDatabase
from typing import List, Dict, Optional
from app.config import settings


class Neo4jClient:
    """Neo4j数据库客户端"""
    
    def __init__(self):
        """初始化Neo4j连接"""
        self.driver = GraphDatabase.driver(
            settings.NEO4J_URI,
            auth=(settings.NEO4J_USER, settings.NEO4J_PASSWORD)
        )
    
    def close(self):
        """关闭连接"""
        self.driver.close()
    
    def execute_query(self, query: str, parameters: Dict = None):
        """执行Cypher查询"""
        with self.driver.session() as session:
            result = session.run(query, parameters or {})
            return [record.data() for record in result]
    
    def get_nodes(
        self,
        limit: int = 100,
        node_types: Optional[List[str]] = None
    ) -> List[Dict]:
        """获取节点"""
        if node_types:
            query = """
            MATCH (n)
            WHERE n.type IN $types
            RETURN n.id as id, n.type as type, n.label as label, 
                   properties(n) as properties
            LIMIT $limit
            """
            return self.execute_query(query, {"types": node_types, "limit": limit})
        else:
            query = """
            MATCH (n)
            RETURN n.id as id, n.type as type, n.label as label,
                   properties(n) as properties
            LIMIT $limit
            """
            return self.execute_query(query, {"limit": limit})
    
    def get_edges(
        self,
        edge_types: Optional[List[str]] = None
    ) -> List[Dict]:
        """获取边"""
        if edge_types:
            query = """
            MATCH (a)-[r]->(b)
            WHERE type(r) IN $types
            RETURN id(r) as id, a.id as source, b.id as target,
                   type(r) as type, properties(r) as properties
            """
            return self.execute_query(query, {"types": edge_types})
        else:
            query = """
            MATCH (a)-[r]->(b)
            RETURN id(r) as id, a.id as source, b.id as target,
                   type(r) as type, properties(r) as properties
            """
            return self.execute_query(query)
    
    def get_node(self, node_id: str) -> Optional[Dict]:
        """获取单个节点"""
        query = """
        MATCH (n {id: $node_id})
        RETURN n.id as id, n.type as type, n.label as label,
               properties(n) as properties
        """
        results = self.execute_query(query, {"node_id": node_id})
        return results[0] if results else None
    
    def get_neighbors(
        self,
        node_id: str,
        depth: int = 1,
        limit: int = 50
    ) -> Dict:
        """获取节点的邻居节点"""
        query = f"""
        MATCH path = (start {{id: $node_id}})-[*1..{depth}]-(neighbor)
        WHERE start <> neighbor
        WITH neighbor, length(path) as distance
        ORDER BY distance
        LIMIT $limit
        RETURN neighbor.id as id, neighbor.type as type, 
               neighbor.label as label, properties(neighbor) as properties
        """
        nodes = self.execute_query(query, {"node_id": node_id, "limit": limit})
        
        # 获取边
        query_edges = f"""
        MATCH path = (start {{id: $node_id}})-[r*1..{depth}]-(neighbor)
        WHERE start <> neighbor
        WITH relationships(path) as rels
        UNWIND rels as rel
        RETURN id(rel) as id, startNode(rel).id as source,
               endNode(rel).id as target, type(rel) as type,
               properties(rel) as properties
        LIMIT $limit
        """
        edges = self.execute_query(query_edges, {"node_id": node_id, "limit": limit})
        
        return {"nodes": nodes, "edges": edges}
    
    def get_path(
        self,
        source: str,
        target: str,
        max_depth: int = 5
    ) -> List[Dict]:
        """获取两个节点之间的路径"""
        query = f"""
        MATCH path = shortestPath((start {{id: $source}})-[*1..{max_depth}]-(end {{id: $target}}))
        RETURN [node in nodes(path) | node.id] as path
        """
        results = self.execute_query(query, {"source": source, "target": target})
        return results[0]["path"] if results else []
    
    def create_node(
        self,
        node_id: str,
        node_type: str,
        label: str,
        properties: Dict = None
    ) -> Dict:
        """创建节点"""
        query = """
        CREATE (n:Node {
            id: $node_id,
            type: $node_type,
            label: $label
        })
        SET n += $properties
        RETURN n.id as id, n.type as type, n.label as label,
               properties(n) as properties
        """
        result = self.execute_query(
            query,
            {
                "node_id": node_id,
                "node_type": node_type,
                "label": label,
                "properties": properties or {}
            }
        )
        return result[0] if result else None
    
    def update_node(
        self,
        node_id: str,
        label: Optional[str] = None,
        properties: Optional[Dict] = None
    ) -> Dict:
        """更新节点"""
        updates = []
        params = {"node_id": node_id}
        
        if label:
            updates.append("n.label = $label")
            params["label"] = label
        
        if properties:
            updates.append("n += $properties")
            params["properties"] = properties
        
        if not updates:
            return self.get_node(node_id)
        
        query = f"""
        MATCH (n {{id: $node_id}})
        SET {', '.join(updates)}
        RETURN n.id as id, n.type as type, n.label as label,
               properties(n) as properties
        """
        result = self.execute_query(query, params)
        return result[0] if result else None
    
    def delete_node(self, node_id: str) -> bool:
        """删除节点（同时删除相关边）"""
        query = """
        MATCH (n {id: $node_id})
        DETACH DELETE n
        RETURN count(n) as deleted
        """
        result = self.execute_query(query, {"node_id": node_id})
        return result[0]["deleted"] > 0 if result else False
    
    def create_edge(
        self,
        source: str,
        target: str,
        edge_type: str,
        properties: Dict = None
    ) -> Dict:
        """创建边"""
        query = f"""
        MATCH (a {{id: $source}}), (b {{id: $target}})
        CREATE (a)-[r:{edge_type}]->(b)
        SET r += $properties
        RETURN id(r) as id, a.id as source, b.id as target,
               type(r) as type, properties(r) as properties
        """
        result = self.execute_query(
            query,
            {
                "source": source,
                "target": target,
                "properties": properties or {}
            }
        )
        return result[0] if result else None
    
    def delete_edge(self, edge_id: int) -> bool:
        """删除边"""
        query = """
        MATCH ()-[r]->()
        WHERE id(r) = $edge_id
        DELETE r
        RETURN count(r) as deleted
        """
        result = self.execute_query(query, {"edge_id": edge_id})
        return result[0]["deleted"] > 0 if result else False


# 全局客户端实例
neo4j_client = Neo4jClient()
