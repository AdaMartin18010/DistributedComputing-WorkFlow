# SPARQL 查询示例文档

本文档提供分布式计算知识图谱的常用 SPARQL 查询示例。

## 基础查询

### 1. 查询所有概念及其类别

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?concept ?name ?category
WHERE {
  ?concept a :Concept ;
           :name ?name ;
           :category ?category .
}
ORDER BY ?category ?name
```

### 2. 查询所有定理

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?theorem ?name ?year
WHERE {
  ?theorem a :Theorem ;
           :name ?name ;
           :hasYear ?year .
}
ORDER BY DESC(?year)
```

### 3. 查询特定概念的详细信息

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?property ?value
WHERE {
  :CAPTheorem ?property ?value .
}
```

## 算法查询

### 4. 查询所有共识算法

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?algorithm ?name ?year ?complexity
WHERE {
  ?algorithm a :Algorithm ;
             :isA :ConsensusAlgorithm ;
             :name ?name ;
             :hasYear ?year .
  OPTIONAL { ?algorithm :complexity ?complexity . }
}
ORDER BY ?year
```

### 5. 查询Raft算法的实现系统

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX sys: <http://distributedcomputing.org/system#>

SELECT ?system ?name ?language
WHERE {
  ?system a :System ;
          :implements :Raft ;
          :name ?name .
  OPTIONAL { ?system :programmingLanguage ?language . }
}
```

### 6. 查询算法的扩展关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?baseAlgorithm ?extendedAlgorithm
WHERE {
  ?extendedAlgorithm :extends ?baseAlgorithm .
  ?baseAlgorithm :name ?baseName .
  ?extendedAlgorithm :name ?extendedName .
}
ORDER BY ?baseName
```

### 7. 查询Paxos家族的所有算法

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>

SELECT ?algorithm ?name ?year
WHERE {
  ?algorithm (:extends|:isA)* :Paxos ;
             a :Algorithm ;
             :name ?name ;
             :hasYear ?year .
}
ORDER BY ?year
```

## 系统查询

### 8. 查询用Go语言编写的系统

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?system ?name ?systemType
WHERE {
  ?system a :System ;
          :name ?name ;
          :programmingLanguage "Go" .
  OPTIONAL { ?system :systemType ?systemType . }
}
ORDER BY ?name
```

### 9. 查询活跃的分布式系统

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?system ?name ?created
WHERE {
  ?system a :System ;
          :name ?name ;
          :isActive true ;
          :created ?created .
}
ORDER BY DESC(?created)
```

### 10. 查询系统使用的协议

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?system ?systemName ?protocol ?protocolName
WHERE {
  ?system a :System ;
          :name ?systemName ;
          :uses ?protocol .
  ?protocol :name ?protocolName .
}
ORDER BY ?systemName
```

### 11. 查询依赖etcd的系统

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX sys: <http://distributedcomputing.org/system#>

SELECT ?system ?name
WHERE {
  ?system a :System ;
          :name ?name ;
          :uses sys:etcd .
}
```

## 论文与人物查询

### 12. 查询引用次数最多的论文

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?paper ?title ?citations ?year
WHERE {
  ?paper a :Paper ;
         :title ?title ;
         :citations ?citations ;
         :year ?year .
}
ORDER BY DESC(?citations)
LIMIT 10
```

### 13. 查询某人提出的所有概念

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX person: <http://distributedcomputing.org/person#>

SELECT ?concept ?name ?year
WHERE {
  person:LeslieLamport :proposes ?concept .
  ?concept :name ?name .
  OPTIONAL { ?concept :hasYear ?year . }
}
ORDER BY ?year
```

### 14. 查询论文作者及其论文

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?person ?name (COUNT(?paper) AS ?paperCount)
WHERE {
  ?paper a :Paper ;
         :authoredBy ?person .
  ?person :name ?name .
}
GROUP BY ?person ?name
ORDER BY DESC(?paperCount)
```

### 15. 查询共同作者关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?person1 ?name1 ?person2 ?name2 (COUNT(?paper) AS ?collaborations)
WHERE {
  ?paper a :Paper ;
         :authoredBy ?person1, ?person2 .
  ?person1 :name ?name1 .
  ?person2 :name ?name2 .
  FILTER (?person1 != ?person2 && STR(?name1) < STR(?name2))
}
GROUP BY ?person1 ?name1 ?person2 ?name2
ORDER BY DESC(?collaborations)
```

## 关系查询

### 16. 查询与CAP定理相关的所有概念

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?concept ?name ?relationType
WHERE {
  ?concept ?relation :CAPTheorem .
  ?concept :name ?name .
  BIND(REPLACE(STR(?relation), ".*#", "") AS ?relationType)
}
ORDER BY ?relationType
```

### 17. 查询概念的传递依赖

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?concept ?dependency ?dependencyName
WHERE {
  ?concept (:dependsOn|:uses)+ ?dependency .
  ?dependency :name ?dependencyName .
}
ORDER BY ?concept
```

### 18. 查询层次关系（isA的传递闭包）

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?subConcept ?superConcept
WHERE {
  ?subConcept (:isA)+ ?superConcept .
}
ORDER BY ?superConcept ?subConcept
```

### 19. 查询概念的部分-整体关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?whole ?wholeName ?part ?partName
WHERE {
  ?whole :hasPart ?part .
  ?whole :name ?wholeName .
  ?part :name ?partName .
}
ORDER BY ?wholeName
```

## 高级查询

### 20. 查询同时实现了多种算法的系统

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?system ?name (COUNT(?algorithm) AS ?algorithmCount)
WHERE {
  ?system a :System ;
          :name ?name ;
          :implements ?algorithm .
}
GROUP BY ?system ?name
HAVING (COUNT(?algorithm) > 1)
ORDER BY DESC(?algorithmCount)
```

### 21. 查询某年的所有创新

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?innovation ?name ?type
WHERE {
  {
    ?innovation a :Algorithm ;
                :name ?name ;
                :hasYear 2014 .
    BIND("Algorithm" AS ?type)
  }
  UNION
  {
    ?innovation a :System ;
                :name ?name ;
                :created 2014 .
    BIND("System" AS ?type)
  }
  UNION
  {
    ?innovation a :Paper ;
                :title ?name ;
                :year 2014 .
    BIND("Paper" AS ?type)
  }
}
ORDER BY ?type ?name
```

### 22. 查询分布式事务相关概念

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?concept ?name ?distance
WHERE {
  ?concept (:relatedTo|:solves|:isA)* :DistributedTransaction ;
           :name ?name .
  OPTIONAL {
    ?concept :hasDifficulty ?difficulty .
    BIND(IF(?difficulty = "初级"@zh, 1, IF(?difficulty = "中级"@zh, 2, 3)) AS ?distance)
  }
}
ORDER BY ?distance
LIMIT 20
```

### 23. 查询按难度分组的算法

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?difficulty (COUNT(?algorithm) AS ?count) 
       (GROUP_CONCAT(?name; separator=", ") AS ?algorithms)
WHERE {
  ?algorithm a :Algorithm ;
             :name ?name ;
             :hasDifficulty ?difficulty .
}
GROUP BY ?difficulty
ORDER BY ?difficulty
```

### 24. 查询共识算法的演进时间线

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?algorithm ?name ?year 
       (GROUP_CONCAT(DISTINCT ?author; separator=", ") AS ?authors)
WHERE {
  ?algorithm a :Algorithm ;
             :isA :ConsensusAlgorithm ;
             :name ?name ;
             :hasYear ?year .
  OPTIONAL {
    ?algorithm :proposedBy ?person .
    ?person :name ?author .
  }
}
GROUP BY ?algorithm ?name ?year
ORDER BY ?year
```

### 25. 查询没有实现的算法

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?algorithm ?name
WHERE {
  ?algorithm a :Algorithm ;
             :name ?name .
  FILTER NOT EXISTS {
    ?system :implements ?algorithm .
  }
}
ORDER BY ?name
```

### 26. 查询活跃研究主题

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?concept ?name 
       (COUNT(DISTINCT ?paper) AS ?paperCount)
       (COUNT(DISTINCT ?system) AS ?systemCount)
WHERE {
  ?concept a :Concept ;
           :name ?name .
  OPTIONAL { ?paper :proposes ?concept . }
  OPTIONAL { ?system :implements|(:uses ?concept) . }
}
GROUP BY ?concept ?name
HAVING ((COUNT(DISTINCT ?paper) + COUNT(DISTINCT ?system)) > 2)
ORDER BY DESC(?paperCount)
```

## 推理查询

### 27. 使用属性路径查询传递关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

# 查询Raft算法的所有依赖（直接和间接）
SELECT DISTINCT ?dependency ?name
WHERE {
  :Raft (:dependsOn|:uses|:implements)+ ?dependency .
  ?dependency :name ?name .
}
ORDER BY ?name
```

### 28. 查询对称关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT ?concept1 ?name1 ?concept2 ?name2
WHERE {
  ?concept1 :relatedTo ?concept2 .
  ?concept1 :name ?name1 .
  ?concept2 :name ?name2 .
  FILTER (STR(?name1) < STR(?name2))
}
```

### 29. 查询概念的最短路径

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

# 查询从CAP定理到Raft的路径
SELECT ?intermediate ?name
WHERE {
  :CAPTheorem (:relatedTo|:hasPart|:isA)* ?intermediate .
  ?intermediate (:relatedTo|:hasPart|:isA)* :Raft .
  ?intermediate :name ?name .
}
```

### 30. 查询知识图谱统计信息

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

SELECT 
  (COUNT(DISTINCT ?theorem) AS ?theoremCount)
  (COUNT(DISTINCT ?algorithm) AS ?algorithmCount)
  (COUNT(DISTINCT ?system) AS ?systemCount)
  (COUNT(DISTINCT ?paper) AS ?paperCount)
  (COUNT(DISTINCT ?person) AS ?personCount)
  (COUNT(DISTINCT ?concept) AS ?conceptCount)
WHERE {
  { ?theorem a :Theorem . }
  { ?algorithm a :Algorithm . }
  { ?system a :System . }
  { ?paper a :Paper . }
  { ?person a :Person . }
  { ?concept a :Concept . }
}
```

## 更新查询（用于维护）

### 31. 添加新关系

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

# 示例：添加新的实现关系
INSERT DATA {
  sys:NewSystem :implements :Raft ;
                :name "NewSystem"@en .
}
```

### 32. 删除过时信息

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

# 示例：删除不再活跃的系统
DELETE WHERE {
  ?system :isActive false .
}
```

### 33. 更新引用计数

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>

# 示例：增加论文引用数
DELETE { ?paper :citations ?oldCount }
INSERT { ?paper :citations ?newCount }
WHERE {
  ?paper a :Paper ;
         :citations ?oldCount .
  BIND (?oldCount + 1 AS ?newCount)
}
```

## Federated Query（联邦查询）

### 34. 联合外部知识库

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX dbpedia: <http://dbpedia.org/resource/>
PREFIX dbo: <http://dbpedia.org/ontology/>

SELECT ?concept ?name ?abstract
WHERE {
  ?concept a :Concept ;
           :name ?name .
  SERVICE <http://dbpedia.org/sparql> {
    ?dbpResource rdfs:label ?name ;
                 dbo:abstract ?abstract .
    FILTER (LANG(?abstract) = "zh")
  }
}
```

## 查询优化建议

1. **使用适当的索引**: 为常用的查询属性（如 `:name`, `:hasYear`）创建索引
2. **限制结果数量**: 使用 `LIMIT` 避免返回过多结果
3. **选择性过滤**: 尽早使用 `FILTER` 减少中间结果
4. **避免笛卡尔积**: 谨慎使用多个可选模式
5. **使用属性路径**: 利用 `*` 和 `+` 操作符高效处理传递关系

## 常用前缀声明

```sparql
PREFIX : <http://distributedcomputing.org/ontology#>
PREFIX sys: <http://distributedcomputing.org/system#>
PREFIX person: <http://distributedcomputing.org/person#>
PREFIX paper: <http://distributedcomputing.org/paper#>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
PREFIX dc: <http://purl.org/dc/elements/1.1/>
PREFIX dcterms: <http://purl.org/dc/terms/>
```
