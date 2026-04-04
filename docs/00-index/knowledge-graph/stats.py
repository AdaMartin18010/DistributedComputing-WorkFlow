#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
知识图谱统计分析脚本

生成知识图谱的详细统计报告，包括实体数量、关系数量、分类分布等。

使用方法:
    python stats.py -i core-concepts.ttl [-o report.json] [-v]
"""

import re
import json
import argparse
from pathlib import Path
from collections import defaultdict, Counter
from typing import Dict, List, Set, Tuple
from dataclasses import dataclass, asdict


@dataclass
class GraphStats:
    """知识图谱统计信息"""
    total_entities: int = 0
    total_relationships: int = 0
    unique_predicates: int = 0
    
    # 按类型统计
    entity_types: Dict[str, int] = None
    
    # 按类别统计
    categories: Dict[str, int] = None
    
    # 关系统计
    predicate_counts: Dict[str, int] = None
    
    # 难度分布
    difficulty_distribution: Dict[str, int] = None
    
    # 时间分布
    year_distribution: Dict[int, int] = None
    
    # 语言分布
    language_distribution: Dict[str, int] = None
    
    # 连通性统计
    connected_components: int = 0
    isolated_entities: int = 0
    avg_degree: float = 0.0
    max_degree: int = 0
    
    # 覆盖范围
    coverage_areas: List[str] = None
    
    def __post_init__(self):
        if self.entity_types is None:
            self.entity_types = {}
        if self.categories is None:
            self.categories = {}
        if self.predicate_counts is None:
            self.predicate_counts = {}
        if self.difficulty_distribution is None:
            self.difficulty_distribution = {}
        if self.year_distribution is None:
            self.year_distribution = {}
        if self.language_distribution is None:
            self.language_distribution = {}
        if self.coverage_areas is None:
            self.coverage_areas = []


class TurtleStatsParser:
    """Turtle RDF 文件统计解析器"""
    
    # 正则表达式模式
    TYPE_PATTERN = re.compile(r'(\S+)\s+rdf:type\s+([^;]+)')
    PREDICATE_PATTERN = re.compile(r'(\S+)\s+(:\w+|a)\s+([^;\.]+)')
    STRING_LITERAL_PATTERN = re.compile(r'"([^"]*)"(?:@(\w+))?')
    INTEGER_PATTERN = re.compile(r'"(\d+)"\^\^xsd:integer')
    URI_PATTERN = re.compile(r'<([^>]+)>|(\S+:\S+)')
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.entities: Dict[str, Dict] = {}
        self.triples: List[Tuple[str, str, str]] = []
        self.predicates: Set[str] = set()
        
    def log(self, message: str):
        """输出日志"""
        if self.verbose:
            print(f"[INFO] {message}")
    
    def parse(self, filepath: Path) -> GraphStats:
        """解析 Turtle 文件并生成统计"""
        self.log(f"解析文件: {filepath}")
        
        content = filepath.read_text(encoding='utf-8')
        
        # 提取所有三元组
        self._extract_triples(content)
        
        # 构建实体信息
        self._build_entities()
        
        # 生成统计
        return self._generate_stats()
    
    def _extract_triples(self, content: str):
        """提取三元组"""
        # 移除注释
        content = re.sub(r'#.*$', '', content, flags=re.MULTILINE)
        
        # 分割语句
        # 简化的解析：按句号分割，然后处理每个语句块
        statements = re.split(r'\s*\.\s*', content)
        
        for stmt in statements:
            stmt = stmt.strip()
            if not stmt or stmt.startswith('@prefix'):
                continue
            
            # 提取主语
            lines = stmt.split('\n')
            if not lines:
                continue
            
            first_line = lines[0].strip()
            subject_match = re.match(r'^(\S+)', first_line)
            if not subject_match:
                continue
            
            subject = subject_match.group(1)
            
            # 提取谓语-宾语对
            # 替换换行符为空格以便匹配
            flat_stmt = ' '.join(line.strip() for line in lines)
            
            # 查找所有谓语-宾语
            # 模式: 谓语 宾语 [; 谓语 宾语]*
            pred_obj_pattern = re.findall(r'(:\w+|rdf:type)\s+([^;]+)', flat_stmt)
            
            for pred, obj in pred_obj_pattern:
                obj = obj.strip()
                # 清理对象值
                obj = re.sub(r'\s+', ' ', obj)
                
                self.triples.append((subject, pred, obj))
                self.predicates.add(pred)
                
                if pred == 'a' or pred == 'rdf:type':
                    self._add_entity_type(subject, obj)
                else:
                    self._add_entity_property(subject, pred, obj)
    
    def _add_entity_type(self, subject: str, obj: str):
        """添加实体类型"""
        if subject not in self.entities:
            self.entities[subject] = {'types': [], 'properties': {}}
        
        types = [t.strip() for t in obj.split(',')]
        self.entities[subject]['types'].extend(types)
    
    def _add_entity_property(self, subject: str, pred: str, obj: str):
        """添加实体属性"""
        if subject not in self.entities:
            self.entities[subject] = {'types': [], 'properties': {}}
        
        if pred not in self.entities[subject]['properties']:
            self.entities[subject]['properties'][pred] = []
        
        self.entities[subject]['properties'][pred].append(obj)
    
    def _build_entities(self):
        """构建完整实体信息"""
        self.log(f"构建 {len(self.entities)} 个实体")
        
        # 清理和规范化
        for uri, entity in self.entities.items():
            # 去重类型
            entity['types'] = list(set(t.strip() for t in entity['types']))
    
    def _generate_stats(self) -> GraphStats:
        """生成统计信息"""
        stats = GraphStats()
        
        # 基本计数
        stats.total_entities = len(self.entities)
        stats.total_relationships = len(self.triples)
        stats.unique_predicates = len(self.predicates)
        
        # 实体类型统计
        type_counter = Counter()
        category_counter = Counter()
        difficulty_counter = Counter()
        year_counter = Counter()
        lang_counter = Counter()
        
        for uri, entity in self.entities.items():
            # 类型
            for t in entity['types']:
                type_counter[t] += 1
            
            props = entity['properties']
            
            # 类别
            if ':category' in props:
                for cat in props[':category']:
                    cat_clean = cat.strip().replace(':', '')
                    category_counter[cat_clean] += 1
            
            # 难度
            if ':difficulty' in props:
                for diff in props[':difficulty']:
                    # 提取语言标签前的值
                    diff_val = re.sub(r'@\w+$', '', diff).strip('"')
                    difficulty_counter[diff_val] += 1
            
            # 年份
            if ':hasYear' in props or ':created' in props:
                year_prop = props.get(':hasYear', props.get(':created', []))
                for year_str in year_prop:
                    year_match = re.search(r'(\d{4})', year_str)
                    if year_match:
                        year_counter[int(year_match.group(1))] += 1
            
            # 语言
            for prop_values in props.values():
                for val in prop_values:
                    lang_match = re.search(r'@(\w+)$', val)
                    if lang_match:
                        lang_counter[lang_match.group(1)] += 1
        
        stats.entity_types = dict(type_counter)
        stats.categories = dict(category_counter)
        stats.difficulty_distribution = dict(difficulty_counter)
        stats.year_distribution = dict(sorted(year_counter.items()))
        stats.language_distribution = dict(lang_counter)
        
        # 谓词统计
        pred_counter = Counter()
        for _, pred, _ in self.triples:
            pred_counter[pred] += 1
        stats.predicate_counts = dict(pred_counter)
        
        # 连通性统计
        stats = self._calculate_connectivity(stats)
        
        # 覆盖范围
        stats.coverage_areas = self._identify_coverage_areas()
        
        return stats
    
    def _calculate_connectivity(self, stats: GraphStats) -> GraphStats:
        """计算连通性统计"""
        # 构建邻接表
        adjacency = defaultdict(set)
        
        for subj, pred, obj in self.triples:
            # 只考虑对象关系（非字面量）
            if obj.startswith(':') or obj.startswith('sys:') or obj.startswith('person:'):
                adjacency[subj].add(obj)
                adjacency[obj].add(subj)
        
        # 计算度数
        degrees = [len(neighbors) for neighbors in adjacency.values()]
        
        if degrees:
            stats.avg_degree = sum(degrees) / len(degrees)
            stats.max_degree = max(degrees)
        
        # 查找孤立实体
        all_subjects = set(s for s, _, _ in self.triples)
        all_objects = set(o for _, _, o in self.triples if o.startswith(':'))
        all_entities = all_subjects | all_objects
        
        connected_entities = set(adjacency.keys())
        stats.isolated_entities = len(all_entities - connected_entities)
        
        # 计算连通分量（简化版）
        visited = set()
        components = 0
        
        for entity in all_entities:
            if entity not in visited and entity in adjacency:
                components += 1
                self._dfs(entity, adjacency, visited)
        
        stats.connected_components = components
        
        return stats
    
    def _dfs(self, node: str, adjacency: Dict, visited: Set):
        """深度优先搜索"""
        visited.add(node)
        for neighbor in adjacency.get(node, []):
            if neighbor not in visited:
                self._dfs(neighbor, adjacency, visited)
    
    def _identify_coverage_areas(self) -> List[str]:
        """识别知识图谱覆盖的领域"""
        areas = set()
        
        # 根据实体类型识别领域
        for uri, entity in self.entities.items():
            types = [t.lower() for t in entity['types']]
            
            if any('consensus' in t or 'algorithm' in t for t in types):
                areas.add('共识算法')
            if any('system' in t or 'database' in t for t in types):
                areas.add('存储系统')
            if any('protocol' in t for t in types):
                areas.add('通信协议')
            if any('pattern' in t for t in types):
                areas.add('设计模式')
            if 'theorem' in str(types):
                areas.add('理论基础')
            if any('paper' in t for t in types):
                areas.add('学术论文')
            if any('person' in t for t in types):
                areas.add('关键人物')
        
        return sorted(list(areas))


def print_report(stats: GraphStats):
    """打印统计报告"""
    print("\n" + "=" * 60)
    print("          分布式计算知识图谱统计报告")
    print("=" * 60)
    
    print(f"\n【基本信息】")
    print(f"  实体总数:          {stats.total_entities}")
    print(f"  关系总数:          {stats.total_relationships}")
    print(f"  唯一谓词:          {stats.unique_predicates}")
    
    print(f"\n【实体类型分布】")
    for t, count in sorted(stats.entity_types.items(), key=lambda x: -x[1]):
        print(f"  {t:20s}: {count:3d}")
    
    print(f"\n【分类分布】")
    for cat, count in sorted(stats.categories.items(), key=lambda x: -x[1]):
        print(f"  {cat:20s}: {count:3d}")
    
    print(f"\n【难度分布】")
    for diff, count in sorted(stats.difficulty_distribution.items()):
        bar = "█" * count
        print(f"  {diff:10s}: {count:3d} {bar}")
    
    print(f"\n【时间分布 (按年代)】")
    decades = defaultdict(int)
    for year, count in stats.year_distribution.items():
        decade = (year // 10) * 10
        decades[f"{decade}s"] += count
    for decade, count in sorted(decades.items()):
        bar = "█" * (count // 2)
        print(f"  {decade:8s}: {count:3d} {bar}")
    
    print(f"\n【语言分布】")
    for lang, count in sorted(stats.language_distribution.items(), key=lambda x: -x[1]):
        lang_name = {'zh': '中文', 'en': '英文'}.get(lang, lang)
        print(f"  {lang_name:10s}: {count:3d}")
    
    print(f"\n【连通性】")
    print(f"  连通分量:          {stats.connected_components}")
    print(f"  孤立实体:          {stats.isolated_entities}")
    print(f"  平均度数:          {stats.avg_degree:.2f}")
    print(f"  最大度数:          {stats.max_degree}")
    
    print(f"\n【覆盖领域】")
    for area in stats.coverage_areas:
        print(f"  ✓ {area}")
    
    print(f"\n【关系类型TOP10】")
    for pred, count in sorted(stats.predicate_counts.items(), 
                              key=lambda x: -x[1])[:10]:
        print(f"  {pred:20s}: {count:3d}")
    
    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(description='知识图谱统计分析')
    parser.add_argument('-i', '--input', required=True, help='输入Turtle文件')
    parser.add_argument('-o', '--output', help='输出JSON报告文件')
    parser.add_argument('-v', '--verbose', action='store_true', help='详细输出')
    
    args = parser.parse_args()
    
    input_path = Path(args.input)
    if not input_path.exists():
        print(f"[ERROR] 文件不存在: {input_path}")
        return
    
    # 解析统计
    parser_obj = TurtleStatsParser(verbose=args.verbose)
    stats = parser_obj.parse(input_path)
    
    # 打印报告
    print_report(stats)
    
    # 导出JSON
    if args.output:
        output_path = Path(args.output)
        
        # 将dataclass转换为字典
        stats_dict = asdict(stats)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(stats_dict, f, ensure_ascii=False, indent=2)
        
        print(f"\n报告已保存: {output_path}")


if __name__ == '__main__':
    main()
