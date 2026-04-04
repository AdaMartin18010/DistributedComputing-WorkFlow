#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
从 Markdown 文档中提取 RDF 三元组
用于构建分布式计算知识图谱

使用方法:
    python extract_rdf.py [options]

选项:
    -i, --input DIR      输入目录 (默认: ../../)
    -o, --output FILE    输出文件 (默认: extracted.ttl)
    -f, --format FORMAT  输出格式: turtle, ntriples, jsonld (默认: turtle)
    -v, --verbose        详细输出
    --dry-run            试运行，不写入文件
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass, field
from collections import defaultdict

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

# RDF 前缀定义
RDF_PREFIXES = """@prefix dc: <http://purl.org/dc/elements/1.1/> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix : <http://distributedcomputing.org/ontology#> .
@prefix sys: <http://distributedcomputing.org/system#> .
@prefix person: <http://distributedcomputing.org/person#> .
@prefix paper: <http://distributedcomputing.org/paper#> .

"""

@dataclass
class Triple:
    """RDF 三元组"""
    subject: str
    predicate: str
    object: str
    is_literal: bool = False
    datatype: Optional[str] = None
    language: Optional[str] = None
    
    def to_turtle(self) -> str:
        """转换为 Turtle 格式"""
        subj = self._format_uri(self.subject)
        pred = self._format_uri(self.predicate)
        
        if self.is_literal:
            obj = self._format_literal()
        else:
            obj = self._format_uri(self.object)
        
        return f"    {subj} {pred} {obj} ."
    
    def _format_uri(self, uri: str) -> str:
        """格式化 URI"""
        if uri.startswith('http://') or uri.startswith('https://'):
            return f"<{uri}>"
        if ':' not in uri:
            return f":{uri}"
        return uri
    
    def _format_literal(self) -> str:
        """格式化字面值"""
        # 转义特殊字符
        value = self.object.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')
        
        if self.language:
            return f'"{value}"@{self.language}'
        elif self.datatype:
            return f'"{value}"^^<{self.datatype}>'
        else:
            return f'"{value}"'
    
    def to_ntriples(self) -> str:
        """转换为 N-Triples 格式"""
        # 简化的 N-Triples 输出
        return f"<{self.subject}> <{self.predicate}> {self._format_literal() if self.is_literal else f'<{self.object}>'} ."


@dataclass
class Entity:
    """知识图谱实体"""
    uri: str
    rdf_type: str
    properties: Dict[str, List] = field(default_factory=dict)
    relationships: List[Triple] = field(default_factory=list)
    
    def add_property(self, predicate: str, value, is_literal: bool = True, 
                     datatype: Optional[str] = None, language: Optional[str] = None):
        """添加属性"""
        triple = Triple(
            subject=self.uri,
            predicate=predicate,
            object=str(value),
            is_literal=is_literal,
            datatype=datatype,
            language=language
        )
        self.relationships.append(triple)
        
        if predicate not in self.properties:
            self.properties[predicate] = []
        self.properties[predicate].append(value)
    
    def add_relationship(self, predicate: str, target_uri: str):
        """添加对象关系"""
        triple = Triple(
            subject=self.uri,
            predicate=predicate,
            object=target_uri,
            is_literal=False
        )
        self.relationships.append(triple)
        
        if predicate not in self.properties:
            self.properties[predicate] = []
        self.properties[predicate].append(target_uri)


class MarkdownExtractor:
    """Markdown 文档 RDF 提取器"""
    
    # 正则表达式模式
    FRONTMATTER_PATTERN = re.compile(r'^---\s*\n(.*?)\n---\s*\n', re.DOTALL)
    HEADING_PATTERN = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)
    LINK_PATTERN = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
    CODE_BLOCK_PATTERN = re.compile(r'```[\w]*\n(.*?)```', re.DOTALL)
    TAG_PATTERN = re.compile(r'#([\w\u4e00-\u9fa5]+)')
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.entities: Dict[str, Entity] = {}
        self.statistics = defaultdict(int)
    
    def log(self, message: str):
        """输出日志"""
        if self.verbose:
            print(f"[INFO] {message}")
    
    def extract_from_file(self, filepath: Path) -> Optional[Entity]:
        """从单个 Markdown 文件提取实体"""
        self.log(f"处理文件: {filepath}")
        
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception as e:
            print(f"[ERROR] 无法读取文件 {filepath}: {e}")
            return None
        
        # 提取 Frontmatter
        frontmatter = self._extract_frontmatter(content)
        
        # 提取标题
        title = self._extract_title(content)
        if not title:
            title = filepath.stem
        
        # 确定实体类型
        entity_type = self._determine_type(filepath, frontmatter)
        
        # 生成 URI
        uri = self._generate_uri(filepath, frontmatter, title)
        
        # 创建实体
        entity = Entity(uri=uri, rdf_type=entity_type)
        
        # 添加基本属性
        entity.add_property('rdfs:label', title, language='zh')
        entity.add_property(':name', title, language='zh')
        
        # 从 Frontmatter 提取属性
        if frontmatter:
            self._extract_frontmatter_properties(entity, frontmatter)
        
        # 从内容提取属性
        self._extract_content_properties(entity, content, filepath)
        
        # 提取关系
        self._extract_relationships(entity, content, filepath)
        
        self.entities[uri] = entity
        self.statistics['files_processed'] += 1
        self.statistics[f'type_{entity_type}'] += 1
        
        return entity
    
    def _extract_frontmatter(self, content: str) -> Optional[Dict]:
        """提取 YAML Frontmatter"""
        if not HAS_YAML:
            return None
        
        match = self.FRONTMATTER_PATTERN.match(content)
        if match:
            try:
                return yaml.safe_load(match.group(1))
            except yaml.YAMLError as e:
                self.log(f"YAML 解析错误: {e}")
        return None
    
    def _extract_title(self, content: str) -> Optional[str]:
        """提取文档标题"""
        # 优先从 Frontmatter 的 title 字段
        # 然后尝试第一个 H1 标题
        match = self.HEADING_PATTERN.search(content)
        if match:
            return match.group(2).strip()
        return None
    
    def _determine_type(self, filepath: Path, frontmatter: Optional[Dict]) -> str:
        """确定实体类型"""
        if frontmatter and 'type' in frontmatter:
            return f':{frontmatter["type"]}'
        
        # 根据文件路径推断
        path_str = str(filepath).lower()
        if 'consensus' in path_str or 'algorithm' in path_str:
            return ':Algorithm'
        elif 'system' in path_str or any(x in path_str for x in ['etcd', 'kafka', 'redis']):
            return ':System'
        elif 'theorem' in path_str or '理论' in path_str:
            return ':Theorem'
        elif 'pattern' in path_str or '模式' in path_str:
            return ':Pattern'
        elif 'protocol' in path_str or '协议' in path_str:
            return ':Protocol'
        else:
            return ':Concept'
    
    def _generate_uri(self, filepath: Path, frontmatter: Optional[Dict], title: str) -> str:
        """生成实体 URI"""
        if frontmatter and 'id' in frontmatter:
            return frontmatter['id']
        
        # 从文件名生成
        safe_name = re.sub(r'[^\w\u4e00-\u9fa5]', '', title)
        return f':{safe_name}'
    
    def _extract_frontmatter_properties(self, entity: Entity, frontmatter: Dict):
        """从 Frontmatter 提取属性"""
        property_mapping = {
            'description': (':definition', 'zh'),
            'summary': (':definition', 'zh'),
            'author': (':author', None),
            'date': (':createdAt', None),
            'tags': (':tags', None),
            'difficulty': (':difficulty', 'zh'),
            'year': (':hasYear', 'xsd:integer'),
            'category': (':category', None),
            'related': (None, None),  # 特殊处理
            'implements': (None, None),  # 特殊处理
            'uses': (None, None),  # 特殊处理
        }
        
        for key, value in frontmatter.items():
            if key in property_mapping:
                pred, lang_or_type = property_mapping[key]
                
                if key == 'related' and isinstance(value, list):
                    for related in value:
                        entity.add_relationship(':relatedTo', f':{related}')
                elif key == 'implements' and isinstance(value, list):
                    for impl in value:
                        entity.add_relationship(':implements', f':{impl}')
                elif key == 'uses' and isinstance(value, list):
                    for use in value:
                        entity.add_relationship(':uses', f':{use}')
                elif pred:
                    if lang_or_type and lang_or_type.startswith('xsd:'):
                        entity.add_property(pred, value, datatype=lang_or_type)
                    elif lang_or_type:
                        entity.add_property(pred, value, language=lang_or_type)
                    else:
                        entity.add_property(pred, value)
    
    def _extract_content_properties(self, entity: Entity, content: str, filepath: Path):
        """从内容提取属性"""
        # 提取标签
        tags = self.TAG_PATTERN.findall(content)
        if tags:
            for tag in set(tags):
                entity.add_property(':tag', tag)
        
        # 提取第一个段落作为定义
        lines = content.split('\n')
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#') and not line.startswith('---'):
                if len(line) > 20:  # 假设定义至少20个字符
                    entity.add_property(':definition', line[:200], language='zh')
                    break
        
        # 从文件路径提取年份信息
        year_match = re.search(r'\b(19|20)\d{2}\b', str(filepath))
        if year_match and ':hasYear' not in entity.properties:
            entity.add_property(':hasYear', year_match.group(), datatype='xsd:integer')
    
    def _extract_relationships(self, entity: Entity, content: str, filepath: Path):
        """提取关系"""
        # 提取内部链接
        links = self.LINK_PATTERN.findall(content)
        for text, url in links:
            if url.endswith('.md') and not url.startswith('http'):
                # 内部 Markdown 链接
                related_name = Path(url).stem
                entity.add_relationship(':references', f':{related_name}')
        
        # 提取代码引用（可能表示实现关系）
        code_blocks = self.CODE_BLOCK_PATTERN.findall(content)
        for code in code_blocks:
            # 检测伪代码中的算法
            if 'algorithm' in code.lower() or 'procedure' in code.lower():
                entity.add_property(':hasPseudoCode', code[:500], language='en')
    
    def extract_from_directory(self, directory: Path, pattern: str = '**/*.md'):
        """从目录批量提取"""
        self.log(f"扫描目录: {directory}")
        
        files = list(directory.glob(pattern))
        self.log(f"找到 {len(files)} 个文件")
        
        for filepath in files:
            # 排除某些目录
            if any(x in str(filepath) for x in ['node_modules', '.git', '__pycache__', 'archive']):
                continue
            
            self.extract_from_file(filepath)
        
        return self.entities
    
    def generate_turtle(self) -> str:
        """生成 Turtle 格式输出"""
        lines = [RDF_PREFIXES]
        
        for uri, entity in sorted(self.entities.items()):
            lines.append(f"# {entity.properties.get(':name', [uri])[0]}")
            lines.append(f"{uri} rdf:type {entity.rdf_type} , owl:NamedIndividual ;")
            
            # 添加所有关系
            rel_strings = []
            for triple in entity.relationships:
                rel_strings.append(triple.to_turtle())
            
            if rel_strings:
                lines.extend(rel_strings)
            
            lines.append(".")
            lines.append("")
        
        return '\n'.join(lines)
    
    def generate_ntriples(self) -> str:
        """生成 N-Triples 格式输出"""
        lines = []
        
        for entity in self.entities.values():
            for triple in entity.relationships:
                lines.append(triple.to_ntriples())
        
        return '\n'.join(lines)
    
    def generate_jsonld(self) -> Dict:
        """生成 JSON-LD 格式输出"""
        graph = {
            "@context": {
                "dc": "http://purl.org/dc/elements/1.1/",
                "dcterms": "http://purl.org/dc/terms/",
                "": "http://distributedcomputing.org/ontology#",
                "sys": "http://distributedcomputing.org/system#",
                "person": "http://distributedcomputing.org/person#",
                "paper": "http://distributedcomputing.org/paper#"
            },
            "@graph": []
        }
        
        for uri, entity in self.entities.items():
            node = {
                "@id": uri,
                "@type": entity.rdf_type
            }
            
            for pred, values in entity.properties.items():
                key = pred.replace(':', '')
                if len(values) == 1:
                    node[key] = values[0]
                else:
                    node[key] = values
            
            graph["@graph"].append(node)
        
        return graph
    
    def get_statistics(self) -> Dict:
        """获取统计信息"""
        return dict(self.statistics)


def main():
    parser = argparse.ArgumentParser(description='从 Markdown 文档提取 RDF 三元组')
    parser.add_argument('-i', '--input', default='../../', help='输入目录')
    parser.add_argument('-o', '--output', default='extracted.ttl', help='输出文件')
    parser.add_argument('-f', '--format', default='turtle', 
                       choices=['turtle', 'ntriples', 'jsonld'],
                       help='输出格式')
    parser.add_argument('-v', '--verbose', action='store_true', help='详细输出')
    parser.add_argument('--dry-run', action='store_true', help='试运行')
    
    args = parser.parse_args()
    
    # 创建提取器
    extractor = MarkdownExtractor(verbose=args.verbose)
    
    # 处理输入目录
    input_dir = Path(args.input)
    if not input_dir.exists():
        print(f"[ERROR] 输入目录不存在: {input_dir}")
        sys.exit(1)
    
    # 提取实体
    extractor.extract_from_directory(input_dir)
    
    # 生成输出
    if args.format == 'turtle':
        output = extractor.generate_turtle()
    elif args.format == 'ntriples':
        output = extractor.generate_ntriples()
    else:  # jsonld
        output = json.dumps(extractor.generate_jsonld(), ensure_ascii=False, indent=2)
    
    # 输出结果
    if args.dry_run:
        print("[DRY RUN] 输出内容预览:")
        print(output[:2000] + "..." if len(output) > 2000 else output)
    else:
        output_path = Path(args.output)
        output_path.write_text(output, encoding='utf-8')
        print(f"[DONE] 已生成: {output_path}")
    
    # 打印统计
    stats = extractor.get_statistics()
    print("\n[统计信息]")
    for key, value in sorted(stats.items()):
        print(f"  {key}: {value}")


if __name__ == '__main__':
    main()
