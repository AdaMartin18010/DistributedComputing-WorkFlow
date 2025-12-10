"""
Petri网分析引擎
"""

from typing import Dict, Optional
from xml.etree import ElementTree as ET
import tempfile
from pathlib import Path


class PetriEngine:
    """Petri网分析引擎"""
    
    def __init__(self):
        """初始化引擎"""
        pass
    
    def analyze(
        self,
        model: str,
        analysis_type: str,
        config: Optional[Dict] = None
    ) -> Dict:
        """
        分析Petri网
        
        Args:
            model: Petri网模型（PNML格式）
            analysis_type: 分析类型（reachability, deadlock, boundedness, liveness）
            config: 分析配置
        
        Returns:
            分析结果
        """
        try:
            # 解析PNML模型
            petri_net = self._parse_pnml(model)
            
            # 根据分析类型执行相应的分析
            if analysis_type == "reachability":
                result = self._analyze_reachability(petri_net, config)
            elif analysis_type == "deadlock":
                result = self._analyze_deadlock(petri_net)
            elif analysis_type == "boundedness":
                result = self._analyze_boundedness(petri_net)
            elif analysis_type == "liveness":
                result = self._analyze_liveness(petri_net)
            else:
                return {
                    "status": "error",
                    "error": f"不支持的分析类型: {analysis_type}",
                    "result": None
                }
            
            return {
                "status": "success",
                "result": result,
                "error": None
            }
        except Exception as e:
            return {
                "status": "error",
                "error": str(e),
                "result": None
            }
    
    def _parse_pnml(self, model: str) -> Dict:
        """解析PNML模型"""
        root = ET.fromstring(model)
        
        places = []
        transitions = []
        arcs = []
        
        # 解析位置（Place）
        for place in root.findall(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}place"):
            place_id = place.get("id")
            name_elem = place.find(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}text")
            name = name_elem.text if name_elem is not None else place_id
            
            marking_elem = place.find(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}text")
            marking = 0
            if marking_elem is not None:
                try:
                    marking = int(marking_elem.text)
                except:
                    marking = 0
            
            places.append({
                "id": place_id,
                "name": name,
                "marking": marking
            })
        
        # 解析转换（Transition）
        for transition in root.findall(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}transition"):
            trans_id = transition.get("id")
            name_elem = transition.find(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}text")
            name = name_elem.text if name_elem is not None else trans_id
            
            transitions.append({
                "id": trans_id,
                "name": name
            })
        
        # 解析弧（Arc）
        for arc in root.findall(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}arc"):
            arc_id = arc.get("id")
            source = arc.get("source")
            target = arc.get("target")
            
            inscription_elem = arc.find(".//{http://www.pnml.org/version-2009/grammar/pnmlcoremodel}text")
            weight = 1
            if inscription_elem is not None:
                try:
                    weight = int(inscription_elem.text)
                except:
                    weight = 1
            
            arcs.append({
                "id": arc_id,
                "source": source,
                "target": target,
                "weight": weight
            })
        
        return {
            "places": places,
            "transitions": transitions,
            "arcs": arcs
        }
    
    def _analyze_reachability(self, petri_net: Dict, config: Optional[Dict]) -> Dict:
        """可达性分析"""
        # 简化的可达性分析实现
        # 实际实现需要使用更复杂的算法（如状态空间搜索）
        
        initial_marking = {place["id"]: place["marking"] for place in petri_net["places"]}
        
        # 构建可达图（简化版本）
        reachable_states = [initial_marking]
        transitions = petri_net["transitions"]
        arcs = petri_net["arcs"]
        
        # 简单的状态空间探索
        max_states = config.get("max_states", 100) if config else 100
        explored = set()
        queue = [initial_marking]
        
        while queue and len(reachable_states) < max_states:
            current_state = queue.pop(0)
            state_key = str(sorted(current_state.items()))
            
            if state_key in explored:
                continue
            explored.add(state_key)
            
            # 尝试所有可能的转换
            for transition in transitions:
                if self._is_enabled(transition, current_state, arcs):
                    new_state = self._fire_transition(transition, current_state, arcs)
                    new_state_key = str(sorted(new_state.items()))
                    
                    if new_state_key not in explored:
                        reachable_states.append(new_state)
                        queue.append(new_state)
        
        return {
            "reachable_states_count": len(reachable_states),
            "reachable_states": reachable_states[:10],  # 只返回前10个状态
            "is_bounded": len(reachable_states) < max_states
        }
    
    def _analyze_deadlock(self, petri_net: Dict) -> Dict:
        """死锁检测"""
        # 简化的死锁检测
        # 检查是否存在无法继续执行的状态
        
        initial_marking = {place["id"]: place["marking"] for place in petri_net["places"]}
        transitions = petri_net["transitions"]
        arcs = petri_net["arcs"]
        
        # 检查初始状态
        enabled_transitions = [
            t for t in transitions
            if self._is_enabled(t, initial_marking, arcs)
        ]
        
        has_deadlock = len(enabled_transitions) == 0
        
        return {
            "has_deadlock": has_deadlock,
            "deadlock_states": [initial_marking] if has_deadlock else []
        }
    
    def _analyze_boundedness(self, petri_net: Dict) -> Dict:
        """有界性验证"""
        # 简化的有界性验证
        # 检查位置是否有界
        
        places = petri_net["places"]
        bounded = True
        max_markings = {}
        
        for place in places:
            max_markings[place["id"]] = place["marking"]
        
        # 简化的有界性检查
        # 实际实现需要更复杂的分析
        
        return {
            "is_bounded": bounded,
            "max_markings": max_markings
        }
    
    def _analyze_liveness(self, petri_net: Dict) -> Dict:
        """活性验证"""
        # 简化的活性验证
        # 检查转换是否可能无限次执行
        
        transitions = petri_net["transitions"]
        live_transitions = []
        
        for transition in transitions:
            # 简化的活性检查
            # 实际实现需要更复杂的分析
            live_transitions.append(transition["id"])
        
        return {
            "live_transitions": live_transitions,
            "all_live": len(live_transitions) == len(transitions)
        }
    
    def _is_enabled(self, transition: Dict, marking: Dict, arcs: list) -> bool:
        """检查转换是否可执行"""
        transition_id = transition["id"]
        
        # 检查所有输入弧
        for arc in arcs:
            if arc["target"] == transition_id:
                source_place = arc["source"]
                weight = arc["weight"]
                if marking.get(source_place, 0) < weight:
                    return False
        
        return True
    
    def _fire_transition(self, transition: Dict, marking: Dict, arcs: list) -> Dict:
        """执行转换"""
        new_marking = marking.copy()
        transition_id = transition["id"]
        
        # 消耗输入位置的标记
        for arc in arcs:
            if arc["target"] == transition_id:
                source_place = arc["source"]
                weight = arc["weight"]
                new_marking[source_place] = new_marking.get(source_place, 0) - weight
        
        # 产生输出位置的标记
        for arc in arcs:
            if arc["source"] == transition_id:
                target_place = arc["target"]
                weight = arc["weight"]
                new_marking[target_place] = new_marking.get(target_place, 0) + weight
        
        return new_marking
