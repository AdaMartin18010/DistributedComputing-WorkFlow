"""
TLA+验证引擎
"""

import subprocess
import tempfile
import os
from typing import Optional, Dict, List
from pathlib import Path
from app.config import settings


class TLAEngine:
    """TLA+验证引擎"""
    
    def __init__(self):
        """初始化引擎"""
        self.toolbox_path = settings.TLA_TOOLBOX_PATH
    
    def verify(
        self,
        model: str,
        properties: Optional[List[str]] = None,
        config: Optional[Dict] = None
    ) -> Dict:
        """
        验证TLA+模型
        
        Args:
            model: TLA+模型代码
            properties: 要验证的属性列表
            config: 验证配置
        
        Returns:
            验证结果
        """
        # 创建临时文件
        with tempfile.TemporaryDirectory() as tmpdir:
            model_file = Path(tmpdir) / "model.tla"
            cfg_file = Path(tmpdir) / "model.cfg"
            
            # 写入模型文件
            model_file.write_text(model, encoding='utf-8')
            
            # 写入配置文件
            if config:
                cfg_content = self._generate_cfg(config, properties)
            else:
                cfg_content = self._default_cfg(properties)
            cfg_file.write_text(cfg_content, encoding='utf-8')
            
            # 调用TLC进行验证
            try:
                result = self._run_tlc(model_file, cfg_file)
                return {
                    "status": "success" if result["success"] else "error",
                    "result": result.get("output"),
                    "error": result.get("error"),
                    "counter_example": result.get("counter_example")
                }
            except Exception as e:
                return {
                    "status": "error",
                    "error": str(e),
                    "result": None,
                    "counter_example": None
                }
    
    def _run_tlc(self, model_file: Path, cfg_file: Path) -> Dict:
        """运行TLC模型检验器"""
        try:
            # 构建TLC命令
            cmd = [
                "java",
                "-cp", self.toolbox_path + "/tla2tools.jar",
                "tlc2.TLC",
                "-config", str(cfg_file),
                str(model_file)
            ]
            
            # 执行命令
            process = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5分钟超时
            )
            
            # 解析输出
            output = process.stdout + process.stderr
            success = process.returncode == 0
            
            # 检查是否有反例
            counter_example = None
            if "Error" in output or "violation" in output.lower():
                counter_example = self._parse_counter_example(output)
            
            return {
                "success": success,
                "output": output,
                "error": None if success else output,
                "counter_example": counter_example
            }
        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "output": None,
                "error": "验证超时（超过5分钟）",
                "counter_example": None
            }
        except Exception as e:
            return {
                "success": False,
                "output": None,
                "error": str(e),
                "counter_example": None
            }
    
    def _parse_counter_example(self, output: str) -> Optional[Dict]:
        """解析反例"""
        # 简单的反例解析逻辑
        # 实际实现需要更复杂的解析
        lines = output.split('\n')
        counter_example = {
            "states": [],
            "error_message": output
        }
        
        # 尝试提取状态序列
        in_state = False
        current_state = {}
        for line in lines:
            if "State" in line and ":" in line:
                if current_state:
                    counter_example["states"].append(current_state)
                current_state = {"description": line.strip()}
            elif current_state and "=" in line:
                parts = line.split("=")
                if len(parts) == 2:
                    key = parts[0].strip()
                    value = parts[1].strip()
                    current_state[key] = value
        
        if current_state:
            counter_example["states"].append(current_state)
        
        return counter_example if counter_example["states"] else None
    
    def _generate_cfg(self, config: Dict, properties: Optional[List[str]]) -> str:
        """生成TLA+配置文件"""
        lines = ["SPECIFICATION Spec"]
        
        if properties:
            for prop in properties:
                lines.append(f"PROPERTY {prop}")
        
        if "constants" in config:
            lines.append("CONSTANTS")
            for key, value in config["constants"].items():
                lines.append(f"  {key} = {value}")
        
        if "init" in config:
            lines.append(f"INIT {config['init']}")
        
        if "next" in config:
            lines.append(f"NEXT {config['next']}")
        
        return "\n".join(lines)
    
    def _default_cfg(self, properties: Optional[List[str]]) -> str:
        """生成默认配置文件"""
        lines = ["SPECIFICATION Spec"]
        
        if properties:
            for prop in properties:
                lines.append(f"PROPERTY {prop}")
        
        return "\n".join(lines)
