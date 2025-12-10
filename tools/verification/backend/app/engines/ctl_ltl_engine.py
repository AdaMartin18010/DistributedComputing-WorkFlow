"""
CTL/LTL验证引擎
"""

import subprocess
import tempfile
from typing import Optional, Dict
from pathlib import Path
from app.config import settings


class CTLLTLEngine:
    """CTL/LTL验证引擎"""
    
    def __init__(self):
        """初始化引擎"""
        self.nusmv_path = settings.NUSMV_PATH
        self.spin_path = settings.SPIN_PATH
    
    def verify(
        self,
        model: str,
        formula: str,
        logic_type: str,
        tool: str = "nusmv"
    ) -> Dict:
        """
        验证CTL/LTL公式
        
        Args:
            model: 模型代码
            formula: CTL/LTL公式
            logic_type: 逻辑类型（CTL或LTL）
            tool: 使用的工具（nusmv或spin）
        
        Returns:
            验证结果
        """
        if tool == "nusmv":
            return self._verify_with_nusmv(model, formula, logic_type)
        elif tool == "spin":
            return self._verify_with_spin(model, formula)
        else:
            return {
                "status": "error",
                "error": f"不支持的工具: {tool}",
                "result": None,
                "counter_example": None
            }
    
    def _verify_with_nusmv(self, model: str, formula: str, logic_type: str) -> Dict:
        """使用NuSMV进行验证"""
        with tempfile.TemporaryDirectory() as tmpdir:
            model_file = Path(tmpdir) / "model.smv"
            
            # 构建完整的SMV模型
            full_model = f"""{model}

-- 添加要验证的属性
LTLSPEC {formula}""" if logic_type == "LTL" else f"""{model}

-- 添加要验证的属性
CTLSPEC {formula}"""
            
            model_file.write_text(full_model, encoding='utf-8')
            
            try:
                # 运行NuSMV
                cmd = [self.nusmv_path, "-int", str(model_file)]
                process = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=300
                )
                
                output = process.stdout + process.stderr
                success = process.returncode == 0
                
                # 解析结果
                counter_example = None
                if "false" in output.lower() or "violation" in output.lower():
                    counter_example = self._parse_nusmv_counter_example(output)
                
                return {
                    "status": "success" if success and not counter_example else "error",
                    "result": {"output": output},
                    "error": None if success else output,
                    "counter_example": counter_example
                }
            except subprocess.TimeoutExpired:
                return {
                    "status": "error",
                    "error": "验证超时（超过5分钟）",
                    "result": None,
                    "counter_example": None
                }
            except Exception as e:
                return {
                    "status": "error",
                    "error": str(e),
                    "result": None,
                    "counter_example": None
                }
    
    def _verify_with_spin(self, model: str, formula: str) -> Dict:
        """使用SPIN进行验证"""
        with tempfile.TemporaryDirectory() as tmpdir:
            model_file = Path(tmpdir) / "model.pml"
            
            # 构建完整的Promela模型
            full_model = f"""{model}

-- 添加要验证的LTL公式
ltl {formula}"""
            
            model_file.write_text(full_model, encoding='utf-8')
            
            try:
                # 运行SPIN
                cmd = ["spin", "-a", str(model_file)]
                process = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=300,
                    cwd=tmpdir
                )
                
                if process.returncode != 0:
                    return {
                        "status": "error",
                        "error": process.stderr,
                        "result": None,
                        "counter_example": None
                    }
                
                # 编译生成的C代码
                compile_cmd = ["gcc", "-o", "pan", "pan.c"]
                subprocess.run(compile_cmd, capture_output=True, cwd=tmpdir)
                
                # 运行验证器
                run_cmd = ["./pan"]
                process = subprocess.run(
                    run_cmd,
                    capture_output=True,
                    text=True,
                    timeout=300,
                    cwd=tmpdir
                )
                
                output = process.stdout + process.stderr
                success = "errors: 0" in output
                
                return {
                    "status": "success" if success else "error",
                    "result": {"output": output},
                    "error": None if success else output,
                    "counter_example": None
                }
            except Exception as e:
                return {
                    "status": "error",
                    "error": str(e),
                    "result": None,
                    "counter_example": None
                }
    
    def _parse_nusmv_counter_example(self, output: str) -> Optional[Dict]:
        """解析NuSMV反例"""
        lines = output.split('\n')
        counter_example = {
            "states": [],
            "error_message": output
        }
        
        in_trace = False
        current_state = {}
        for line in lines:
            if "Trace" in line or "Counterexample" in line:
                in_trace = True
            elif in_trace and "->" in line:
                if current_state:
                    counter_example["states"].append(current_state)
                current_state = {"description": line.strip()}
            elif in_trace and "=" in line:
                parts = line.split("=")
                if len(parts) == 2:
                    key = parts[0].strip()
                    value = parts[1].strip()
                    current_state[key] = value
        
        if current_state:
            counter_example["states"].append(current_state)
        
        return counter_example if counter_example["states"] else None
