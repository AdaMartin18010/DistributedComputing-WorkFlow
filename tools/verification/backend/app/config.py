"""
配置文件
"""

from pydantic_settings import BaseSettings
from typing import List


class Settings(BaseSettings):
    """应用配置"""
    
    # 应用配置
    APP_NAME: str = "推理方法验证工具"
    VERSION: str = "1.0.0"
    DEBUG: bool = True
    
    # 服务器配置
    HOST: str = "0.0.0.0"
    PORT: int = 8001
    
    # CORS配置
    CORS_ORIGINS: List[str] = [
        "http://localhost:3000",
        "http://localhost:5173",
        "http://127.0.0.1:3000",
        "http://127.0.0.1:5173"
    ]
    
    # TLA+配置
    TLA_TOOLBOX_PATH: str = "/path/to/tla-toolbox"
    
    # CTL/LTL配置
    NUSMV_PATH: str = "/usr/bin/nusmv"
    SPIN_PATH: str = "/usr/bin/spin"
    
    # Petri网配置
    CPN_TOOLS_PATH: str = "/path/to/cpn-tools"
    
    class Config:
        env_file = ".env"
        case_sensitive = True


settings = Settings()
