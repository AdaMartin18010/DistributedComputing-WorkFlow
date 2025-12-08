"""
推理方法验证工具 - 后端主应用
"""

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
import uvicorn

from app.api import tla, ctl_ltl, petri
from app.config import settings

app = FastAPI(
    title="推理方法验证工具 API",
    description="提供TLA+、CTL/LTL、Petri网等验证功能",
    version="1.0.0"
)

# CORS配置
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.CORS_ORIGINS,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# 注册路由
app.include_router(tla.router, prefix="/api/tla", tags=["tla"])
app.include_router(ctl_ltl.router, prefix="/api/ctl-ltl", tags=["ctl-ltl"])
app.include_router(petri.router, prefix="/api/petri", tags=["petri"])


@app.get("/")
async def root():
    """根路径"""
    return {
        "message": "推理方法验证工具 API",
        "version": "1.0.0",
        "status": "running"
    }


@app.get("/health")
async def health_check():
    """健康检查"""
    return {"status": "healthy"}


@app.exception_handler(Exception)
async def global_exception_handler(request, exc):
    """全局异常处理"""
    return JSONResponse(
        status_code=500,
        content={"message": "Internal server error", "detail": str(exc)}
    )


if __name__ == "__main__":
    uvicorn.run(
        "main:app",
        host=settings.HOST,
        port=settings.PORT,
        reload=settings.DEBUG
    )
