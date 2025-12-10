import axios from 'axios'

const api = axios.create({
  baseURL: '/api',
  timeout: 60000, // 验证可能需要较长时间
})

// 请求拦截器
api.interceptors.request.use(
  config => {
    return config
  },
  error => {
    return Promise.reject(error)
  }
)

// 响应拦截器
api.interceptors.response.use(
  response => {
    return response.data
  },
  error => {
    const message = error.response?.data?.detail || error.message || '请求失败'
    return Promise.reject(new Error(message))
  }
)

// TLA+验证API
export const tlaApi = {
  verify: (data) => api.post('/tla/verify', data),
  getStatus: (taskId) => api.get(`/tla/status/${taskId}`),
}

// CTL/LTL验证API
export const ctlLtlApi = {
  verify: (data) => api.post('/ctl-ltl/verify', data),
}

// Petri网分析API
export const petriApi = {
  analyze: (data) => api.post('/petri/analyze', data),
}

export default api
