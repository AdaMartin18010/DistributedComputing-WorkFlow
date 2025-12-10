import axios from 'axios'

const api = axios.create({
  baseURL: '/api',
  timeout: 30000,
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

// 图谱API
export const graphApi = {
  getGraph: (params) => api.get('/graph', { params }),
  getNode: (nodeId) => api.get(`/graph/nodes/${nodeId}`),
  getNeighbors: (nodeId, params) => api.get(`/graph/nodes/${nodeId}/neighbors`, { params }),
  getPath: (params) => api.get('/graph/path', { params }),
}

// 搜索API
export const searchApi = {
  search: (params) => api.get('/search', { params }),
  advancedSearch: (params) => api.get('/search/advanced', { params }),
}

// 更新API
export const updateApi = {
  createNode: (data) => api.post('/update/nodes', data),
  updateNode: (nodeId, data) => api.put(`/update/nodes/${nodeId}`, data),
  deleteNode: (nodeId) => api.delete(`/update/nodes/${nodeId}`),
  createEdge: (data) => api.post('/update/edges', data),
  deleteEdge: (edgeId) => api.delete(`/update/edges/${edgeId}`),
}

export default api
