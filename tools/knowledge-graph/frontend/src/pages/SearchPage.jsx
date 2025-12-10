import React, { useState } from 'react'
import { Card, Input, Button, List, Tag, message } from 'antd'
import { SearchOutlined } from '@ant-design/icons'
import { searchApi } from '../services/api'

function SearchPage() {
  const [query, setQuery] = useState('')
  const [loading, setLoading] = useState(false)
  const [results, setResults] = useState([])
  const [total, setTotal] = useState(0)

  const handleSearch = async () => {
    if (!query.trim()) {
      message.warning('请输入搜索关键词')
      return
    }

    try {
      setLoading(true)
      const data = await searchApi.search({ q: query, page: 1, page_size: 20 })
      setResults(data.results)
      setTotal(data.total)
    } catch (error) {
      message.error('搜索失败: ' + error.message)
    } finally {
      setLoading(false)
    }
  }

  return (
    <Card title="知识图谱搜索">
      <div style={{ marginBottom: '24px' }}>
        <Input
          size="large"
          placeholder="输入搜索关键词..."
          value={query}
          onChange={e => setQuery(e.target.value)}
          onPressEnter={handleSearch}
          suffix={
            <Button
              type="primary"
              icon={<SearchOutlined />}
              onClick={handleSearch}
              loading={loading}
            >
              搜索
            </Button>
          }
        />
      </div>

      {total > 0 && (
        <div style={{ marginBottom: '16px', color: '#666' }}>
          找到 {total} 个结果
        </div>
      )}

      <List
        loading={loading}
        dataSource={results}
        renderItem={item => (
          <List.Item>
            <List.Item.Meta
              title={
                <div>
                  <span style={{ fontSize: '16px', fontWeight: 'bold' }}>
                    {item.label}
                  </span>
                  <Tag color="blue" style={{ marginLeft: '8px' }}>
                    {item.type}
                  </Tag>
                  <span style={{ marginLeft: '8px', color: '#999' }}>
                    相似度: {(item.score * 100).toFixed(2)}%
                  </span>
                </div>
              }
              description={
                <div>
                  <div style={{ marginTop: '8px' }}>
                    {Object.entries(item.properties).map(([key, value]) => (
                      <div key={key} style={{ marginBottom: '4px' }}>
                        <strong>{key}:</strong> {String(value)}
                      </div>
                    ))}
                  </div>
                </div>
              }
            />
          </List.Item>
        )}
      />
    </Card>
  )
}

export default SearchPage
