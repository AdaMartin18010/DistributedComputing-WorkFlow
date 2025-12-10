import React, { useState } from 'react'
import { Card, Button, message, Space, Select, Tag } from 'antd'
import { PlayCircleOutlined, CheckCircleOutlined, CloseCircleOutlined } from '@ant-design/icons'
import Editor from '@monaco-editor/react'
import { petriApi } from '../services/api'

const { Option } = Select

function PetriVerifier() {
  const [model, setModel] = useState(`<?xml version="1.0" encoding="UTF-8"?>
<pnml>
  <net id="net1" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
    <place id="p1">
      <name><text>Place 1</text></name>
      <initialMarking><text>1</text></initialMarking>
    </place>
    <transition id="t1">
      <name><text>Transition 1</text></name>
    </transition>
    <arc id="a1" source="p1" target="t1">
      <inscription><text>1</text></inscription>
    </arc>
  </net>
</pnml>`)
  
  const [analysisType, setAnalysisType] = useState('reachability')
  const [analyzing, setAnalyzing] = useState(false)
  const [result, setResult] = useState(null)

  const handleAnalyze = async () => {
    try {
      setAnalyzing(true)
      setResult(null)
      const data = await petriApi.analyze({
        model,
        analysis_type: analysisType,
      })
      setResult(data)
      if (data.status === 'success') {
        message.success('分析成功')
      } else if (data.status === 'error') {
        message.error('分析失败: ' + data.error)
      }
    } catch (error) {
      message.error('分析失败: ' + error.message)
    } finally {
      setAnalyzing(false)
    }
  }

  return (
    <Card title="Petri网分析">
      <Space direction="vertical" style={{ width: '100%' }} size="large">
        <Space>
          <Select value={analysisType} onChange={setAnalysisType} style={{ width: 200 }}>
            <Option value="reachability">可达性分析</Option>
            <Option value="deadlock">死锁检测</Option>
            <Option value="boundedness">有界性验证</Option>
            <Option value="liveness">活性验证</Option>
          </Select>
          <Button
            type="primary"
            icon={<PlayCircleOutlined />}
            onClick={handleAnalyze}
            loading={analyzing}
            size="large"
          >
            开始分析
          </Button>
        </Space>

        <Editor
          height="400px"
          defaultLanguage="xml"
          value={model}
          onChange={setModel}
          theme="vs-dark"
          options={{
            minimap: { enabled: false },
            fontSize: 14,
            wordWrap: 'on',
          }}
        />

        {result && (
          <Card title="分析结果" size="small">
            <div>
              <Space>
                <Tag color={result.status === 'success' ? 'green' : result.status === 'error' ? 'red' : 'orange'}>
                  {result.status === 'success' && <CheckCircleOutlined />}
                  {result.status === 'error' && <CloseCircleOutlined />}
                  {result.status}
                </Tag>
              </Space>
            </div>
            {result.error && (
              <div style={{ marginTop: '16px', color: 'red' }}>
                <strong>错误:</strong> {result.error}
              </div>
            )}
            {result.result && (
              <div style={{ marginTop: '16px' }}>
                <strong>结果:</strong>
                <pre style={{ background: '#f5f5f5', padding: '12px', borderRadius: '4px' }}>
                  {JSON.stringify(result.result, null, 2)}
                </pre>
              </div>
            )}
          </Card>
        )}
      </Space>
    </Card>
  )
}

export default PetriVerifier
