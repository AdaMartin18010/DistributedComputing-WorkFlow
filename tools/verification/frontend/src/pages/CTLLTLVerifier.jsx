import React, { useState } from 'react'
import { Card, Button, message, Space, Tabs, Tag, Select } from 'antd'
import { PlayCircleOutlined, CheckCircleOutlined, CloseCircleOutlined } from '@ant-design/icons'
import Editor from '@monaco-editor/react'
import { ctlLtlApi } from '../services/api'

const { TabPane } = Tabs
const { Option } = Select

function CTLLTLVerifier() {
  const [model, setModel] = useState(`MODULE main
VAR
  x : boolean;
  y : boolean;

ASSIGN
  init(x) := FALSE;
  init(y) := FALSE;
  next(x) := !x;
  next(y) := !y;`)
  
  const [formula, setFormula] = useState('AG (x -> AF y)')
  const [logicType, setLogicType] = useState('CTL')
  const [tool, setTool] = useState('nusmv')
  const [verifying, setVerifying] = useState(false)
  const [result, setResult] = useState(null)

  const handleVerify = async () => {
    try {
      setVerifying(true)
      setResult(null)
      const data = await ctlLtlApi.verify({
        model,
        formula,
        logic_type: logicType,
        tool,
      })
      setResult(data)
      if (data.status === 'success') {
        message.success('验证成功')
      } else if (data.status === 'error') {
        message.error('验证失败: ' + data.error)
      }
    } catch (error) {
      message.error('验证失败: ' + error.message)
    } finally {
      setVerifying(false)
    }
  }

  return (
    <Card title="CTL/LTL公式验证">
      <Space direction="vertical" style={{ width: '100%' }} size="large">
        <Space>
          <Select value={logicType} onChange={setLogicType} style={{ width: 120 }}>
            <Option value="CTL">CTL</Option>
            <Option value="LTL">LTL</Option>
          </Select>
          <Select value={tool} onChange={setTool} style={{ width: 120 }}>
            <Option value="nusmv">NuSMV</Option>
            <Option value="spin">SPIN</Option>
          </Select>
          <Button
            type="primary"
            icon={<PlayCircleOutlined />}
            onClick={handleVerify}
            loading={verifying}
            size="large"
          >
            开始验证
          </Button>
        </Space>

        <Tabs defaultActiveKey="model">
          <TabPane tab="模型" key="model">
            <Editor
              height="300px"
              defaultLanguage="smv"
              value={model}
              onChange={setModel}
              theme="vs-dark"
              options={{
                minimap: { enabled: false },
                fontSize: 14,
                wordWrap: 'on',
              }}
            />
          </TabPane>
          <TabPane tab="公式" key="formula">
            <Editor
              height="300px"
              defaultLanguage="plaintext"
              value={formula}
              onChange={setFormula}
              theme="vs-dark"
              placeholder="输入CTL或LTL公式"
              options={{
                minimap: { enabled: false },
                fontSize: 14,
                wordWrap: 'on',
              }}
            />
          </TabPane>
        </Tabs>

        {result && (
          <Card title="验证结果" size="small">
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
            {result.counter_example && (
              <div style={{ marginTop: '16px' }}>
                <strong>反例:</strong>
                <pre style={{ background: '#f5f5f5', padding: '12px', borderRadius: '4px' }}>
                  {JSON.stringify(result.counter_example, null, 2)}
                </pre>
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

export default CTLLTLVerifier
