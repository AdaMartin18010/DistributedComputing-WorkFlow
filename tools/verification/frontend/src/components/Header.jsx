import React from 'react'
import { Layout, Menu } from 'antd'
import { useNavigate, useLocation } from 'react-router-dom'
import { CheckCircleOutlined, BranchesOutlined, ApartmentOutlined } from '@ant-design/icons'

const { Header: AntHeader } = Layout

function Header() {
  const navigate = useNavigate()
  const location = useLocation()

  const menuItems = [
    {
      key: '/tla',
      icon: <CheckCircleOutlined />,
      label: 'TLA+验证',
    },
    {
      key: '/ctl-ltl',
      icon: <BranchesOutlined />,
      label: 'CTL/LTL验证',
    },
    {
      key: '/petri',
      icon: <ApartmentOutlined />,
      label: 'Petri网分析',
    },
  ]

  return (
    <AntHeader style={{ background: '#fff', padding: '0 24px' }}>
      <div style={{ display: 'flex', alignItems: 'center', height: '100%' }}>
        <div style={{ fontSize: '20px', fontWeight: 'bold', marginRight: '40px' }}>
          推理方法验证工具
        </div>
        <Menu
          mode="horizontal"
          selectedKeys={[location.pathname]}
          items={menuItems}
          onClick={({ key }) => navigate(key)}
          style={{ flex: 1, borderBottom: 'none' }}
        />
      </div>
    </AntHeader>
  )
}

export default Header
