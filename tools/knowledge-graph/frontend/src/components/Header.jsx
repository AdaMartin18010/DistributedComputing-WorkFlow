import React from 'react'
import { Layout, Menu } from 'antd'
import { useNavigate, useLocation } from 'react-router-dom'
import { HomeOutlined, SearchOutlined } from '@ant-design/icons'

const { Header: AntHeader } = Layout

function Header() {
  const navigate = useNavigate()
  const location = useLocation()

  const menuItems = [
    {
      key: '/',
      icon: <HomeOutlined />,
      label: '知识图谱',
    },
    {
      key: '/search',
      icon: <SearchOutlined />,
      label: '搜索',
    },
  ]

  return (
    <AntHeader style={{ background: '#fff', padding: '0 24px' }}>
      <div style={{ display: 'flex', alignItems: 'center', height: '100%' }}>
        <div style={{ fontSize: '20px', fontWeight: 'bold', marginRight: '40px' }}>
          知识图谱可视化工具
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
