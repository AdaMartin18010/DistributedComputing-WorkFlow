import React from 'react'
import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { Layout } from 'antd'
import Header from './components/Header'
import GraphViewer from './pages/GraphViewer'
import SearchPage from './pages/SearchPage'
import './App.css'

const { Content } = Layout

function App() {
  return (
    <BrowserRouter>
      <Layout style={{ minHeight: '100vh' }}>
        <Header />
        <Content style={{ padding: '24px' }}>
          <Routes>
            <Route path="/" element={<GraphViewer />} />
            <Route path="/search" element={<SearchPage />} />
          </Routes>
        </Content>
      </Layout>
    </BrowserRouter>
  )
}

export default App
