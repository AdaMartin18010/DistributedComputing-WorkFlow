import React from 'react'
import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { Layout } from 'antd'
import Header from './components/Header'
import TLAVerifier from './pages/TLAVerifier'
import CTLLTLVerifier from './pages/CTLLTLVerifier'
import PetriVerifier from './pages/PetriVerifier'
import './App.css'

const { Content } = Layout

function App() {
  return (
    <BrowserRouter>
      <Layout style={{ minHeight: '100vh' }}>
        <Header />
        <Content style={{ padding: '24px' }}>
          <Routes>
            <Route path="/" element={<TLAVerifier />} />
            <Route path="/tla" element={<TLAVerifier />} />
            <Route path="/ctl-ltl" element={<CTLLTLVerifier />} />
            <Route path="/petri" element={<PetriVerifier />} />
          </Routes>
        </Content>
      </Layout>
    </BrowserRouter>
  )
}

export default App
