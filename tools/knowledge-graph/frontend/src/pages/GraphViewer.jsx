import React, { useEffect, useRef, useState } from 'react'
import { Card, Spin, message } from 'antd'
import * as d3 from 'd3'
import { graphApi } from '../services/api'

function GraphViewer() {
  const svgRef = useRef(null)
  const [loading, setLoading] = useState(true)
  const [graph, setGraph] = useState({ nodes: [], edges: [] })

  useEffect(() => {
    loadGraph()
  }, [])

  useEffect(() => {
    if (graph.nodes.length > 0) {
      renderGraph()
    }
  }, [graph])

  const loadGraph = async () => {
    try {
      setLoading(true)
      const data = await graphApi.getGraph({ limit: 100 })
      setGraph(data)
    } catch (error) {
      message.error('加载图谱失败: ' + error.message)
    } finally {
      setLoading(false)
    }
  }

  const renderGraph = () => {
    const svg = d3.select(svgRef.current)
    svg.selectAll('*').remove()

    const width = 1200
    const height = 800

    svg.attr('width', width).attr('height', height)

    // 创建力导向图
    const simulation = d3.forceSimulation(graph.nodes)
      .force('link', d3.forceLink(graph.edges).id(d => d.id).distance(100))
      .force('charge', d3.forceManyBody().strength(-300))
      .force('center', d3.forceCenter(width / 2, height / 2))

    // 绘制边
    const link = svg.append('g')
      .selectAll('line')
      .data(graph.edges)
      .enter()
      .append('line')
      .attr('stroke', '#999')
      .attr('stroke-opacity', 0.6)
      .attr('stroke-width', 2)

    // 绘制节点
    const node = svg.append('g')
      .selectAll('circle')
      .data(graph.nodes)
      .enter()
      .append('circle')
      .attr('r', 10)
      .attr('fill', '#69b3a2')
      .call(d3.drag()
        .on('start', dragstarted)
        .on('drag', dragged)
        .on('end', dragended))

    // 添加标签
    const label = svg.append('g')
      .selectAll('text')
      .data(graph.nodes)
      .enter()
      .append('text')
      .text(d => d.label)
      .attr('font-size', 12)
      .attr('dx', 15)
      .attr('dy', 4)

    // 更新位置
    simulation.on('tick', () => {
      link
        .attr('x1', d => d.source.x)
        .attr('y1', d => d.source.y)
        .attr('x2', d => d.target.x)
        .attr('y2', d => d.target.y)

      node
        .attr('cx', d => d.x)
        .attr('cy', d => d.y)

      label
        .attr('x', d => d.x)
        .attr('y', d => d.y)
    })

    function dragstarted(event, d) {
      if (!event.active) simulation.alphaTarget(0.3).restart()
      d.fx = d.x
      d.fy = d.y
    }

    function dragged(event, d) {
      d.fx = event.x
      d.fy = event.y
    }

    function dragended(event, d) {
      if (!event.active) simulation.alphaTarget(0)
      d.fx = null
      d.fy = null
    }
  }

  return (
    <Card title="知识图谱可视化">
      <Spin spinning={loading}>
        <svg ref={svgRef} style={{ width: '100%', height: '800px', border: '1px solid #ddd' }} />
      </Spin>
    </Card>
  )
}

export default GraphViewer
