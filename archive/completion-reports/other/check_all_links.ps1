# 全面链接检查脚本
param(
    [switch]$Fix = $false,
    [string]$RootDir = $PWD
)

$brokenLinks = @()
$allLinks = @()
$fileCount = 0

Write-Host "`n=== 全面链接检查 ===" -ForegroundColor Cyan
Write-Host "检查目录: $RootDir`n" -ForegroundColor Gray

# 递归获取所有.md文件
$mdFiles = Get-ChildItem -Path $RootDir -Filter *.md -Recurse | 
    Where-Object { 
        $_.FullName -notlike "*\archive\*" -and 
        $_.FullName -notlike "*\node_modules\*" -and
        $_.Name -notlike "*check*links*"
    }

foreach ($file in $mdFiles) {
    $fileCount++
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $fileDir = $file.DirectoryName
    $relativePath = $file.FullName.Replace($RootDir, '.').Replace('\', '/')
    
    # 匹配markdown链接: [text](path) 或 [text](path#anchor)
    $linkPattern = '\[([^\]]+)\]\(([^\)]+)\)'
    $matches = [regex]::Matches($content, $linkPattern)
    
    foreach ($match in $matches) {
        $linkText = $match.Groups[1].Value
        $linkPath = $match.Groups[2].Value
        
        # 跳过外部链接、锚点链接、邮件链接
        if ($linkPath -match '^https?://' -or 
            $linkPath -match '^mailto:' -or 
            $linkPath -eq '#' -or 
            $linkPath -match '^#') {
            continue
        }
        
        # 处理锚点链接，只检查文件部分
        $anchorMatch = [regex]::Match($linkPath, '^([^#]+)(#.+)?$')
        $relativeLinkPath = $anchorMatch.Groups[1].Value
        
        if ([string]::IsNullOrWhiteSpace($relativeLinkPath)) {
            continue
        }
        
        # 构建完整路径
        try {
            if ($relativeLinkPath -match '^\.\.?/') {
                $fullPath = Join-Path $fileDir $relativeLinkPath
            } else {
                $fullPath = Join-Path $fileDir $relativeLinkPath
            }
            
            $fullPath = [System.IO.Path]::GetFullPath($fullPath)
            
            # 检查文件是否存在
            if (-not (Test-Path $fullPath)) {
                $brokenLinks += [PSCustomObject]@{
                    File = $relativePath
                    LinkText = $linkText
                    LinkPath = $linkPath
                    ResolvedPath = $fullPath.Replace($RootDir, '.').Replace('\', '/')
                    Line = ($content.Substring(0, $match.Index) -split "`n").Count
                }
            }
            
            $allLinks += [PSCustomObject]@{
                File = $relativePath
                LinkText = $linkText
                LinkPath = $linkPath
                Valid = (Test-Path $fullPath)
            }
        } catch {
            # 路径解析错误
            $brokenLinks += [PSCustomObject]@{
                File = $relativePath
                LinkText = $linkText
                LinkPath = $linkPath
                ResolvedPath = "路径解析错误"
                Line = 0
            }
        }
    }
}

# 输出结果
Write-Host "检查完成！" -ForegroundColor Green
Write-Host "检查文件数: $fileCount" -ForegroundColor Cyan
Write-Host "总链接数: $($allLinks.Count)" -ForegroundColor Cyan
Write-Host "无效链接数: $($brokenLinks.Count)" -ForegroundColor $(if ($brokenLinks.Count -eq 0) { "Green" } else { "Yellow" })

if ($brokenLinks.Count -gt 0) {
    Write-Host "`n=== 无效链接详情 ===" -ForegroundColor Yellow
    
    # 按文件分组
    $grouped = $brokenLinks | Group-Object File
    
    foreach ($group in $grouped) {
        Write-Host "`n文件: $($group.Name)" -ForegroundColor Cyan
        foreach ($broken in $group.Group) {
            Write-Host "  行 $($broken.Line): [$($broken.LinkText)]($($broken.LinkPath))" -ForegroundColor Gray
            Write-Host "    解析路径: $($broken.ResolvedPath)" -ForegroundColor DarkGray
        }
    }
    
    # 保存到JSON文件
    $brokenLinks | ConvertTo-Json -Depth 3 | Out-File "broken_links_detailed.json" -Encoding UTF8
    Write-Host "`n详细结果已保存到: broken_links_detailed.json" -ForegroundColor Cyan
    
    return $brokenLinks
} else {
    Write-Host "`n✓ 所有链接都有效！" -ForegroundColor Green
    return @()
}
