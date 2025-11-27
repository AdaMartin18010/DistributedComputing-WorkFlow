# 最终链接检查脚本 - 忽略示例和模板中的链接
param(
    [string]$RootDir = $PWD
)

$brokenLinks = @()
$allLinks = @()
$fileCount = 0
$realBrokenLinks = @()

Write-Host "`n=== 最终链接检查（排除示例链接） ===" -ForegroundColor Cyan
Write-Host "检查目录: $RootDir`n" -ForegroundColor Gray

# 要忽略的文件模式（模板和格式规范）
$ignorePatterns = @(
    "*格式规范.md",
    "*风格指南.md",
    "*document-template.md"
)

# 递归获取所有.md文件
$mdFiles = Get-ChildItem -Path $RootDir -Filter *.md -Recurse | 
    Where-Object { 
        $_.FullName -notlike "*\archive\*" -and 
        $_.FullName -notlike "*\node_modules\*" -and
        $_.Name -notlike "*check*links*" -and
        $_.Name -notlike "*COMPLETION*" -and
        $_.Name -notlike "*LINK_FIX*"
    }

foreach ($file in $mdFiles) {
    $shouldIgnore = $false
    foreach ($pattern in $ignorePatterns) {
        if ($file.Name -like $pattern) {
            $shouldIgnore = $true
            break
        }
    }
    
    $fileCount++
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $fileDir = $file.DirectoryName
    $relativePath = $file.FullName.Replace($RootDir, '.').Replace('\', '/')
    
    # 匹配markdown链接
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
        
        # 处理锚点链接
        $anchorMatch = [regex]::Match($linkPath, '^([^#]+)(#.+)?$')
        $relativeLinkPath = $anchorMatch.Groups[1].Value
        
        if ([string]::IsNullOrWhiteSpace($relativeLinkPath)) {
            continue
        }
        
        # 检查是否是示例链接（包含占位符文本）
        $isExample = $linkPath -match '(文件路径|路径|URL|\.\.\.|示例|格式|模板)'
        
        if ($shouldIgnore -or $isExample) {
            continue  # 跳过格式规范和模板中的示例链接
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
                
                if (-not $shouldIgnore) {
                    $realBrokenLinks += [PSCustomObject]@{
                        File = $relativePath
                        LinkText = $linkText
                        LinkPath = $linkPath
                        ResolvedPath = $fullPath.Replace($RootDir, '.').Replace('\', '/')
                    }
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
            if (-not $shouldIgnore -and -not $isExample) {
                $brokenLinks += [PSCustomObject]@{
                    File = $relativePath
                    LinkText = $linkText
                    LinkPath = $linkPath
                    ResolvedPath = "路径解析错误"
                    Line = 0
                }
                $realBrokenLinks += [PSCustomObject]@{
                    File = $relativePath
                    LinkText = $linkText
                    LinkPath = $linkPath
                    ResolvedPath = "路径解析错误"
                }
            }
        }
    }
}

# 输出结果
Write-Host "检查完成！" -ForegroundColor Green
Write-Host "检查文件数: $fileCount" -ForegroundColor Cyan
Write-Host "总链接数: $($allLinks.Count)" -ForegroundColor Cyan
Write-Host "真实无效链接数: $($realBrokenLinks.Count)" -ForegroundColor $(if ($realBrokenLinks.Count -eq 0) { "Green" } else { "Yellow" })

if ($realBrokenLinks.Count -gt 0) {
    Write-Host "`n=== 真实无效链接详情 ===" -ForegroundColor Yellow
    
    $grouped = $realBrokenLinks | Group-Object File
    
    foreach ($group in $grouped) {
        Write-Host "`n文件: $($group.Name)" -ForegroundColor Cyan
        foreach ($broken in $group.Group) {
            Write-Host "  [$($broken.LinkText)]($($broken.LinkPath))" -ForegroundColor Gray
            Write-Host "    解析路径: $($broken.ResolvedPath)" -ForegroundColor DarkGray
        }
    }
    
    return $realBrokenLinks
} else {
    Write-Host "`n✓ 所有真实链接都有效！" -ForegroundColor Green
    return @()
}
