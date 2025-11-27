# 最终链接检查脚本
$rootDir = Get-Location
$brokenLinks = @()

$mdFiles = Get-ChildItem -Path $rootDir -Filter *.md -Recurse | 
    Where-Object { 
        $_.FullName -notlike "*\archive\*" -and 
        $_.FullName -notlike "*\node_modules\*" -and
        $_.Name -notlike "*check_links*" 
    }

foreach ($file in $mdFiles) {
    $content = Get-Content $file.FullName -Raw -Encoding UTF8
    $fileDir = $file.DirectoryName
    
    # 匹配markdown链接
    $linkPattern = '\[([^\]]+)\]\(([^\)#]+)(?:#[^\)]+)?\)'
    $matches = [regex]::Matches($content, $linkPattern)
    
    foreach ($match in $matches) {
        $linkPath = $match.Groups[2].Value
        
        # 跳过外部链接和锚点链接
        if ($linkPath -match '^https?://' -or $linkPath -match '^mailto:' -or $linkPath -eq '#' -or $linkPath -match '^#') {
            continue
        }
        
        # 处理相对路径
        if ($linkPath -match '^\.\.?/') {
            $fullPath = Join-Path $fileDir $linkPath
        } else {
            $fullPath = Join-Path $fileDir $linkPath
        }
        
        $fullPath = [System.IO.Path]::GetFullPath($fullPath)
        
        # 检查文件是否存在
        if (-not (Test-Path $fullPath)) {
            $brokenLinks += [PSCustomObject]@{
                File = $file.FullName.Replace($rootDir, '.')
                LinkPath = $linkPath
                ResolvedPath = $fullPath.Replace($rootDir, '.')
            }
        }
    }
}

if ($brokenLinks.Count -gt 0) {
    Write-Host "`n发现 $($brokenLinks.Count) 个无效链接:" -ForegroundColor Yellow
    $brokenLinks | Group-Object File | ForEach-Object {
        Write-Host "`n文件: $($_.Name)" -ForegroundColor Cyan
        $_.Group | ForEach-Object {
            Write-Host "  - $($_.LinkPath)" -ForegroundColor Gray
        }
    }
    return $brokenLinks.Count
} else {
    Write-Host "`n✓ 所有链接都有效！" -ForegroundColor Green
    return 0
}

