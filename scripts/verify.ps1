$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$previousThreadCount = $env:LEAN_NUM_THREADS
$env:LEAN_NUM_THREADS = '2'
Push-Location -LiteralPath $projectRoot
try {
    New-Item -ItemType Directory -Path 'verification/logs' -Force | Out-Null
    & lake build *> 'verification/logs/build.log'
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath 'verification/logs/build.log' -Tail 100
        throw 'Lake build failed'
    }
    & rg -n --glob '*.lean' '\b(axiom|sorry|admit)\b' ModifiedCartan FewInflection ModifiedCartan.lean FewInflection.lean *> 'verification/logs/placeholder-scan.log'
    $scanExit = $LASTEXITCODE
    if ($scanExit -eq 0) { throw 'Prohibited source token found' }
    if ($scanExit -ne 1) { throw 'Source scan did not run successfully' }
    & lake env lean verification/AllDeclarations.lean *> 'verification/logs/all-declarations.log'
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath 'verification/logs/all-declarations.log' -Tail 80
        throw 'Dependency audit failed'
    }
    $submittedHash = (Get-FileHash -LiteralPath 'paper/submitted.tex' -Algorithm SHA256).Hash
    if ($submittedHash -ne 'D3F63ADE442557F0474EB117EDD0BA99405A09AB412E6D40FAE271C56F7C44CA') {
        throw 'The submitted manuscript differs from the fixed specification'
    }
    $submittedText = Get-Content -Raw -LiteralPath 'paper/submitted.tex'
    $submittedResults = [regex]::Matches($submittedText, '\\begin\{(thmA|thm|lem|prop|cor)\}([\s\S]*?)\\end\{\1\}')
    $submittedLabels = foreach ($result in $submittedResults) {
        [regex]::Match($result.Groups[2].Value, '\\label\{([^}]+)\}').Groups[1].Value
    }
    $completionSource = Get-Content -Raw -LiteralPath 'verification/SubmittedCompletion.lean'
    $completionLabels = foreach ($result in [regex]::Matches($completionSource, '\("([^"]+)", ``ModifiedCartan\.Paper\.')) {
        $result.Groups[1].Value
    }
    if ($submittedLabels.Count -ne 35 -or $completionLabels.Count -ne 35 -or
        (Compare-Object $submittedLabels $completionLabels)) {
        throw 'Submitted result labels do not match the completion gate'
    }
    & lake env lean verification/SubmittedCompletion.lean *> 'verification/logs/submitted-completion.log'
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath 'verification/logs/submitted-completion.log' -Tail 100
        throw 'Submitted manuscript completion check failed'
    }
    Get-Content -LiteralPath 'verification/logs/submitted-completion.log' -TotalCount 1
    Write-Output "Submitted manuscript SHA256: $submittedHash"
    Get-Content -LiteralPath 'verification/logs/build.log' -Tail 1
    Get-Content -LiteralPath 'verification/logs/all-declarations.log'
    Write-Output 'Source scan passed for both project libraries.'
} finally {
    $env:LEAN_NUM_THREADS = $previousThreadCount
    Pop-Location
}
