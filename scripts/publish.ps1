# Run in your normal PowerShell session after reviewing the project.
# This stages the project sources, commits them, and pushes main without force.
param(
    [string]$Coqc = $env:COQC
)
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $projectRoot
$expectedRemote = 'https://github.com/lokeshcha007/verified-raft-coq.git'
# The initial repository may have been created by the Codex sandbox account.
# Trust only this resolved project path, for these commands; do not alter the
# user's global safe.directory configuration.
$gitOptions = @('-c', "safe.directory=$($projectRoot.Replace('\', '/'))", '-c', 'http.sslBackend=openssl')

function Invoke-Git {
    & git @gitOptions @args
    if ($LASTEXITCODE -ne 0) {
        throw "Git failed with exit code $LASTEXITCODE. Check repository access and GitHub authentication."
    }
}

if ($Coqc) {
    & python scripts/check.py --coqc $Coqc
} else {
    & python scripts/check.py
}
if ($LASTEXITCODE -ne 0) { throw 'Formal verification failed; publication stopped.' }

if (-not (Test-Path -LiteralPath '.git')) {
    Invoke-Git init -b main
}
$branch = Invoke-Git symbolic-ref --short HEAD
if ($branch -ne 'main') {
    throw 'Expected the main branch. Switch to main explicitly before publishing.'
}
$remotes = @(Invoke-Git remote)
if ($remotes -contains 'origin') {
    $actualRemote = Invoke-Git remote get-url origin
    if ($actualRemote -ne $expectedRemote) {
        throw 'Origin differs from the requested repository; publication stopped.'
    }
} else {
    Invoke-Git remote add origin $expectedRemote
}

Invoke-Git add -- .gitattributes .gitignore .github _CoqProject Makefile README.md docs scripts theories tests
Invoke-Git diff --cached --check
& git @gitOptions diff --cached --quiet
$stagedStatus = $LASTEXITCODE
if ($stagedStatus -eq 1) {
    Invoke-Git commit -m 'Formalize simplified Raft core and prove safety invariants'
} elseif ($stagedStatus -ne 0) {
    throw 'Unable to inspect staged changes.'
}
Invoke-Git push -u origin main
Write-Output 'Verified project pushed to origin/main.'
