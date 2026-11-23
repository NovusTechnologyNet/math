# Build the Lean library (package at the repository root, sources in this folder) and print
# only errors and the final line.
#
#   .\lean\build.ps1                          # build everything (Pilean and Baker)
#   .\lean\build.ps1 Pilean.PiFormula.Bridge  # build one module
param([string]$Module = "")
$ErrorActionPreference = 'Stop'
$env:Path = [Environment]::GetEnvironmentVariable('Path', 'Machine') + ';' + [Environment]::GetEnvironmentVariable('Path', 'User')

Push-Location (Split-Path $PSScriptRoot -Parent)
try {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $out = if ($Module) { & lake build $Module 2>&1 } else { & lake build 2>&1 }
    $code = $LASTEXITCODE
    $out | Where-Object { $_ -match 'error|warning: declaration uses .sorry.|^✖|Build completed|failed' } | Select-Object -First 80
    "exit $code after $([int]$sw.Elapsed.TotalSeconds) s"
} finally {
    Pop-Location
}
