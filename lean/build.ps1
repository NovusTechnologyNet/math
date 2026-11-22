# Build the Lean library in this folder and print only errors and the final line.
#
#   .\lean\build.ps1                          # build everything (the Pilean library)
#   .\lean\build.ps1 Pilean.PiFormula.Bridge  # build one module
#
# On Windows, Mathlib's deep folders can overflow the 260-character path limit when this
# folder sits in a long path. If the environment variable PILEAN_SHORT names a short path
# that is a directory junction to this folder (made with: mklink /J C:\pilean <this folder>),
# the build runs through it.
param([string]$Module = "Pilean")
$ErrorActionPreference = 'Stop'
$proj = if ($env:PILEAN_SHORT -and (Test-Path $env:PILEAN_SHORT)) { $env:PILEAN_SHORT } else { $PSScriptRoot }
$env:Path = [Environment]::GetEnvironmentVariable('Path', 'Machine') + ';' + [Environment]::GetEnvironmentVariable('Path', 'User')

Push-Location $proj
try {
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $out = & lake build $Module 2>&1
    $code = $LASTEXITCODE
    $out | Where-Object { $_ -match 'error|warning: declaration uses .sorry.|^✖|Build completed|failed' } | Select-Object -First 80
    "exit $code after $([int]$sw.Elapsed.TotalSeconds) s"
} finally {
    Pop-Location
}
