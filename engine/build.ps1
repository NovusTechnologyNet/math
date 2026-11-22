# Builds piwindow.exe into this folder.
# Needs: Rust (cargo), the NVIDIA CUDA toolkit (nvcc), Visual Studio C++ tools.
#
#   .\build.ps1                 # build
#   .\build.ps1 -SkipKernel     # reuse the existing kernel.ptx (no CUDA toolkit needed)
param(
    # Build output goes to a short path: deep folders overflow the 260-character
    # limit of the Microsoft linker.
    [string]$Target = "$env:LOCALAPPDATA\piwindow-target",
    [switch]$SkipKernel
)
$ErrorActionPreference = 'Stop'
Set-Location $PSScriptRoot

if (-not $SkipKernel) {
    # nvcc needs the Visual Studio compiler environment to preprocess the kernel.
    $vswhere = "${env:ProgramFiles(x86)}\Microsoft Visual Studio\Installer\vswhere.exe"
    $vs = & $vswhere -latest -products * -property installationPath
    $vcvars = Join-Path $vs 'VC\Auxiliary\Build\vcvars64.bat'
    if (-not (Test-Path $vcvars)) { throw "vcvars64.bat not found under $vs" }
    cmd /c "`"$vcvars`" >nul 2>&1 && nvcc -ptx -O3 kernel.cu -o kernel.ptx"
    if ($LASTEXITCODE) { throw 'nvcc failed' }
}

$env:CARGO_TARGET_DIR = $Target
cargo build --release
if ($LASTEXITCODE) { throw 'cargo build failed' }
Copy-Item (Join-Path $Target 'release\piwindow.exe') . -Force
'Built .\piwindow.exe'
