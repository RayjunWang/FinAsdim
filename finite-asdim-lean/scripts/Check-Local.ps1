<# Optional offline check against an existing mathlib cache. The normal build
is `lake build`; this script neither installs nor changes dependencies. #>
param(
  [Parameter(Mandatory = $true)][string]$MathlibProject,
  [string]$LeanExe = 'lean',
  [string[]]$Modules = @('Theorem')
)
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$libRoot = Join-Path $projectRoot '.lake\build\lib\lean'
New-Item -ItemType Directory -Path (Join-Path $libRoot 'FiniteAsdim') -Force | Out-Null
$leanLibraries = Get-ChildItem -LiteralPath (Join-Path $MathlibProject '.lake\packages') -Directory |
  ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' }
$env:LEAN_PATH = (@($leanLibraries) + @($libRoot, $projectRoot)) -join ';'
$visited = [System.Collections.Generic.HashSet[string]]::new()
$ordered = [System.Collections.Generic.List[string]]::new()
function Visit-Module([string]$module) {
  if (-not $visited.Add($module)) { return }
  $source = Join-Path $projectRoot "FiniteAsdim\$module.lean"
  foreach ($line in Get-Content -LiteralPath $source) {
    if ($line -match '^import FiniteAsdim\.([A-Za-z0-9_]+)\s*$') {
      Visit-Module $Matches[1]
    }
  }
  $ordered.Add($module)
}
foreach ($module in $Modules) { Visit-Module $module }
Push-Location $projectRoot
try {
  foreach ($module in $ordered) {
    $source = Join-Path $projectRoot "FiniteAsdim\$module.lean"
    $output = Join-Path $libRoot "FiniteAsdim\$module.olean"
    & $LeanExe -o $output $source
    if ($LASTEXITCODE -ne 0) { throw "Lean rejected $module ($LASTEXITCODE)" }
  }
} finally { Pop-Location }
