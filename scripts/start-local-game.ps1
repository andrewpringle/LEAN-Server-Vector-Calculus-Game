param(
  [int]$ClientPort = 3000,
  [int]$ServerPort = 8000
)

$ErrorActionPreference = 'Stop'
$gameRoot = Split-Path -Parent $PSScriptRoot
$runtimeRoot = Join-Path $gameRoot '.lake/leangame-runtime'
$runDirectory = Join-Path $gameRoot '.lake/local-game'
$gameName = [uri]::EscapeDataString((Split-Path -Leaf $gameRoot).ToLowerInvariant())
$gameUrl = "http://localhost:$ClientPort/g/local/$gameName"
$gameApi = "http://127.0.0.1:$ServerPort/api/data/local/$gameName/game"
New-Item -ItemType Directory -Force -Path $runDirectory | Out-Null

if (-not (Test-Path -LiteralPath (Join-Path $gameRoot '.lake/gamedata/game.json'))) {
  throw 'Build this game first with lake build.'
}

if (-not (Test-Path -LiteralPath (Join-Path $runtimeRoot 'package.json'))) {
  & git clone --depth 1 --branch v4.35.0 https://github.com:443/leanprover-community/lean4game.git $runtimeRoot
  if ($LASTEXITCODE -ne 0) { throw 'Could not download the matching official Lean4Game runtime.' }
}

$nodePath = (Get-Command node.exe -ErrorAction Stop).Source
$null = Get-Command lake.exe -ErrorAction Stop

if (-not (Test-Path -LiteralPath (Join-Path $runtimeRoot 'node_modules/.package-lock.json'))) {
  Push-Location $runtimeRoot
  try {
    $env:CYPRESS_INSTALL_BINARY = '0'
    & npm.cmd ci --no-audit --no-fund
    if ($LASTEXITCODE -ne 0) { throw 'Installing the locked browser runtime dependencies failed.' }
  } finally { Pop-Location }
}

# The upstream dev server expects sibling game folders. Allow an explicit local
# parent directory so its runtime can stay inside this checkout's ignored .lake.
# This changes only the downloaded runtime, not its architecture or dependencies.
$gameDataPath = Join-Path $runtimeRoot 'server/src/gameData.ts'
$runtimeSource = [IO.File]::ReadAllText($gameDataPath)
$original = "const REPO_PARENT_DIR = path.resolve(import.meta.dirname, '..', '..', '..')"
$adapted = "const REPO_PARENT_DIR = process.env.LOCAL_GAMES_DIR ?? path.resolve(import.meta.dirname, '..', '..', '..')"
if ($runtimeSource.Contains($original)) {
  [IO.File]::WriteAllText($gameDataPath, $runtimeSource.Replace($original, $adapted), [Text.UTF8Encoding]::new($false))
} elseif (-not $runtimeSource.Contains($adapted)) {
  throw 'The downloaded runtime has an unexpected local-game discovery implementation.'
}

$env:NODE_ENV = 'development'
$env:LOCAL_GAMES_DIR = Split-Path -Parent $gameRoot
$env:HOST = '127.0.0.1'
$env:PORT = "$ServerPort"
$env:CLIENT_PORT = "$ClientPort"
$env:LEAN_IDLE_MINUTES = '60'

function Test-HttpReady([string]$Url) {
  try {
    $response = Invoke-WebRequest -Uri $Url -TimeoutSec 3 -UseBasicParsing
    return $response.StatusCode -eq 200
  } catch { return $false }
}

$backend = $null
$frontend = $null
if (-not (Test-HttpReady $gameApi)) {
  $backend = Start-Process -FilePath $nodePath -ArgumentList @('--import', 'tsx', 'server/src/index.ts') `
    -WorkingDirectory $runtimeRoot -WindowStyle Hidden -PassThru `
    -RedirectStandardOutput (Join-Path $runDirectory 'server.log') `
    -RedirectStandardError (Join-Path $runDirectory 'server-errors.log')
}
if (-not (Test-HttpReady "http://127.0.0.1:$ClientPort")) {
  $frontend = Start-Process -FilePath $nodePath `
    -ArgumentList @('../node_modules/vite/bin/vite.js', '--host', '127.0.0.1', '--port', "$ClientPort", '--strictPort') `
    -WorkingDirectory (Join-Path $runtimeRoot 'client') -WindowStyle Hidden -PassThru `
    -RedirectStandardOutput (Join-Path $runDirectory 'client.log') `
    -RedirectStandardError (Join-Path $runDirectory 'client-errors.log')
}

@{ url = $gameUrl; serverProcessId = $backend.Id; clientProcessId = $frontend.Id } |
  ConvertTo-Json | Set-Content -LiteralPath (Join-Path $runDirectory 'processes.json')

$deadline = (Get-Date).AddSeconds(90)
while ((Get-Date) -lt $deadline) {
  if ((Test-HttpReady $gameApi) -and (Test-HttpReady "http://127.0.0.1:$ClientPort")) {
    $data = Invoke-RestMethod -Uri $gameApi -TimeoutSec 5
    Write-Output "Game running: $gameUrl"
    Write-Output "Worlds: $($data.tile.worlds); levels: $($data.tile.levels)"
    Write-Output "Logs and process IDs: $runDirectory"
    exit 0
  }
  if ($backend) {
    $backend.Refresh()
    if ($backend.HasExited) { throw "The game server stopped. See $runDirectory/server-errors.log" }
  }
  if ($frontend) {
    $frontend.Refresh()
    if ($frontend.HasExited) { throw "The browser client stopped. See $runDirectory/client-errors.log" }
  }
  Start-Sleep -Milliseconds 500
}
throw "The local game did not become ready. See $runDirectory."
