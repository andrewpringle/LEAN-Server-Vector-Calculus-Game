#requires -Version 7.0
$ErrorActionPreference = 'Stop'
$gameRoot = Split-Path -Parent $PSScriptRoot
$fixture = Join-Path $gameRoot ('.lake/validation/package-fixture-' + [guid]::NewGuid().ToString('N'))
$included = @('Game.lean','Game/Levels/Fixture.lean','images/cover.svg','lean-toolchain',
  'lakefile.lean','lake-manifest.json','.i18n/config.json','.lake/config/lakefile.olean',
  '.lake/build/lib/lean/Game.olean','.lake/gamedata/game.json',
  '.lake/packages/GameServer/.lake/build/lib/lean/GameServer.olean',
  '.lake/packages/Fixture/.lake/build/lib/lean/Fixture.olean')
$excluded = @('.git/config','.lake/leangame-runtime/node_modules/not-a-game.txt',
  '.lake/local-game/leangame.db','.lake/local-game/processes.json','.lake/validation/progress.json')
foreach ($relative in ($included + $excluded)) {
  $file = Join-Path $fixture $relative
  New-Item -ItemType Directory -Force -Path (Split-Path -Parent $file) | Out-Null
  [IO.File]::WriteAllText($file, 'Packaging test fixture; not a compiled game.')
}

$listed = @(& (Join-Path $PSScriptRoot 'package-game.ps1') -Root $fixture -ListOnly)
foreach ($relative in $included) {
  if ($relative -notin $listed) { throw "Required file missing from package list: $relative" }
}
foreach ($relative in $excluded) {
  if ($relative -in $listed) { throw "Development file leaked into package list: $relative" }
}
& (Join-Path $PSScriptRoot 'package-game.ps1') -Root $fixture -OutputPath 'fixture.zip'
$archive = [IO.Compression.ZipFile]::OpenRead((Join-Path $fixture 'fixture.zip'))
try {
  $names = @($archive.Entries | ForEach-Object FullName)
  foreach ($relative in $included) {
    if ($relative -notin $names) { throw "Required ZIP entry missing: $relative" }
  }
  foreach ($relative in $excluded) {
    if ($relative -in $names) { throw "Development file leaked into ZIP: $relative" }
  }
  if ($names | Where-Object { $_.Contains('\') -or $_.StartsWith('/') -or $_.StartsWith('../') }) {
    throw 'ZIP entries must have portable relative paths.'
  }
} finally { $archive.Dispose() }
Write-Output 'PASS: package list and real ZIP preserve hidden Lean build files and exclude the local runtime, database, process IDs, and validation data.'
