#requires -Version 7.0
param(
  [string]$Root = (Split-Path -Parent $PSScriptRoot),
  [string]$OutputPath = 'game.zip',
  [switch]$ListOnly
)

$ErrorActionPreference = 'Stop'
$rootPath = [IO.Path]::GetFullPath($Root)
$required = @('Game.lean','Game','images','lean-toolchain','lakefile.lean','lake-manifest.json',
  '.lake/config','.lake/build/lib/lean/Game.olean','.lake/gamedata/game.json',
  '.lake/packages/GameServer/.lake/build/lib/lean/GameServer.olean')
foreach ($relative in $required) {
  if (-not (Test-Path -LiteralPath (Join-Path $rootPath $relative))) {
    throw "Missing required release input: $relative. Build the game and GameServer first."
  }
}

# Only the game and its Lean build belong in the hosted artifact. In particular,
# the local web-client checkout, its node_modules, SQLite database, logs, process
# IDs, and validation fixtures must never enter the import ZIP.
$inputs = @('Game.lean','Game','Test','scripts','images','.i18n','lean-toolchain','lakefile.lean','lake-manifest.json',
  'LICENSE','README.md','CURRICULUM.md','SOURCES.md','STATUS.md','TACTIC_UNLOCKS.md',
  'HOSTING_REPORT.md','.lake/config','.lake/build','.lake/gamedata','.lake/packages')
$files = [Collections.Generic.List[string]]::new()
$directories = [Collections.Generic.List[string]]::new()
foreach ($inputPath in $inputs) {
  $absolute = Join-Path $rootPath $inputPath
  if (-not (Test-Path -LiteralPath $absolute)) { continue }
  if ([IO.Directory]::Exists($absolute)) {
    # Git requires its refs/ and objects/ directories even when they are empty.
    # Fresh detached Lake dependencies can have no files under refs/; a files-only
    # ZIP loses that directory and is no longer recognized as a Git repository.
    $directories.Add($absolute)
    foreach ($directory in [IO.Directory]::EnumerateDirectories($absolute,'*',[IO.SearchOption]::AllDirectories)) {
      $directories.Add($directory)
    }
    foreach ($file in [IO.Directory]::EnumerateFiles($absolute,'*',[IO.SearchOption]::AllDirectories)) {
      if ([IO.Path]::GetExtension($file) -eq '.mo') { continue }
      $files.Add($file)
    }
  } else { $files.Add($absolute) }
}

if ($ListOnly) {
  foreach ($directory in $directories) { [IO.Path]::GetRelativePath($rootPath,$directory).Replace('\','/') + '/' }
  foreach ($file in $files) { [IO.Path]::GetRelativePath($rootPath,$file).Replace('\','/') }
  return
}

$archivePath = if ([IO.Path]::IsPathRooted($OutputPath)) {
  [IO.Path]::GetFullPath($OutputPath)
} else { [IO.Path]::GetFullPath((Join-Path $rootPath $OutputPath)) }
if (Test-Path -LiteralPath $archivePath) {
  throw "Output already exists: $archivePath. Choose a new -OutputPath to preserve the old artifact."
}
$archive = [IO.Compression.ZipFile]::Open($archivePath,[IO.Compression.ZipArchiveMode]::Create)
try {
  foreach ($directory in $directories) {
    $entryName = [IO.Path]::GetRelativePath($rootPath,$directory).Replace('\','/') + '/'
    if ($entryName.StartsWith('../') -or [IO.Path]::IsPathRooted($entryName)) {
      throw "Release input escapes the game directory: $entryName"
    }
    $archive.CreateEntry($entryName) | Out-Null
  }
  foreach ($file in $files) {
    $entryName = [IO.Path]::GetRelativePath($rootPath,$file).Replace('\','/')
    if ($entryName.StartsWith('../') -or [IO.Path]::IsPathRooted($entryName)) {
      throw "Release input escapes the game directory: $entryName"
    }
    [IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
      $archive,$file,$entryName,[IO.Compression.CompressionLevel]::Optimal) | Out-Null
  }
} finally { $archive.Dispose() }
Write-Output "Packaged $($files.Count) files and $($directories.Count) directories into $archivePath"
Write-Output 'This command only creates a local ZIP. It does not upload, import, or publish the game.'
