param([switch]$Fresh)
$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$env:LEAN_PATH = ''
$manifest = Get-Content -Raw lake-manifest.json | ConvertFrom-Json
foreach ($dep in $manifest.packages) {
  $path = Join-Path $PSScriptRoot ('.lake/packages/' + $dep.name)
  if (-not (Test-Path -LiteralPath $path)) { throw ('Missing dependency: ' + $dep.name + '. Run lake update and lake exe cache get first, then verify manifest pins.') }
  Push-Location -LiteralPath $path
  try {
    $head = & git rev-parse HEAD
    if ($LASTEXITCODE -ne 0 -or $head -ne $dep.rev) { throw ('Revision mismatch: ' + $dep.name) }
    $dirty = @(& git --no-optional-locks status --porcelain=v1)
    if ($LASTEXITCODE -ne 0 -or $dirty.Count -ne 0) { throw ('Dependency is dirty or unreadable: ' + $dep.name) }
  } finally { Pop-Location }
}
if ($Fresh) {
  $build = Join-Path $PSScriptRoot '.lake/build'
  if (Test-Path -LiteralPath $build) {
    $resolved = (Resolve-Path -LiteralPath $build).Path
    if ($resolved -ne [IO.Path]::GetFullPath($build)) { throw 'Unexpected build path' }
    $saved = Join-Path $PSScriptRoot ('.lake/previous-build-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
    Move-Item -LiteralPath $resolved -Destination $saved
  }
}
& lake build 2>&1 | Tee-Object -FilePath evidence/build-reproduction.log
if ($LASTEXITCODE -ne 0) { throw 'lake build failed' }
& lake env lean NSeriesAudit.lean 2>&1 | Tee-Object -FilePath evidence/axiom-reproduction.log
if ($LASTEXITCODE -ne 0) { throw 'Integrated axiom audit failed' }
$log = Get-Content -Raw evidence/axiom-reproduction.log
$expected = @(Get-Content NSeriesAudit.lean | Where-Object { $_ -match '^#print axioms ' }).Count
$reports = [regex]::Matches($log, "(?m)^'(BakerNSeries\.[^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
if ($reports.Count -ne $expected) { throw "Expected $expected axiom reports, got $($reports.Count)" }
if ($log -match '\bsorryAx\b') { throw 'sorryAx found' }
foreach ($report in $reports) {
  foreach ($axiom in ($report.Groups[2].Value -split ',\s*' | ForEach-Object { $_.Trim() } | Where-Object { $_ })) {
    if ($axiom -notin @('propext','Classical.choice','Quot.sound')) { throw ('Unexpected axiom: ' + $axiom) }
  }
}
& lake env lean NSeriesLadderAudit.lean 2>&1 | Tee-Object -FilePath evidence/ladder-axiom-reproduction.log
if ($LASTEXITCODE -ne 0) { throw "Ladder axiom audit failed" }
$ladderLog = Get-Content -Raw evidence/ladder-axiom-reproduction.log
$ladderExpected = @(Get-Content NSeriesLadderAudit.lean | Where-Object { $_ -match "^#print axioms " }).Count
$ladderReports = [regex]::Matches($ladderLog, "depends on axioms: \[([^\]]*)\]")
if ($ladderExpected -ne 5 -or $ladderReports.Count -ne $ladderExpected) { throw "Ladder audit report count mismatch" }
if ($ladderLog -match "sorryAx") { throw "Ladder uses sorryAx" }
foreach ($entry in $ladderReports) { foreach ($axiom in ($entry.Groups[1].Value -split ",\s*")) { if ($axiom -notin @("propext","Classical.choice","Quot.sound")) { throw "Unexpected Ladder axiom: $axiom" } } }
Write-Output "PASS: five Ladder certificate audits."
Write-Output "PASS: full build and $expected declaration audits."