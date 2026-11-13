# Reproducibility record

Toolchain: `leanprover/lean4:v4.36.0-rc2` (Lean commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`). Lake: `5.0.0-src+b35cb10`. Mathlib: `9d581dfff2e41de989072ea63abf3daf69311520`. All transitive pins are in lake-manifest.json and evidence/dependency-audit.json.

The successful build was run on Windows x86_64 from the staged NSeries-release folder. LEAN_PATH was cleared. `Verify-Release.ps1 -Fresh` moved the existing project `.lake/build` aside, leaving the final build without N-Series object files, then ran `lake build` and `lake env lean NSeriesAudit.lean`. The script checked all nine dependency Git HEADs and required clean Git status before building. No theorem statements were changed to obtain acceptance.

Dependency source/Git trees were copied from the existing BakerTrisection environment without altering that environment. Every copied source tree was clean and matched its recorded pin. The earlier nine Lake “local changes” warnings were investigated: Git status in the original location failed under the restricted execution environment; the copied trees returned clean status. Generated `.lake` caches were copied only after source inspection. They are not included in the repository and are not represented as newly compiled Mathlib binaries.

For a new clone, obtain the pinned dependency cache with `lake exe cache get`, then `lake build`. Do not run an unreviewed `lake update` that changes pins. Compare the manifest against SHA256SUMS.txt if any setup tool rewrites it. A full dependency-source rebuild is an optional stronger check and was not performed for this release. Independent-machine reproduction and CI are not claimed.

`SHA256SUMS.txt` covers the released text sources, configuration, manuscript, preserved originals, and audit/build evidence, excluding itself. The Git commit identifies the complete publication snapshot. Files are stored without Git newline conversion (`* -text` in .gitattributes), so the byte hashes remain meaningful across platforms. Failed-attempt logs are clearly named and must not be confused with the successful build and final audit logs.

Recheck all published hashes in PowerShell:

```powershell
Get-Content SHA256SUMS.txt | ForEach-Object {
  $hash, $path = $_ -split '  ', 2
  if ((Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant() -ne $hash) {
    throw "Hash mismatch: $path"
  }
}
```
