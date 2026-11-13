# N-Series Lean verification

Integrated A-E10 verification package for Wayne Baker's N-Series manuscript.

**Build and axiom audit: PASS (2026-11-13).** The clean project build completed 18,239 Lake jobs and compiled all 28 release modules. The integrated audit checked 112 named declarations. Every reported axiom belongs to `propext`, `Classical.choice`, and `Quot.sound`; no final declaration depends on `sorryAx`.

## Reproduce

Install Elan, Git, and the toolchain selected by `lean-toolchain`, then run from a fresh clone:

```sh
lake exe cache get
lake build
lake env lean NSeriesAudit.lean
lake env lean NSeriesTheoremSignatures.lean
```

Keep `lake-manifest.json` unchanged. It pins all nine dependencies. On Windows, after dependency setup, `./Verify-Release.ps1 -Fresh` checks dependency HEADs and clean status, preserves any previous project build directory, rebuilds the release, and rejects unexpected axiom reports.

The recorded clean build rebuilt every N-Series module from source. Existing dependency build caches were reused after checking that the dependency source trees were clean and matched their pins. This is not a from-source rebuild of Lean or all of Mathlib. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Evidence

- [Release report](RELEASE-REPORT.md)
- [Complete successful build](evidence/build-reproduction.log)
- [Final integrated axiom audit](evidence/axiom-reproduction.log)
- [Dependency inspection](evidence/dependency-inspection.md) and [pins/status](evidence/dependency-audit.json)
- [Reproducibility manifest](release-manifest.json) and [SHA-256 hashes](SHA256SUMS.txt)
- [Manuscript theorem signatures](evidence/manuscript-theorem-signatures.log)
- [Integrated manuscript source](paper/nseries_pi_acceleration.tex) and [verification section](paper/FormalVerification_v4.tex)

The earlier failed build is retained as historical evidence. Its `sorryAx` messages arose from a failed E3 proof elaboration and are not the final audit result.

## Scope

The selected release comprises A, consolidated B5/B6, C2Final, the D geometry/limit chain, and E1-E10. Earlier exploratory B/C files are superseded by these consolidated modules; the build does not claim to certify every historical candidate file.

Theorems certify the stated mathematical bounds, limits, finite moment systems, and trisection identities. High-precision digit runs, 100,000-digit agreement, and observed digit-growth rates remain separate computational evidence.

The mathematical theorem statements were not weakened. B5 imports C2Final instead of repeating an identical proof block; E3 has a one-sign correction in a proof combination; E9 uses the previously repaired proof; E10 is byte-identical to its individually checked source. Some historical source headers still say “not compiled”; the build logs and hashes identify the checked release bytes.

Manuscript provenance: [N-Series-pi-acceleration](https://github.com/CWBaker360/N-Series-pi-acceleration), commit `53c7135741354f1911e2488260e479140afcefaa`. That repository was not modified. This repository is the separate formal-verification companion. Code and paper licensing are preserved in LICENSE and LICENSE-PAPER.md.
