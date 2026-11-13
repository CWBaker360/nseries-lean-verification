# Integrated release report

Date: 2026-11-13 (America/St_Johns)

## Result

PASS: clean project `lake build`, 18,239 jobs; all 28 release source modules and the aggregate/audit targets compiled. PASS: 112 declaration axiom reports, checked against the allowlist `propext`, `Classical.choice`, `Quot.sound`. No final `sorryAx` or unexpected axiom. See evidence/certification.log and evidence/certification.exit.

## Repairs and preservation

- B5: replaced the duplicated C2 prefix with `import NSeriesC2Final`. The removed block is byte-identical to C2Final before its namespace closing command. All B5-specific statements and proofs were retained.
- E9: staged the previously repaired Lagrange interpolation proof from the earlier verification session. Statements are unchanged.
- E3: the first full source build failed in `BakerNSeries.three_scale_sharp_weights`, line 68: `ring failed, ring expressions not equal`. The sixth-moment hypothesis in `linear_combination` had coefficient `+ Real.pi^7 / (5040 * N^6)`; the correct coefficient is negative. Only that proof sign was changed. The targeted repair build passed, followed by a fresh full build. The initial failure and exact diagnostic remain in evidence/build-attempt-1.log; the patch is evidence/E3-proof-sign.patch. The failed attempt's downstream sorryAx reports are not certification results.
- E10: unchanged SHA-256 `e1bab16df7e67c3a7c5240624242c91f35519b7634611c64e6f20c909a818f76`.
- Original B5, E3, E9, the supplied v4 section, and the upstream manuscript are preserved under originals/. Original project files outside the staged release were left untouched.

## Warnings

The final build retains nonfatal warnings: Mathlib recommends the new `module` header in legacy modules; D1/D2BClosing have tactic-sequencing linter suggestions; D3Positive has an implicitly used parameter-name warning; D3Limit has a `letI` style suggestion. Informational `ring_nf` suggestions appear within successful tactic sequences. None is a final compiler error. Complete diagnostics are preserved in the build log. No dependency dirty-tree warnings were emitted in the clean release environment.

## Manuscript correspondence

The 16 theorem names in the verification table were extracted and checked against the integrated environment. The table's three-scale row now explicitly identifies the polygonal specialization; the general finite cancellation statement is covered by the explicit-hypothesis moment theorem. Numerical digit-growth language in the main manuscript is qualified as computational evidence. The supplied trisection paper is a separate manuscript and was not used as the host for N-Series cross-references.

The integrated manuscript is based on N-Series-pi-acceleration commit 53c7135741354f1911e2488260e479140afcefaa. The desktop LaTeX compiler successfully compiled the integration. No digit experiments were rerun or certified by this work.

## Limits

The clean build rebuilt the N-Series project using checked pinned dependency sources and reused dependency build caches. It did not rebuild all Mathlib or Lean from source. The release does not claim an independent-machine or CI reproduction. These limits are documented, not hidden behind the build-pass claim.
