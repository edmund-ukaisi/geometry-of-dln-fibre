# A4 Case 2 Corrected Exponent Post-Data Review

Date: 2026-06-19.

Scope: xhigh source/math and Lean/API review of the corrected Case 2 exponent
post-data package and supplied-post gap bridge.

## Reviewers

- Source/math explorer: `Kierkegaard the 3rd`.
- Lean/API explorer: `Locke the 3rd`.

## Verdict

No blockers.

The source/math review found no source or mathematical issues. It confirmed
that the implementation keeps the printed Case 2 vector separate from the
corrected prefix-minimum vector, uses actual-width label domains, and advances
the least-value gap correctly.

The Lean/API review found no theorem-shape blockers. It confirmed that the
package is narrow and useful: it packages old-label preservation plus the new
corrected exponent values, while leaving source validity and certification to
`CorrectedCase2NewLabelCertificate`.

## Incorporated API Fixes

- Renamed the selected-label override supplier to
  `Case2CorrectedExponentPostData.updateSelected`, since it constructs the
  post-data package rather than a certificate package.
- Aligned the supplied-post gap theorem argument order with the level-invariant
  helper: `hpost`, `hinv`, `hexp`, `hgap`.

## Required Caveats

- This is corrected certificate and invariant bookkeeping, not chart
  production.
- This does not prove old exponent assignments are geometrically unchanged.
- This does not prove a full exponent transition invariant.
- This does not prove arbitrary-pivot transport or chart coverage.
- This does not prove source comparability, normal crossings, or RLCT
  extraction.
- This does not claim that the corrected vector is the PDF's printed Case 2
  vector.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
