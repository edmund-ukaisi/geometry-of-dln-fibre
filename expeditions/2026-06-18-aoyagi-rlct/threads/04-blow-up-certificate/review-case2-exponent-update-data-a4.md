# A4 Case 2 Exponent Update Data Review

Date: 2026-06-19.

Scope: xhigh source/math and Lean/API review of the corrected Case 2 exponent
update-data wrapper.

## Reviewers

- Source/math explorer: `Volta the 2nd`.
- Lean/API explorer: `Kepler the 2nd`.

## Verdict

No blockers. Both reviewers confirmed that
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`
is a sound thin wrapper around the existing corrected new-label domain
extension theorem.

The source/math review confirmed that the theorem is source-faithful as
corrected certificate bookkeeping, not as verbatim PDF data. The Lean/API
review confirmed that old-label non-equality is proved exactly by
`not_introducedLabel_case2_new_before`, and that the selected-label update
equalities are robust.

## Required Caveats

- This is corrected exponent-domain bookkeeping, not chart production.
- This does not prove a chart leaves old exponent assignments unchanged.
- This does not derive exponent data from recurrence post-data.
- This does not prove a full exponent transition invariant.
- This does not prove arbitrary-pivot transport.
- This does not prove source comparability.
- This does not introduce normal-crossing or RLCT extraction claims.
- This does not claim that the corrected vector is the PDF's printed Case 2
  vector.

## Checks

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From worktree root: `git diff --check`: passed.
