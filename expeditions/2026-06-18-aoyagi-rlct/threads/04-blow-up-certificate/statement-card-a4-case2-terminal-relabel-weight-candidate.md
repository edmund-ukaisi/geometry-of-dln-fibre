# Statement card - A4 Case 2 terminal relabel-weight candidate

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceTerminalEntryIdeal_eq_relabelCandidate_of_actualWidth`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_actualWidth`

## Statement

Lean now restates the stopped displayed Case 2 terminal product using the
relabelled `(S+1,0)` post-state pivot weight
`data.terminalRelabelPost.weight (J+1)`.  Actual-width exhaustion supplies
failed next continuation and proves this pivot weight equals the old supplied
post-state pivot weight `post.weight (J+1)`.

## Proved

- The source-displayed weighted terminal-product entry-ideal theorem with
  pivot scalar `data.terminalRelabelPost.weight (J+1)`.
- A source-model wrapper specialized to
  `b0 = data.terminalRelabelPost.weight (J+1)`.

## Assumed

- Actual next-width exhaustion `n(S+1)=J+1`.
- A supplied displayed Case 2 boundary.
- Supplied old top multiplier/block and suffix data.

## Not Proved

- No chart production of recurrence or exponent data.
- No proof that `[Ctop;C0]` is source-produced `C'^(S+1)`.
- No automatic transport of Case 2 gap or flat-tail invariants.
- No chart coverage or regularity, Jacobian arithmetic, normal crossings,
  RLCT extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-terminal-relabel-weight-candidate-a4.md`.
- Review artifact:
  `review-case2-terminal-relabel-weight-candidate-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `scripts/sorries`
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
