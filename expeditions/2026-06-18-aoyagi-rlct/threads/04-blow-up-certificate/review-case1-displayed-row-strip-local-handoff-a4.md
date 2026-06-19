# Review - A4 Case 1 displayed row-strip local handoff

Status: reviewed; no blockers found.

## Reviewers

- Math/source scouts: `Lagrange the 3rd`, `Bacon the 3rd`.
- Implementation reviewer: `Curie the 3rd`.
- Controller verification: current checkpoint commands listed below.

## Math Review

The local handoff keeps the Case 1(2) off-by-one arithmetic straight. A
recurrence factor at level `r` first affects row `r+1`. Therefore the old
selected factor at level `J+J1` does not affect the strip
`J+1..J+J1`, while the fresh label at level `J` affects every residual row
from `J+1` onward.

The row and column bounds are also separated correctly. First-jump data gives
`1 <= J1` and `J+J1 < prefixMinNat n S`, while the actual source column bound
`J+1 <= n(S+1)` supplies actual-width validity for `(S,J+1)` and combines with
the row bound to give `J+1 <= prefixMinNat n (S+1)`. The exponent increment
uses the actual width `n(S+1)-J`, not the prefix minimum.

## Lean/API Review

`Case1DisplayedRowStripSuppliedTransitionBoundary` is correctly named as a
supplied boundary. It stores first-jump data, stage/source bounds, supplied
recurrence post-data, supplied pre-state exponent certificates, level-tail
invariants, and supplied exponent post-data. The source-order theorem still
takes the normalized matrix block and pivot equation as inputs.

The source-order wrapper
`exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData`
is a thin combination of the source-weight recurrence rewrite and the
factored-base post-data `Q/P` theorem. It does not claim to construct the
factored base or a chart-produced post-state.

The exponent projection is also conditional: it extends certificates using
the supplied pre-certificates, level-tail invariants, and supplied exponent
post-data. It does not prove that the chart leaves old exponent assignments
unchanged or produces the new assignment.

## Caveats

- This is not a chart-production theorem.
- It does not construct the factored-base recurrence from the original
  pre-state.
- It does not prove hidden old-label source validity.
- It does not prove chart coverage, regularity, transition regularity,
  Jacobian accounting, normal crossings, or RLCT extraction.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
