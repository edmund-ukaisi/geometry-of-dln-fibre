# Statement card - A4 Case 1 displayed row-strip factored-base post-data

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`764944f2752ffe2798011d78ecbb89ed3c0ab268`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripFactoredBasePostData`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.case1DisplayedRowStrip_diagonal_mul_sourceMatrix_pivotFirst_succWeights`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.exists_case1DisplayedRowStrip_sourceOrder_identity_succWeights_of_postData`

## Statement

Lean now packages the displayed Case 1(2) recurrence-weight update relative to
a factored-old base state.

The factored base is not the original pre-chart recurrence state.  It is the
state after replacing the selected old variable by its residual coordinate.
Supplied post-data then adds the fresh label `(S,J+1)` at level `J` with
selected variable `u`, giving

```text
post.weight i = u * factoredBase.weight i
```

for all residual rows `J+1 <= i`.

The displayed row-strip `Q/P` wrapper now rewrites the right-hand diagonal
from the common `u * factoredBase.weight` form to supplied post weights.

## Source Role

Aoyagi prints the factorisation `u_(s,k)=u_(S,J+1)u'_(s,k)` and displays
`b'_i = u_(S,J+1)b_i` over the residual row range.  The PDF does not spell out
complete old-label post-data, so Lean keeps this as a supplied-data boundary.

## Proved

- A named factored-base recurrence post-data boundary.
- Pivot-first row-strip source weights rewrite to supplied post weights.
- The displayed source-order `Q/P` identity can be stated with post weights on
  the right-hand diagonal.

## Assumed

- The factored-base recurrence state has already replaced the old selected
  variable by its residual coordinate.
- Supplied post-data preserves old factored-base labels and adds `(S,J+1)` at
  level `J` with variable `u`.
- The actual-width proof for `(S,J+1)` is supplied.
- The row-strip source matrix and following factor are supplied.

## Not Proved

- No relation between the original pre-state and the factored-base state.
- No hidden old-label source-validity production.
- No complete source extraction of all old-label post assignments.
- No chart construction, chart coverage, regularity, or Jacobian formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-row-strip-factored-base-postdata-a4.md`.
- Review artifact:
  `review-case1-displayed-row-strip-factored-base-postdata-a4.md`.

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
