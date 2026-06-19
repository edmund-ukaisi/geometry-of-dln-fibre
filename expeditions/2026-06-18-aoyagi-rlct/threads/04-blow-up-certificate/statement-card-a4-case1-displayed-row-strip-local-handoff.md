# Statement card - A4 Case 1 displayed row-strip local handoff

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`PENDING-COMMIT`.

Names:

- `DLNFibre.DLN.Aoyagi.IntroducedLabelRecurrenceState.Case2SuppliedPostData.exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.stage_pos`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.continuationBound`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.newLabelActualWidth`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_sourceWeights`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.extendExponentDomain`

## Statement

Lean now packages the displayed top-left Case 1(2) local handoff as supplied
data.

The source-order projection writes the left diagonal using the original source
recurrence after substituting the old selected variable at level `J+J1`:

```text
monomialRec (mulStepAt factoredBase.step u (J+J1)).
```

The right diagonal uses the supplied post-state recurrence weights after the
fresh label `(S,J+1)` is added at level `J`.

The exponent projection extends the introduced-label exponent certificate
domain using the supplied Case 1(2) displayed row-strip exponent post-data.

## Source Role

This is the local source-facing handoff for Aoyagi's printed Case 1(2)
displayed row-strip chart on PDF p. 17. It combines the already proved
first-jump width bookkeeping, source-weight row-strip algebra,
factored-base recurrence post-data, and new-label exponent post-data.

## Proved

- The displayed pivot continuation bound follows from first-jump row bounds
  and the actual source column bound.
- The fresh label `(S,J+1)` is actual-width valid under `2 <= S <= L` and
  `J+1 <= n(S+1)`.
- The displayed source-order `Q/P` identity can be stated with original source
  recurrence weights on the left and supplied post weights on the right.
- Supplied exponent pre-certificates, level-tail invariants, and supplied
  exponent post-data extend the exponent certificate domain to `(S,J+1)`.

## Assumed

- `Case1FirstJumpHypotheses`.
- A supplied factored-base recurrence state.
- Supplied recurrence post-data from the factored-base state to the post state.
- Supplied pre-state exponent certificates and level-tail invariants.
- Supplied exponent post-data.
- A normalized displayed pivot block with pivot entry equal to `1`.

## Not Proved

- No construction of the factored-base recurrence from the original pre-state.
- No hidden old-label source-validity theorem.
- No proof that a chart produces the supplied recurrence or exponent post-data.
- No chart coverage, chart regularity, transition regularity, or Jacobian
  formula.
- No full Case 1 transition invariant.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-row-strip-local-handoff-a4.md`.
- Review artifact:
  `review-case1-displayed-row-strip-local-handoff-a4.md`.

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
