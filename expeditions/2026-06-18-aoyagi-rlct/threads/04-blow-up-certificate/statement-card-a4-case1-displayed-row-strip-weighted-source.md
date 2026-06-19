# Statement card - A4 Case 1 displayed row-strip weighted source

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`c8a7797f90103d8432cceda10c7a9cdf1e1f3093`.

Names:

- `DLNFibre.DLN.Aoyagi.diagonal_mul_apply`
- `DLNFibre.DLN.Aoyagi.case1RowStripSourceMatrix`
- `DLNFibre.DLN.Aoyagi.case1RowStripOldWeight`
- `DLNFibre.DLN.Aoyagi.case1RowStrip_diagonal_mul_sourceMatrix`
- `DLNFibre.DLN.Aoyagi.case1RowStrip_diagonal_mul_sourceMatrix_pivotFirst`
- `DLNFibre.DLN.Aoyagi.case1RowStrip_weightedPivotFirstSubstitutionData`
- `DLNFibre.DLN.Aoyagi.case1RowStrip_sourceOrder_identity`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedWeightedSourceData`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedWeightedSourceData.continuationBound`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedWeightedSourceData.displayedPivot_mem_center`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedWeightedSourceData.displayedPivot_mem_residualBlockPivotEntries`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedWeightedSourceData.sourceOrder_identity`

## Statement

Lean now records the elementary source-order weighted block for Aoyagi's
displayed Case 1(2) top-left row-strip chart.

The generic row-strip theorem proves:

```text
diag(oldWeight) * rowStripSource
  = diag(i |-> u * baseWeight_i) * A,
```

where row-strip entries of `rowStripSource` are `u * A_ij` and lower residual
rows are unchanged.  The old row weights are `baseWeight_i` on the strip and
`u * baseWeight_i` below the strip, representing the hidden old-variable
factorisation.  Thus the selected variable is counted once.

The pivot-first theorem transports this equality into the input shape required
by `WeightedPivotFirstSubstitutionData`, and the source-order theorem applies
the existing displayed top-left `Q/P` identity under supplied quotient
witnesses.

The Case 1-specific wrapper combines this supplied weighted source block with
`Case1FirstJumpHypotheses`, the stage bound `1 <= S`, and the actual source
column bound `J+1 <= n_(S+1)`.  It proves the displayed continuation bound and
displayed pivot memberships, then exposes the supplied source-order identity.

## Source Role

This matches Aoyagi's Case 1(2) display on PDF pp. 16-19: only rows
`J+1..J+J1` are divided by the selected variable, while rows below the strip
remain old residual entries and get the common selected factor through
`u_(s,k)=u_(S,J+1)u'_(s,k)`.

## Proved

- Left multiplication by a diagonal matrix weights each row.
- The Case 1(2) row-strip source block and hidden old-variable factorisation
  combine into one post row-weight factor `u * baseWeight_i`.
- The pivot-first form supplies the weighted source equality needed by the
  displayed top-left adapter.
- With supplied quotient witnesses and a normalised pivot entry, the displayed
  `Q/P` source-order product identity follows.
- Under `Case1FirstJumpHypotheses` plus the actual column bound, the displayed
  top-left pivot is source-valid for the finite Case 1 center and residual
  block interfaces.

## Assumed

- The displayed pivot chart has already produced the normalised matrix `A`.
- The hidden old variable has already been factored in the supplied
  `oldWeight` convention.
- Quotient witnesses for lower row weights are supplied.
- The following factor is already in the matching pivot-first column order.

## Not Proved

- No selected-entry chart construction.
- No full residual-block selected-entry substitution for Case 1(2).
- No source validity semantics for the hidden old label represented by `Unit`.
- No arbitrary row-strip pivot chart coverage.
- No chart regularity, transition regularity, or Jacobian formula.
- No recurrence/exponent post-data or continuation/advance transition
  invariant.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-displayed-row-strip-weighted-source-a4.md`.
- Review artifact:
  `review-case1-displayed-row-strip-weighted-source-a4.md`.

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
