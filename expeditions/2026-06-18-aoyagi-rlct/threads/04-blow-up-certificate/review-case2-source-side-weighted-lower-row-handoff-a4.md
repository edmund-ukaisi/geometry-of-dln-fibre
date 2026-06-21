# Review - A4 Case 2 source-side weighted lower-row handoff

Status: reviewed and formalised.

## Scope Check

The target is a projection of an already-proved full weighted local `Q/P`
identity, followed by the already-proved weighted lower-row projection of the
right side.  It adds no chart production claim.

## Risks

- The theorem must keep the lower-row diagonal weights.
- The theorem must not include the pivot row.
- The theorem must not name itself as an inductive step or successor product.
- The theorem must keep corrected post-data as supplied/concrete data, not
  coordinate-derived data.

## Verdict

The Lean theorem landed with the shape typechecked by the Lean API scout.  The
source-side product includes `weightedPivotBlockRowOp q`, and the conclusion
keeps the lower-row successor weight diagonal.

## Xhigh Checks

Source checker `Maxwell` accepted the theorem as source-faithful finite
algebra from Aoyagi Case 2 pp. 19-22.  It is a projection of the displayed
`P diag(b') D'' C' = diag(b') D''' C'` identity after reconstructing the old
following factor as `Q*Cprime`.

Lean API scout `Noether` typechecked the concrete theorem via
`lake env lean --stdin`, using the existing local product package and the
weighted lower-row projection wrapper.

Formalised Lean name:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_constructedSourceFreeCprimeWeightedNextSameStageProduct_withCorrectedPostData
```
