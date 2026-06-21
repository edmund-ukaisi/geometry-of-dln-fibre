# Statement card - A4 Case 2 weighted free Cprime lower-row projection

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Expected names:

- `DLNFibre.DLN.Aoyagi.weightedPivotDiagonal_mul_lowerRows`
- `DLNFibre.DLN.Aoyagi.weightedPivotDiagonal_mul_lowerRows_reindex`
- `DLNFibre.DLN.Aoyagi.case2DisplayedWeightedPaperDppp_mul_freeCprime_postPivot_eq_nextSameStageProduct`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.postPivotWeightedFreeCprimeNextSameStageProduct`

## Statement

For the displayed Case 2 pivot chart, lower rows of

```text
(weightedPivotDiagonal successorWeights * D''') * Cprime
```

reindex to the next same-stage row domain as the lower-row successor-weight
diagonal times the already-proved bare post-pivot product

```text
case2DisplayedPostPivotResidualBlock
  *
case2DisplayedPostPivotFreeFollowingFactor.
```

## Proved

- Generic lower-row projection for `weightedPivotDiagonal`.
- Reindexed lower-row projection along an equivalence.
- Displayed Case 2 weighted lower-row projection for arbitrary lower-row
  weights.
- Supplied-boundary wrapper using the successor state's row weights.

## Assumed

- Displayed pivot validity `1 <= S` and
  `J+1 <= prefixMinNat n (S+1)`.
- A supplied successor recurrence state only as a source of row weights.
- A supplied residual block and free pivot-first `Cprime`.

## Cited

- None in Lean.  This is finite matrix algebra and finite reindexing.

## Deferred

- Source production of `Cprime`, successor chart-family construction, chart
  coverage, arbitrary-pivot coverage, transition invariance, terminal
  relabeling, Jacobian arithmetic, normal crossings, pole order, and RLCT.

## Review

- xhigh source checker `Beauvoir` green-lit this as a finite displayed-pivot
  weighted lower-row projection, not a successor product theorem.
- xhigh Lean API scout `Dirac` recommended the same row-scaling abstraction
  and the supplied-boundary wrapper with explicit successor row weights.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
