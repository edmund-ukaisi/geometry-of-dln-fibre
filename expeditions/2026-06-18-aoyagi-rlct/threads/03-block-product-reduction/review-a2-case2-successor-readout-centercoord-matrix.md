# Review - A2 Case 2 successor readout CenterCoord matrix

Date: 2026-06-26.

Reviewers: controller, using prior xhigh source/API scouts `Gauss` and `Nash`.

## Verdict

Pass for conditional finite composition.  The theorem converts a supplied
successor source-chart entrywise readout into the exact selected-entry
`CenterCoord.chartMap` matrix shape for the residual-factor product.  It does
not prove the readout.

## Source Check

Gauss confirmed that Aoyagi pp. 19-22 support the old selected-entry chart and
the continuing product `D_(J+1) * C'_+`, but not an identification of the
product entries with successor chart coordinates.  The theorem keeps that
identification as `hentry`.

The only source-backed chart vocabulary used here is the selected-entry
substitution formula itself.  The post-pivot product-to-chart readout remains
outside this theorem.

## Lean/API Check

Nash identified the useful downstream composition point: after
`Case2ResidualFactorProduct.lean` and `SelectedEntrySignedBoxMeasure.lean`,
one can combine

```text
residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply
```

without importing selected-entry measure APIs into the finite product module.

The proof assembles the residual-coordinate equivalence

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J+1) e2.symm (e0k.symm.trans eNext)
```

and checks that this agrees on displayed entries with the `hentry` equivalence
using explicit equivalence cancellation.

## Lean Check

Focused module build passed:

```text
env LAKE_SHARED=/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct/lean/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge
```

## Nonclaims

No construction of the successor readout, endpoint equivalences, compatible
residual factors, source-produced `Cprime`, source image, source-measure
transport, chart coverage, normal crossings, pole order, or RLCT.
