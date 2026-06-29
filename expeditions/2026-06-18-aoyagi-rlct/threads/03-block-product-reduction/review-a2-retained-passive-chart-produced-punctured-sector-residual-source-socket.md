# Review: A2 retained-passive chart-produced punctured-sector residual-source socket

Reviewer: `Harvey the 3rd` (`019f1413-3343-72f1-a325-b584f902a723`)

Verdict: PASS, with corrections incorporated in the Lean proof.

## Scope checked

The reviewer checked:

- the reproduction
  `reproduction-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`;
- the statement card
  `statement-card-a2-retained-passive-chart-produced-punctured-sector-residual-source-socket.md`;
- the supporting Lean APIs for the punctured-sector map identity, fixed-pivot
  inverse, pivot-zero collapse, selected-entry residual square-sum, finite
  square-sum reindexing, and `residualNegPowerIntegrableOn`.

## Findings

The pivot-nonzero argument is sound.  If the residual-coordinate value has
zero selected pivot, then `preimageOfPivotNeZero` has zero pivot coordinate,
`chartMap_eq_zero_of_pivot_eq_zero` collapses the selected-entry chart to
zero, and `residual_eq_aoyagiCoordinateSquareSum_chartMap` makes the selected
residual zero, contradicting the pulled-back marginal positivity.  With pivot
nonzero, `chartMap_preimageOfPivotNeZero` applies, and
`aoyagiCoordinateSquareSum_comp_equiv residualCoordEquiv.symm` identifies the
selected-entry square-sum with the fixed-base residual square-sum.

The measure direction is correct.  The existing theorem gives

```text
Measure.map inverseReadout mu = marginal.
```

Thus positivity transfers from `marginal` to `mu` by `ae_of_ae_map`, and the
finite integral transfers by `lintegral_map` plus `lintegral_congr_ae`.  The
final restriction to `localSource` uses the returned support equality
`mu.restrict localSource = mu`.

No determinant-chart Haar, source-prior, Jacobian, normal-crossing, pole-order,
or RLCT claim is smuggled in.  The source measure is arbitrary, and the
marginal positivity/integrability assumptions remain explicit.

## Incorporated corrections

- The finite-integral assumption is stated in Lean-exact lintegral form:
  `∫⁻ y, ENNReal.ofReal ((residual pivotNext y)^(-t)) ∂ marginal < ∞`.
- The proof constructs measurability of `inverseReadout` from residual-coordinate
  measurability and
  `SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero`.
- The pivot contradiction explicitly passes through
  `residual_eq_aoyagiCoordinateSquareSum_chartMap` after
  `chartMap_eq_zero_of_pivot_eq_zero`.
- The marginal assumptions are scoped after the existential `V`, since
  `marginal = Measure.map Prod.snd (sourceMeasure.restrict V)` depends on that
  sector.
