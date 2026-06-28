# Statement card: A2 retained-passive canonical chart selected-entry square-sum bridge

## Lean name

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
```

## Content

For a determinant-chart retained-passive tuple `z`, if the canonical residual
factor product of `(ofTopologyTuple z).C` is a selected-entry chart matrix
after a finite residual-coordinate reindexing, then the canonical chart-side
residual square-sum is the selected-entry center residual.

The proof uses:

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualFactorProduct
AoyagiResidualBlockCoordinateIndex.value_matrix
aoyagiCoordinateSquareSum_comp_equiv
SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap
```

## Proved

The theorem

```text
aoyagiCoordinateSquareSum_retainedPassiveP13Canonical_chart_eq_selectedEntryCenter_residual_of_residualFactorProduct_eq_matrix
```

is proved in `RetainedPassiveLocalJacobianMeasure.lean`.

## Assumed

The input tuple lies in `topologyTupleDetChartSet`, and the residual factor
product has the supplied selected-entry matrix form.

## Cited

None.  This is finite coordinate readout and finite-sum reindexing.

## Deferred

The selected-entry matrix identity for the full canonical suffix product,
zero-locus/nullity analysis, chart-side positivity, finite negative-power
integrability, density transport, normal crossings, pole order, and RLCT
extraction.

## Review

Xhigh review by `Dirac the 3rd` passed after this status correction.  The
review is saved at
`review-a2-retained-passive-canonical-chart-selected-entry-square-sum.md`.

## Verification

Focused `RetainedPassiveLocalJacobianMeasure` build passed.  `scripts/sorries`,
`git diff --check`, and Lean touched-file forbidden-marker search passed.
