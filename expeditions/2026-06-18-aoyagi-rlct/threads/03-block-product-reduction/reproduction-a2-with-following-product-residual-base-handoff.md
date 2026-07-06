# Reproduction - A2 with-following product-residual base handoff

Date: 2026-07-06.

Status: Lean target implemented as a residual-base bridge.

## Source Boundary

Aoyagi pp. 10-13 reduce a block of the transformed network product to a
cleaned product of residual factors.  In the two-edge Case 2 endpoint
convention used here, the with-following source has active factors

```text
C_1(z) = D(theta.yNext),
C_0(z) = F,
```

so the cleaned p.13 product residual is

```text
P(z) = C_1(z) * C_0(z) = D(theta.yNext) * F.
```

This is the product term `prod C^(s)` after the elementary block reduction.  It
is not the original transformed loss block by itself: the displayed local
transformed loss still also contains regular terms such as `C1 - I`, `F2`,
`F3`, and the correction `prod C^(s) - F3 F2`.  The comparison to the original
square-Frobenius loss belongs to the separate adapted-product and endpoint
loss-comparison layer.

## Calculation

The fixed-base p.13 residual block is indexed by endpoint complement labels.
The with-following Case 2 product-residual readout is indexed by

```text
Case2ResidualRowIndex n S (J + 1) x tau.
```

The endpoint equivalences

```text
e (Fin.last 2) : Case2ResidualRowIndex n S (J + 1) ~= endpoint row index,
e 0            : tau ~= endpoint column index
```

combine to a finite product equivalence

```text
Case2ResidualRowIndex n S (J + 1) x tau
  ~= AoyagiResidualBlockCoordinateIndex endpointRow endpointCol.
```

The raw-edge theorem already says that, after applying the endpoint source
chart to a determinant-chart source point, the reindexed raw fixed-base
residual block equals the source-side with-following product residual.  The
remaining step is only invariance of the finite coordinate square-sum under
that product equivalence:

```text
sum_(endpoint labels) rawResidual(endpoint)^2
  = sum_(case2 labels) rawResidual(e row, e col)^2
  = sum_(case2 labels) productResidual(row, col)^2.
```

This proves the pointwise equality between the fixed-base p.13 residual
square-sum of `sourceChart z` and the with-following product-residual
square-sum of `z`, under the determinant-chart hypothesis on the retained data.

The generic measure handoff is then a pure a.e. congruence.  If on a measurable
source set

```text
squareSum(fixedBaseResidual E) = squareSum(readbackProductResidual E)
```

and the negative-power readback-product-residual integral is finite there, then
the fixed-base residual negative-power predicate
`residualNegPowerIntegrableOn` holds on the same set and measure.  No
positivity, source coverage, prior identification, or loss comparison is
created by this congruence.

## Lean Target

Implemented in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean`:

```text
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_case2PassiveThetaWithFollowingFactorEndpointSourceChart_eq_of_detChart
```

Implemented in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductResidualBridge.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualNegPowerIntegrableOn_of_lintegral_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidual_eq
```

The new bridge is imported by `lean/DLNFibre.lean`.

## Check

Xhigh read-only scouts checked three independent aspects before integration.
`Aquinas` checked the pen-and-paper product calculation and found no
index/order mismatch: in the reverse endpoint convention the product is
`C_1 * C_0`.  `Confucius` recommended the residual-base handoff as the
smallest honest Lean target and warned not to state a `lossDLN` theorem at this
rung.  `Hume` identified the next local source-rank/rank-cut adapter but
confirmed that it is not analytic atlas coverage.

## Nonclaims

- No residual positivity theorem.
- No comparison from cleaned product residual to original `lossDLN`.
- No density upper/lower bound, adapted-product lower bound, or base alignment.
- No source-image coverage, source-rank coverage, or analytic atlas coverage.
- No statistical prior identification or source-prior transport.
- No determinant/raw Haar transport or Jacobian normalization.
- No normal crossings, pole order, or RLCT extraction.
- No assertion that singular following factors preserve the zero set; a later
  comparison needs explicit nondegenerate/full-rank following-factor
  hypotheses when that is the intended claim.
