# Statement card: A2 retained-passive canonical chart residual readout

## Lean names

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualProduct
paperEndpointFixedBaseResidualBlockCoordinateMap_retainedPassiveP13Canonical_chart_eq_residualFactorProduct
```

## Content

For a retained-passive determinant-chart tuple `z`, the residual coordinate map
which appears in the canonical chart-side handoff hypotheses,

```text
paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
  (sourceChart (topologyTupleEdgeRawOrder z)),
```

is identified with the coordinate readout of the deterministic suffix residual
product of `topologyTupleEdgeMatrix z`.  The stronger theorem rewrites the
same expression as the residual-factor product of the stored retained-passive
`C` blocks in `ofTopologyTuple z`.

The proof combines:

```text
mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
retainedPassiveP13CanonicalSourceChart_realize
edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
sourceReadback_edgeMatrix_eq
```

## Proved

Pointwise residual readout on the determinant chart for the canonical
retained-passive p.13 source chart.

## Assumed

The input tuple is in `topologyTupleDetChartSet`.  The theorem also carries the
fixed endpoint-base hypotheses already needed by the p.13 retained-passive
local-source setup.

## Cited

None.  This is finite coordinate and matrix-product bookkeeping.

## Deferred

Residual zero-locus/nullity analysis, chart-side a.e. positivity, finite
negative-power integrability, monomial lower bounds, normal-crossing
production, pole-order computation, original-prior/source-density transport,
and RLCT extraction.

## Verification

Focused `RetainedPassiveLocalJacobianMeasure` build passed.  Full `DLNFibre`
build passed with pre-existing warning noise.  `scripts/sorries`,
`git diff --check`, and the touched-file forbidden-marker search passed.

Xhigh review by `Zeno the 3rd` passed.

## Nonclaims

No chart-side residual positivity, residual integrability, selected-entry
signed-box density identification, original prior transport, normal-crossing
production, pole-order theorem, or RLCT theorem is claimed.
