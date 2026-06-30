# Construction Card - A2 post-5c source-prior/full-image frontier

Date: 2026-06-30.

Status: controller construction card after commit `5c113254`.  No Lean theorem
is claimed here.

## Question

After the passive-theta endpoint-sector and raw-order package, what remains
before the A2 finite-integral results can be read as statements about the
original DLN source/prior rather than about a chart-produced passive measure?

Answer: the chart-produced retained-passive measure path is already developed.
The next non-wrapper target is a bridge from an external/original local source
measure, or a full local source image theorem, into that chart-produced path.

## Current Lean Inputs

The following local coordinate and support pieces are already present.

```text
RetainedPassiveCase2PassiveThetaSourceMeasure.lean
  case2PassiveThetaEndpointSourceChart
  exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
  exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
  exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
  exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext

RetainedPassiveCase2LocalJacobianMeasure.lean
  retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive
  case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
  continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport_withPassive
  measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
  measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds

RetainedPassiveLocalJacobianMeasure.lean
  measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_restrict_detChart_eq_map_rawOrderSourceChart_withDensity_inverseJacobian
  residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian
```

These inputs prove coordinate-domain, readback, local injectivity,
measurable-image, source/support, chart-produced measure support, and local
Jacobian boundedness facts.  They do not identify any external original prior
with the chart-produced passive measure.

## Pen-And-Paper Check

Aoyagi pp. 10-13 give the elementary block substitution

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C  = A4 - A3 A1^{-1} A2
```

and its product-reduction iteration.  These formulas justify the local
coordinate transformations and the p.13 product-difference display.  The Lean
development has already turned this into the retained-passive source chart,
its readback, and chart-produced passive measure handoffs.

The missing bridge is different.  Let `x` denote an original fixed-base source
edge family near the base chain, and let `theta` denote retained-passive
coordinates.  The existing chart-produced measure is built from a passive
domain measure and selected-entry residual signed box:

```text
passiveMeasure.prod weightedBox
```

then pushed forward by the retained-passive source chart.  An original local
DLN/source prior is instead a measure on edge-family coordinates.  To compare
them one needs either:

```text
x = sourceChart theta
```

locally with a measurable inverse and controlled Jacobian density, or a direct
absolute-continuity/domination theorem between the restricted original source
measure and the chart-produced pushforward.  This comparison is not a
consequence of the p.13 residual algebra alone.

Thus passive variables are already accounted for as harmless chart variables
inside the chart-produced path.  What remains is not more passive bookkeeping;
it is source-prior transport or full local image coverage.

## Smallest Non-Wrapper Lean Targets

Target A, local image/inverse:

```text
exists_open_subset_sourceRankStratum_subset_range_case2PassiveThetaEndpointSourceChart
```

Expected content: for a fixed-base base point and endpoint data, find an open
source neighborhood `U` such that every `E` in
`U inter paperEndpointFixedBaseSourceRankStratum ...` is `sourceChart theta`
for some determinant-sector, nonzero-pivot `theta` in the local passive-theta
domain, with the readback/inverse recovering `theta`.

Target B, original-prior domination:

```text
exists_open_originalSourceMeasure_restrict_le_smul_case2PassiveThetaChartProducedMeasure
```

Expected content: for a named original/source measure `m` on fixed-base edge
families, prove on a local source neighborhood that

```text
m.restrict U <= C • Measure.map sourceChart chartDomainMeasure
```

or the corresponding two-sided bounded-density statement.  The theorem must
not define `m` to be the right-hand side.

Target C, determinant/raw-order Haar transport:

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_chartMeasure_eq_restrict_detChartHaar
```

Expected content: identify the passive-theta topology tuple map with a
determinant/raw-order Haar measure interface using the already-proved
raw-order Jacobian density.  This is only useful if the source-side original
measure is already expressed in that Haar chart.

## Kill Conditions

- Do not add a theorem that only repackages `Measure.map sourceChart
  (sourceMeasure.restrict V)` for an arbitrary `sourceMeasure`.
- Do not call a chart-produced passive product measure the original source
  prior unless an explicit density or equality theorem proves it.
- Do not derive full raw-Haar transport from the reduced p.13 section; the
  section fixes raw variables and is lower-dimensional in positive rank.
- Do not count a local finite-integral theorem as closing the source-prior
  frontier if its measure is still chart-produced.
- Keep normal-crossing-to-RLCT extraction as the cited analytic boundary.

## Controller Decision

The next Lean work should attack Target A first if the source-rank local image
statement can be made precise from `sourceReadback`; otherwise attack Target B
as a bounded-density handoff with the external source measure explicit.  Target
C is only appropriate after confirming which Haar chart the intended original
source prior is expressed in.

## Addendum - 2026-06-30 compatibility audit

Three xhigh scouts checked Target A after the passive-theta source-rank support
commit.  The broad source-rank local-image statement is too strong as written:
`paperEndpointFixedBaseSourceRankStratum` does not imply source-recursive
determinant-chart membership, selected-entry/pivot compatibility, or a
canonical projective lift through the Case 2 blow-up center.

The Lean theorem now proved instead is:

```text
case2PassiveThetaEndpointSourceChart_readback_eq_and_rightInverse_of_sourceReadback_eq_retainedData
```

It gives two-sided reconstruction for a source edge family already in the
retained-passive determinant source chart, assuming its `sourceReadback` is
the selected Case 2 passive-theta endpoint datum and its selected-entry inverse
readout is `theta.yNext`.

Revised Target A is therefore not source-rank coverage.  It is to derive those
compatibility hypotheses from honest source-side lifted-chart assumptions.  If
that is not available, move to Target B with an explicit external/source
measure and a non-vacuous domination hypothesis.
