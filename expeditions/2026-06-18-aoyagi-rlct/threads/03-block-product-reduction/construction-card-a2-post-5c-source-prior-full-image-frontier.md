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

## Addendum - 2026-06-30 post-product-source-support audit

After commit `2e8e23dd`, the concrete Case 2 product source chart has both:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_productReductionCertificate_nhdsWithin_source

exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_retainedPassiveP13LocalSource_nhdsWithin_source
```

These close product-chart certificate/support obligations for constructed
points.  They do not change the source-prior/full-image frontier: the chart
point is in the named local source, but no theorem says an arbitrary nearby
source-rank point is produced by the Case 2 passive-theta chart, and no theorem
identifies an original/external source prior with the chart-produced source
measure.

Two xhigh scouts rechecked the frontier.

Image/coverage verdict: genuine `Case2PassiveTheta` source-rank coverage is
not currently feasible from source-rank membership alone.  The missing
source-side field is the readback-shape compatibility

```text
sourceReadback E =
  case2PassiveThetaEndpointRetainedData ... theta ...
```

for `theta = case2PassiveThetaEndpointSourceChartReadback ... X`, together
with the selected-entry inverse-readout equality.  Equivalently, after
endpoint transport the residual factors must be the canonical Case 2
selected-entry factors attached to `theta.yNext`.  Source-rank membership and
retained-passive local-source membership do not imply that selected-entry
factorization.

The honest theorem extracted from this audit is retained-passive rather than
passive-theta:

```text
exists_open_paperEndpointFixedBaseRetainedPassiveP13SourceChart_image_coverage_of_selfBase
```

It exposes a determinant-chart coordinate datum whose retained-passive source
chart realizes `Cedge x` on the existing self-base retained-passive local
source neighborhood.  This is useful image-witness bookkeeping, but it is not
Case 2 selected-entry coverage.

Measure/prior verdict: current measure APIs still only consume a bounded
density transport statement.  The landed source-level handoff asks for

```text
externalSourceMeasure.restrict sourceLocal =
  (sourceImageMeasure.withDensity externalDensity).restrict sourceLocal

externalDensity <= Cext
  a.e. with respect to sourceImageMeasure.restrict sourceLocal
```

and then proves the finite-integral conclusion.  The missing theorem is
precisely the original/external source-measure local bounded-density transport
over the Case 2 chart-produced source image, or an equivalent Haar/Jacobian
transport theorem.  It is not supplied by `withDensity` bookkeeping,
local-source support, or product-reduction certificates.

## Addendum - 2026-06-30 product-source measure support wrapper

The pointwise product source-chart support theorem has been lifted to a
chart-produced product-measure support wrapper:

```text
exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_retainedPassiveP13LocalSource_eq_self
```

For arbitrary theta-domain and regular-coordinate measures, after restricting
to the chosen open theta neighborhood, source-rank carrier, and regular ball,
the pushforward through the concrete product source chart restricts to the
retained-passive local source as itself.

This removes only a chart-produced support bookkeeping obligation. It does
not change the frontier conclusion above: original/external source-measure
comparison, source-image equality, and Haar/Jacobian transport remain open or
explicit theorem inputs.

## Addendum - 2026-06-30 post-dev-merge source-prior inventory

After merging current `origin/dev` into the expedition branch, an xhigh scout
rechecked the exact Lean measure inventory.  No current declaration defines a
source-side original DLN prior measure independently of a chart pushforward.

The closest objects are:

```text
RetainedPassiveCase2PassiveThetaProductMeasure.lean
  passiveSource := passiveMeasure.prod weightedBox

RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
  baseJ := passiveSource.withDensity jacobianDensity
  sourceMeasure := baseJ.withDensity sourceDensity

RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
  sourceImageBase := Measure.map sourceChart (baseJ.restrict W)
  sourceImageMeasure := sourceImageBase.withDensity sourceImageDensity

RetainedPassiveLocalJacobianMeasure.lean
  measure_map_paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_...
```

All four are coordinate-side, chart-produced, or chart-layer change-of-
variables statements.  `OriginalLossSourceMeasure.lean` and
`OriginalLossLocalMeasure.lean` still consume arbitrary `μ`, `ν`, and density
hypotheses; they do not construct the original source measure.

Thus the sharpened theorem target is a named external/original source measure
with local comparison to the chart-produced reference:

```text
originalSourcePrior.restrict (sourceChart '' W) <=
  Csrc • Measure.map sourceChart (baseJ.restrict W)
```

or a bounded-density equality over the same image.  The theorem must not
define `originalSourcePrior` to be the right hand side.  Aoyagi pp. 10-13
support the Schur/product algebra already formalized; pp. 5 and 8 support
local boundedness of a smooth positive prior after a valid coordinate-change
identity is present, not the project-specific identity itself.

## Addendum - 2026-06-30 original coordinate prior and density adapter

Lean now names the flattened ambient original coordinate measure:

```text
originalCoordinateVolume
originalCoordinatePrior
originalCoordinatePrior_restrict_le_smul_of_ae_le
```

This lives on `RepCoord d -> ℝ`, the canonical matrix-entry coordinate space,
and is independent of retained-passive chart pushforwards.

Lean also proves the generic adapter from unweighted local domination to
prior-weighted local domination:

```text
restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le
```

The theorem says that if

```text
μ.restrict s <= c • ν
```

and the prior density is locally bounded on `s`, then

```text
(μ.withDensity f).restrict s <= (C * c) • ν.
```

This is useful because Aoyagi's smooth compactly supported prior contributes
only local boundedness after a legitimate coordinate transport theorem has
been proved.  The new definitions and adapter do not prove that transport
theorem; they sharpen the remaining source-prior frontier to transporting the
flattened original-coordinate measure through the Aoyagi source chart and
comparing it with the retained-passive chart-produced reference.
