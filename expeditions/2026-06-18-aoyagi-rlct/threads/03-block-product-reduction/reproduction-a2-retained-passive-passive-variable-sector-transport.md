# Reproduction - A2 Retained-Passive Passive-Variable Sector Transport

Date: 2026-06-29.

Status: controller pen-and-paper reproduction after xhigh scout round.  This
is a sector-transport specification and gap analysis, not a Lean theorem.

## Question

What concrete passive-variable sector has to be constructed before the
selected-entry Case 2 measure can remove a determinant-chart `hmap` field or
be compared with a source prior?

Answer: the sector must include all retained-passive variables, not only the
selected-entry residual coordinates.  The reduced selected-entry signed-box
measure is valid for chart-produced finite-integral theorems, but the
source-measure frontier needs a passive-variable-explicit domain, a source
map, an inverse or image theorem on a punctured pivot sector, and a measure
statement that names whether it is chart-produced, determinant-chart Haar, or
an external source prior.

## Source Equations

Aoyagi Lemma 2, pp. 10-11, starts from

```text
A = [ A1  A2
      A3  A4 ],
```

with `A1` invertible, and uses

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

Theorem 3, pp. 11-13, iterates this block substitution.  In the induction step

```text
C^(S+1) = -A3' (A1')^{-1} A2' + A4',
F2''    = -(A1')^{-1} A2',
F3''    = F3' - (prod_{s=1}^S C^(s)) A3' (C1' A1')^{-1}.
```

After Theorem 3, p.13 gives the product-difference display

```text
[ C1 - Er              -F2
  -F3       prod_s C^(s) - F3 F2 ].
```

The regular variables are `C1 - Er`, `F2`, and `F3`; the residual variable is
the corrected lower-right block `prod_s C^(s) - F3 F2`.  This correction is
load-bearing: a sector theorem must not replace it by `prod_s C^(s)`.

## Coordinate Domain

For the continuing Case 2 selected-entry chart in Lean, let

```text
center    = case2ResidualBlockPivotEntries n S (J+1),
pivotNext = (J+2, J+2) in center,
rho       = Fin (finrank R U0),
kappaRaw  = case2PostPivotTwoEdgeDomain n S J tau,
kappaEnd  = throughSubspaceEndpointComplementIndex (...).
```

The residual selected-entry coordinates are

```text
y : center -> R.
```

The passive retained variables are the fields suppressed by the reduced
selected-entry section:

```text
A1passive : Fin 1 -> Matrix rho rho,
F2        : forall p : Fin 2, Matrix rho (kappaRaw p.castSucc),
A3passive : forall p : Fin 1, Matrix (kappaRaw p.castSucc.succ) rho,
Ctop      : Matrix rho rho,
F3        : Matrix (kappaRaw (Fin.last 2)) rho.
```

The endpoint equivalences

```text
e : forall q : Fin 3, Equiv (kappaRaw q) (kappaEnd q)
```

are applied by `endpointTransport e`; the source chart and residual readback
then live over `kappaEnd`.

For source-map and support results the existing Lean interface allows these
to be continuous functions of an abstract passive parameter `theta : eta`.
For an exact sector-Haar theorem, however, `eta` must be replaced by the
finite product vector space of these matrix entries, with its product
Lebesgue/Haar measure.  An arbitrary passive measure can only produce an
arbitrary chart-produced measure.

The passive selected-entry coordinate domain is therefore

```text
Omega = Theta x (center -> R),
```

with `Theta` the finite product of the passive matrix-coordinate spaces.  A
local determinant sector is an open set

```text
Udet = { (theta,y) in Omega |
  IsUnit (Ctop(theta).det)
  and forall q : Fin 1, IsUnit ((A1passive(theta) q).det) }.
```

The determinant condition is independent of `y`.  No determinant condition is
imposed on the selected-entry residual coordinates.

## Source Map

Given `(theta,y)`, define the retained-passive datum by the existing Case 2
constructor:

```text
rawData(theta,y) =
  case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
    n hS hcont hnext
    (A1passive theta) (F2 theta) (A3passive theta)
    (Ctop theta) (F3 theta) y eNext.
```

Transport endpoints:

```text
data(theta,y) = endpointTransport e (rawData(theta,y)).
```

The determinant-chart theorem for this constructor says that if `Ctop(theta)`
and `A1passive(theta)` are determinant units, then `data(theta,y).detChart`.

Define the topology-tuple and source edge-family charts:

```text
Y(theta,y) = topologyTuple (data(theta,y)),

sourceChart(theta,y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (data(theta,y)).
```

The existing local source-readback theorem proves that on an open determinant
neighborhood of a base point, `sourceChart(theta,y)` lies in the
retained-passive p.13 local source and source readback recovers
`data(theta,y)`.  This is already enough for support of chart-produced
measures after restricting the coordinate-domain measure to the open set.

## Selected-Entry Residual Sector

The center-coordinate selected-entry map is

```text
chartMap pivotNext y pivotNext = y pivotNext,
chartMap pivotNext y i = y pivotNext * y i  for i != pivotNext.
```

Lean already has the inverse on the nonzero-pivot locus:

```text
preimageOfPivotNeZero pivotNext value i =
  if i = pivotNext then value pivotNext
  else value i / value pivotNext.
```

and the two inverse laws:

```text
chartMap pivotNext (preimageOfPivotNeZero pivotNext value) = value
  if value pivotNext != 0,

preimageOfPivotNeZero pivotNext (chartMap pivotNext y) = y
  if y pivotNext != 0.
```

Thus a genuine local inverse or image theorem for a fixed selected-entry
sector must use the punctured pivot condition

```text
y pivotNext != 0.
```

The full signed box includes the pivot-zero hyperplane.  That hyperplane is
harmless for the monomial integral and for a.e. statements, but the chart is
not injective there: if `y pivotNext = 0`, then `chartMap pivotNext y = 0`.
Therefore exact inverse/image statements must be made on the punctured sector,
or must explicitly work only up to a null set.

## Measure Candidates

There are three distinct measure statements.

### 1. Chart-produced passive sector measure

For an arbitrary passive measure:

```text
signedBox =
  Measure.pi (fun i : center => volume.restrict (-R_i, R_i)),

weightedBox =
  signedBox.withDensity
    (fun y => ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)),

sourceMeasure = passiveMeasure.prod weightedBox.
```

After an open determinant restriction `Udom`, and optional passive raw-order
Jacobian weighting

```text
J(theta,y) =
  retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y(theta,y)),

jacobianWeightedMeasure =
  (sourceMeasure.restrict Udom).withDensity (fun z => ofReal (J z)),
```

the source-side chart-produced measure is

```text
muJ = Measure.map sourceChart jacobianWeightedMeasure.
```

This is exactly the measure used by the current passive Case 2
finite-integral theorems.  It is not Haar on the determinant chart and not an
external source prior.

### 2. Passive-variable sector Haar transport

To remove a determinant-chart Haar `hmap` field, the passive parameter space
must be concrete finite-dimensional coordinate space `Theta`, not abstract
`eta`, and the theorem must compare a product coordinate measure with a
measure on a sector of the retained-passive determinant chart:

```text
Measure.map Y
  ((volume_Theta.prod weightedBox).restrict Udet
    with any required passive/selected-entry Jacobian density)
=
determinantChartHaar.restrict sectorSet
```

where

```text
sectorSet = Y '' Udet
```

or a measurable punctured-sector variant of it.  If the target is not the full
determinant chart, the statement must say so; a sector image is not the whole
determinant chart unless a separate coverage theorem proves it.

The selected-entry density accounts only for the residual selected-entry
chart.  The passive determinant-chart variables need their own Jacobian
factor, or at least a theorem that this factor is a bounded positive unit on a
chosen open neighborhood when only integrability equivalence is needed.

### 3. External source-prior comparison

An external or original DLN source prior is a separate input:

```text
externalPrior.restrict sourceNeighborhood
  is equal or mutually absolutely continuous to
Measure.map sourceChart sectorCoordinateMeasure.
```

No theorem in Aoyagi pp. 10-13 directly states this comparison, and current
Lean infrastructure does not prove it.  It must not be inferred from the
chart-produced measure.

## Existing Lean Pieces

Already available:

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive

exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
exists_open_measure_map_case2EndpointTransport_withPassive_withDensity_restrict_retainedPassiveP13LocalSource_eq_self

SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_value_of_case2EndpointTransport_sourceEdgeFamilyOfData_preimageOfPivotNeZero

exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_withDensity_jacobian_finiteMass_sourceStratum_bounds
```

These prove local source support, selected-entry residual chart density, a
non-passive punctured selected-entry readout package, a passive pointwise
chart-map readout package under determinant-unit hypotheses, and bounded-unit
passive Jacobian accounting for chart-produced passive measures.  The
with-passive endpoint residual-factor identity and the open source-readback
theorem give the ingredients for a passive-sector punctured readout package,
but that combined open-sector statement has not yet been named.  None of
these pieces proves passive-sector Haar transport or external source-prior
comparison.

## First Lean-Ready Subtarget

The broad measure transport theorem is not Lean-ready until `Theta`, the
sector set, and the target measure are fixed.  The first useful Lean subtarget
is the combined with-passive open punctured-sector inverse/readout package:

```text
for (theta,y) in Udet with y pivotNext != 0,
  sourceReadback(sourceChart(theta,y)) = data(theta,y)
  and
  selectedEntryPreimage(
    residualFactorProduct (sourceReadback(sourceChart(theta,y))).C)
  = y.
```

Equivalently, after reindexing residual block coordinates by the existing
`residualCoordEquiv`, the selected-entry inverse of the residual factor
product recovers the original `y` on the nonzero-pivot sector.

This subtarget should be a packaging theorem, not a fresh calculation from
zero: it combines `exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq`,
the with-passive endpoint residual-factor chart-map identity, and
`SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap`, with the
existing passive pointwise readout theorem
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive`
or its underlying residual-factor identity as the implementation bridge.  It
would not prove a measure theorem, but it is the missing passive-variable
open-sector inverse/image component needed before a passive-variable sector
transport theorem can be stated honestly.

## Transport Target Constraints

A later measure theorem may have one of the following shapes.

Chart-produced sector handoff:

```text
muSector =
  Measure.map sourceChart
    ((volume_Theta.prod weightedBox).restrict Udom
      withDensity passiveUnitOrJacobian)
```

with downstream consumers stated over `muSector`.

Sector Haar transport:

```text
Measure.map Y sectorCoordinateMeasure =
  determinantChartHaar.restrict sectorSet.
```

This requires a concrete finite-dimensional `Theta`, a sector image theorem,
and a Frechet/Jacobian determinant calculation for `Y`.

External source-prior comparison:

```text
externalPrior.restrict sourceNeighborhood
  <<>> Measure.map sourceChart sectorCoordinateMeasure.
```

This requires an explicit definition of `externalPrior` and a comparison
proof.  Aoyagi pp. 10-13 do not supply it as a standalone theorem.

## Kill Conditions

- Do not use the reduced selected-entry signed-box section to claim full
  determinant-chart Haar measure.
- Do not drop passive `A1`, tail `F2`, non-final `A3`, `Ctop`, or `F3` from a
  source-measure theorem.
- Do not call `SelectedEntrySignedBox.CenterCoord.sourceDensity` the passive
  determinant-chart Jacobian; it is the residual selected-entry Jacobian.
- Do not state a fixed-pivot inverse without the nonzero-pivot hypothesis or
  an explicit a.e. null-set qualification.
- Do not read Aoyagi p.13 as `prod C^(s)` in the lower-right block; it is
  `prod C^(s) - F3 F2`.
- Do not treat local support in the retained-passive p.13 local source as
  source-rank coverage or selected-entry image equality.
- Keep normal-crossing-to-RLCT extraction as the only cited analytic boundary.

## Current Verdict

The next substantial Lean implementation should not be another finite-integral
wrapper.  Either first prove the punctured-sector inverse/readout theorem, or
make `Theta` concrete and state the sector image and measure theorem with its
Jacobian fields explicit.  Until then, the chart-produced passive sector
measure remains a legitimate local measure for finite-integral handoffs but
not determinant-chart Haar and not an external source prior.
