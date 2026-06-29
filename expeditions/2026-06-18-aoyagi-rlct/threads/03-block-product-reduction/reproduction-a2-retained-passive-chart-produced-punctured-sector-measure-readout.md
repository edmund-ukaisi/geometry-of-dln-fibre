# Reproduction - A2 Retained-Passive Chart-Produced Punctured-Sector Measure Readout

Date: 2026-06-29.

Status: Lean theorem landed; focused and full builds passed; hygiene and
axiom probes passed; xhigh review PASS.  This is a chart-produced measure
theorem only; it is not a determinant-chart Haar or external source-prior
theorem.

## Question

The open punctured-sector readout theorem proves a pointwise inverse identity.
What is the strongest honest measure theorem that follows from it without
constructing determinant-chart Haar transport or an Aoyagi original-prior
comparison?

Answer: restrict an arbitrary coordinate-domain measure to the open
determinant-and-pivot-nonzero sector, push it forward by the retained-passive
p.13 source chart, and then push that source measure by the inverse residual
readout.  The resulting measure is exactly the second-coordinate marginal of
the same restricted coordinate-domain measure.

This is a chart-produced theorem:

```text
source-side measure =
  Measure.map sourceChart (sourceMeasure.restrict V)
```

where `sourceMeasure` is a measure on the passive-variable and residual
coordinate domain.  The theorem is allowed to specialize later to

```text
passiveMeasure.prod
  (signedBox.withDensity selectedEntrySourceDensity)
```

or to a further Jacobian-weighted chart-produced measure.  It does not identify
that measure with determinant-chart Haar or with Aoyagi's original Bayesian
prior.

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive coordinate algebra.  For a block
matrix

```text
A = [ A1  A2
      A3  A4 ],
```

with `A1` invertible, Lemma 2 uses

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = -A3 A1^{-1} A2 + A4.
```

Theorem 3 iterates this substitution, and the p.13 product-difference block is

```text
prod_s C^(s) - F3 F2.
```

The same pages do not state selected-entry determinant-chart coverage,
passive-sector Haar transport, or source-prior transport.  Aoyagi's Bayesian
prior density is an external smooth positive density on the full parameter
space; turning it into a retained-passive coordinate theorem would require a
separate local chart/Jacobian comparison.  That comparison is not part of this
measure-readout target.

## Coordinate Domain

Keep the passive variables explicit.  In the continuing Case 2 selected-entry
chart, write

```text
center    = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) in center
z         = (theta, y) : eta x (center -> R)
```

with passive fields

```text
A1passive theta
F2 theta
A3passive theta
Ctop theta
F3 theta
```

and retained-passive datum

```text
retainedData z =
  endpointTransport e
    (case2PostPivotSelectedEntryRetainedPassiveDataWithPassive
      n hS hcont hnext
      (A1passive theta) (F2 theta) (A3passive theta)
      (Ctop theta) (F3 theta) y eNext).
```

The source chart is

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z).
```

The existing open source-readback theorem supplies an open determinant-domain
neighborhood `Udet` of a base point `z0` such that, for all `z in Udet`,

```text
sourceChart z in retainedPassiveP13LocalSource
sourceReadback (edgeMatrix (sourceChart z)) = retainedData z.
```

For a measure-level inverse statement, impose the basepoint and sector
hypothesis

```text
z0.2 pivotNext != 0
```

and work on the open punctured sector

```text
V = Udet inter {z | z.2 pivotNext != 0}.
```

The set is open because the pivot coordinate is continuous and `{x | x != 0}`
is open in `R`.

## Residual Inverse Readout

Let `E(source)` be the fixed-base edge-matrix family associated to a source
edge family.  Define the source-side residual inverse readout by

```text
inverseReadout X =
  SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
    (fun i : center =>
      AoyagiResidualBlockCoordinateIndex.value
        (residualFactorProduct
          (sourceReadback (E X)).C
          (Fin.last 2) 0)
        (residualCoordEquiv.symm i)).
```

The open punctured-sector theorem proves pointwise, for every `z in V`,

```text
inverseReadout (sourceChart z) = z.2.
```

This is exactly the identity needed for the measure pushforward.  It uses the
residual-factor identity from the with-passive endpoint chart and

```text
SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
```

under the pointwise pivot condition `z.2 pivotNext != 0`.

## Measure Calculation

Let

```text
nu = sourceMeasure.restrict V
mu = Measure.map sourceChart nu.
```

The already-proved support theorem also gives

```text
mu.restrict retainedPassiveP13LocalSource = mu,
```

because `sourceChart z` lies in the retained-passive p.13 local source for all
`z in V`.

For the inverse readout,

```text
Measure.map inverseReadout mu
  = Measure.map inverseReadout (Measure.map sourceChart nu)
  = Measure.map (inverseReadout o sourceChart) nu
  = Measure.map Prod.snd nu.
```

The first equality is definitional.  The second is Mathlib's map-map theorem
for measurable or a.e.-measurable maps.  The last equality is `Measure.map_congr`
using the pointwise identity on `V`, hence almost everywhere for
`sourceMeasure.restrict V`.

The measurability obligations are finite-coordinate bookkeeping:

- `sourceChart` is a.e. measurable on `nu` because it is continuous on the
  determinant-domain open set used by the support theorem.
- `inverseReadout` is measurable once the fixed-base edge-matrix construction,
  residual-coordinate map, and `preimageOfPivotNeZero` are measurable.
- `preimageOfPivotNeZero` is measurable coordinatewise: at the pivot it is an
  evaluation map, and away from the pivot it is a quotient of evaluation maps.

## Lean Target

The landed theorem is in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean
```

with name

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

It returns an open set `V`, `z0 in V`, local-source support for the
chart-produced source pushforward, and the inverse-readout pushforward
identity:

```text
Measure.map inverseReadout
  (Measure.map sourceChart (sourceMeasure.restrict V))
=
Measure.map Prod.snd (sourceMeasure.restrict V).
```

The theorem may be stated for an arbitrary coordinate-domain measure
`sourceMeasure`; the passive product signed-box measure is then a direct
specialization.

A small selected-entry helper was also added:

```text
SelectedEntrySignedBox.CenterCoord.measurable_preimageOfPivotNeZero
```

The main proof uses
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`
to avoid unfolding the suffix-state residual-coordinate map inside the
source-measure proof.

Post-recovery verification:

```text
scripts/lb DLNFibre
scripts/sorries
git diff --check
touched Lean-file forbidden-marker scan
direct axiom probes: [propext, Classical.choice, Quot.sound]
```

## Kill Conditions

- If the theorem mentions determinant-chart Haar or an original source prior,
  it is overclaiming.
- If the theorem omits the pivot-nonzero sector, the inverse-readout identity
  is false at the exceptional divisor.
- If it uses a reduced selected-entry signed-box measure to remove a full
  determinant-chart `hmap` field, it is overclaiming.
- If it asserts image coverage or source-rank coverage, it has left this
  calculation.

## Nonclaims

No determinant-chart Haar transport, raw/source Haar theorem,
external/original source-prior comparison, passive Jacobian formula,
selected-entry source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction is claimed here.
