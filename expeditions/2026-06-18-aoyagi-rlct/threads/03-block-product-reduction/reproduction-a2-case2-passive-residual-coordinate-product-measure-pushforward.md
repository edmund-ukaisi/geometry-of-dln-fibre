# Reproduction - A2 Case 2 Passive Residual-Coordinate Product-Measure Pushforward

Date: 2026-06-29.

## Source Slice

Aoyagi pp. 10-13 give the retained-passive Case 2 source coordinates and the
p.13 residual block produced from the selected-entry chart variables.  The
preceding Lean steps established:

- the passive source chart sends `(theta, y)` to an endpoint-transported
  fixed-base p.13 source family;
- the residual-coordinate map of that source family is the selected-entry
  chart map applied to `y`;
- the concrete passive-domain source measure is
  `passiveMeasure.prod weightedBox`, where `weightedBox` is the selected-entry
  signed-box measure with Aoyagi's source-density factor.

This reproduction records the residual-coordinate marginal of that
chart-produced product-domain measure.

## Claim to Formalise

Let

```text
sourceMeasure = passiveMeasure.prod weightedBox
mu = Measure.map sourceChart sourceMeasure
```

where

```text
weightedBox =
  signedBox.withDensity
    (fun y =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)).
```

Let `residualMap` be the fixed-base residual-coordinate readout, with
coordinates indexed through `residualCoordEquiv.symm`.  Then

```text
Measure.map residualMap mu
  =
passiveMeasure Set.univ •
  ((volume : Measure (center -> R)).restrict
    (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
      SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)).
```

The scalar `passiveMeasure Set.univ` is required.  If `passiveMeasure` is not a
probability measure, projecting the product measure to the selected-entry
factor multiplies the selected-entry marginal by the total passive mass.

## Calculation

The pointwise residual readout is

```text
residualMap (sourceChart (theta, y))
  = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext y.
```

Therefore the residual pushforward is

```text
Measure.map residualMap (Measure.map sourceChart sourceMeasure)
  =
Measure.map (fun z => CenterCoord.chartMap pivotNext z.2) sourceMeasure.
```

The right-hand map factors as

```text
CenterCoord.chartMap pivotNext o Prod.snd.
```

For a product measure, Mathlib gives

```text
Measure.map Prod.snd (passiveMeasure.prod weightedBox)
  =
passiveMeasure Set.univ • weightedBox.
```

Mapping the selected-entry chart across this scalar multiple gives

```text
Measure.map (CenterCoord.chartMap pivotNext)
  (passiveMeasure Set.univ • weightedBox)
  =
passiveMeasure Set.univ •
  Measure.map (CenterCoord.chartMap pivotNext) weightedBox.
```

The selected-entry signed-box theorem identifies the final pushforward:

```text
Measure.map (CenterCoord.chartMap pivotNext) weightedBox
  =
(volume : Measure (center -> R)).restrict
  (CenterCoord.chartMap pivotNext '' CenterCoord.signedBoxSet Rres).
```

Combining these equalities proves the claim.

## Dependency Boundary

The theorem uses:

- continuity of the passive source chart only to compose the first map through
  `Measure.map`;
- pointwise determinant-unit hypotheses only to define the passive source
  chart inside the determinant-chart subtype;
- `Measure.map_snd_prod`, whose `SFinite weightedBox` instance is supplied by
  the selected-entry weighted signed-box measure;
- no source-rank assumptions.

The theorem does not prove determinant-chart Haar pushforward, raw/source Haar
transport, original source-prior transport, passive Jacobian/source-density
accounting beyond the displayed product marginal scalar, source-rank coverage,
source-image equality, local inverse/coverage, normal crossings, pole order,
or RLCT.

## Expected Lean Target

```text
measure_map_residualBlockCoordinateMap_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_eq_smul_restrict_chartMap_image
```

