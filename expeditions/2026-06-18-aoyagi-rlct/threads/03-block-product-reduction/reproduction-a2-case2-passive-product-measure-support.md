# Reproduction - A2 Case 2 Passive Product-Measure Support

Date: 2026-06-29.

## Source Slice

Aoyagi pp. 10-13 give the retained-passive Case 2 source chart and the p.13
selected-entry residual product display.  The preceding Lean steps established:

- passive selected-entry source charts land pointwise in the retained-passive
  p.13 local source;
- arbitrary passive-domain chart-produced measures inherit this support when
  the source chart is a.e. measurable;
- the passive source chart is continuous under continuity of the passive
  fields.

The remaining elementary measure step is to name the concrete passive-domain
product measure and discharge the a.e. measurability input by continuity.

## Claim to Formalise

Let `passiveMeasure : Measure eta` be arbitrary.  On the selected-entry
coordinate side define

```text
signedBox =
  Measure.pi (fun i : center =>
    volume.restrict (Ioo (-(Rres i)) (Rres i)))

weightedBox =
  signedBox.withDensity
    (fun y =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
```

and on the passive chart domain define

```text
sourceMeasure = passiveMeasure.prod weightedBox.
```

If the passive fields `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3` are
continuous in `theta`, and the pointwise determinant-chart unit hypotheses for
`Ctop` and `A1passive` hold, then the chart-produced source measure

```text
mu = Measure.map sourceChart sourceMeasure
```

restricts to the retained-passive p.13 local source as itself.  Separately,
under the explicit a.e. successor-rank equation on this same `sourceMeasure`,
it restricts to the named source-rank stratum as itself.

There is also a pure domain-measure identity:

```text
passiveMeasure.prod (signedBox.withDensity selectedDensity)
  =
(passiveMeasure.prod signedBox).withDensity (fun z => selectedDensity z.2).
```

This identity records that the selected-entry density is on the second product
factor; it is not a source-side Jacobian theorem.

## Calculation

The product-density identity is exactly Mathlib's

```text
prod_withDensity_right_0
```

applied to the selected-entry density.  The density is a.e. measurable on the
signed box by the already-proved selected-entry monomial-density bounds.

For local-source support, the new continuity theorem gives

```text
Continuous sourceChart.
```

With `OpensMeasurableSpace eta` and `BorelSpace EdgeFamily`, Mathlib turns this
into

```text
AEMeasurable sourceChart sourceMeasure.
```

The arbitrary passive chart-produced support theorem then applies directly to
the concrete `sourceMeasure`.

For source-rank support, the same a.e. measurability proof is used, but the
successor-rank equation remains an explicit a.e. hypothesis:

```text
forall^ae z in sourceMeasure,
  r + rank(case2SuccessorSelectedEntryMatrix z.2) = rEdge 1.
```

The arbitrary passive source-rank support theorem then applies.

## Dependency Boundary

The theorem should carry:

- arbitrary `passiveMeasure : Measure eta`;
- no positivity hypothesis on `Rres`, since no integrability or nonzero-volume
  statement is being proved;
- continuity hypotheses for `A1passive`, `F2`, `A3passive`, `Ctop`, and `F3`;
- pointwise determinant-chart unit hypotheses on `Ctop` and `A1passive`;
- `BorelSpace EdgeFamily`, needed only to turn continuity into
  a.e. measurability;
- for source-rank support only, explicit `hprod`, `hr0`, and a.e. successor
  rank.

This does not prove source-rank coverage, source-image equality, determinant-
chart pushforward, passive Jacobian/source-density accounting, original
source-prior transport, normal crossings, pole order, or RLCT.

## Expected Lean Targets

```text
case2PassiveDomainProductMeasure_eq_prod_withDensity_sourceDensity
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_passiveProductMeasure_restrict_sourceRankStratum_eq_self
```
