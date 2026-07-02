# Reproduction - A2 Case 2 enlarged following-factor source readback

Date: 2026-07-02.

Status: pointwise source chart/readback for the enlarged following-factor
domain; no open-image theorem yet.

## Pen-and-Paper Check

For the enlarged source

```text
Case2PassiveThetaWithFollowingFactor = Case2PassiveTheta x F,
```

the source chart is the usual fixed-base retained-passive p.13 source chart
applied to the enlarged retained datum.  The readback cannot use the old
residual-product inverse.  With a free following factor,

```text
C(1) * C(0)
```

is generally the selected-entry residual block multiplied by the free
following factor, so it no longer determines the selected-entry center
coordinates.

The correct readback is:

```text
passive fields <- sourceReadback, transported back to the raw two-edge domain
yNext          <- selected-entry inverse applied to the raw C(1) matrix
F              <- raw C(0)
```

The `C(1)` matrix is the successor selected-entry matrix after reindexing its
columns by `eNext.symm`, so the nonzero-pivot selected-entry inverse recovers
`yNext`.  The `C(0)` matrix is the displayed following factor of
`case2DisplayedPostPivotFreeCprimeOfFollowingFactor F`, hence recovers `F`.

## Lean Slice

The new definitions are in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
```

with names

```text
case2PassiveThetaWithFollowingFactorEndpointSourceChart
case2PassiveThetaWithFollowingFactorEndpointCOneReadout
case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
```

The pointwise theorem is

```text
case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
```

It assumes:

- `sourceReadback` of the source edge family equals the endpoint retained data
  of the enlarged coordinate;
- the selected pivot coordinate of the underlying `Case2PassiveTheta` is
  nonzero.

It proves that the enlarged readback recovers the original enlarged coordinate.

## Nonclaims

No local open set, injectivity theorem, source-image measurability,
source-image coverage, measure pushforward, Jacobian density, normal-crossing
statement, pole order, or RLCT extraction is proved here.
