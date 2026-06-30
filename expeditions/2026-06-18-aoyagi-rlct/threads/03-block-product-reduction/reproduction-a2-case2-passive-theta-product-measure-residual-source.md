# Reproduction - A2 Case 2 passive theta product-measure residual-source adapter

Date: 2026-06-30.

Status: pen-and-paper check completed before the theta-specific Lean
product-measure residual-source adapter.

## Question

After the arbitrary-measure theta adapter, what can be proved for the concrete
product-style theta measure

```text
sourceMeasure = passiveMeasure.prod weightedBox
```

on

```text
Case2PassiveTheta = Case2PassiveTheta.PassiveFields × (center -> R)?
```

The goal is not determinant-chart Haar transport.  The useful next statement
is that the chart-produced source measure on the returned punctured sector
already satisfies the residual-source positivity and finite negative-power
integrability hypotheses, provided the passive factor has finite mass and the
selected-entry critical inequality holds.

A second useful variant keeps an arbitrary theta-domain source measure but
requires explicit local finite-scalar domination by the passive-product
measure after the sector `V` is chosen.

## Product Measure

Let

```text
center = case2ResidualBlockPivotEntries n S (J+1),
pivotNext = (J+2,J+2) in center.
```

For radii `Rres : center -> R`, define

```text
signedBox =
  Measure.pi (fun i : center =>
    volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
```

and

```text
weightedBox =
  signedBox.withDensity
    (fun y : center -> R =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)).
```

For a passive-fields measure

```text
passiveMeasure : Measure Case2PassiveTheta.PassiveFields
```

set

```text
sourceMeasure = passiveMeasure.prod weightedBox.
```

This is still a coordinate-domain measure.  It is not identified with a
determinant-chart Haar measure or with the original DLN source prior.

## Marginal Calculation

The arbitrary theta adapter returns an open punctured determinant-sector
neighborhood `V` around the base theta point and a chart-produced source
measure

```text
mu = Measure.map sourceChart (sourceMeasure.restrict V).
```

The residual-source socket needs positivity and finite integrability for the
selected residual marginal

```text
Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V).
```

Because restriction is monotone and `Case2PassiveTheta.yNext` is the second
projection on the product theta domain,

```text
Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V)
  <= Measure.map Case2PassiveTheta.yNext sourceMeasure.
```

For the product measure,

```text
Measure.map Case2PassiveTheta.yNext sourceMeasure
  = passiveMeasure Set.univ • weightedBox.
```

Therefore

```text
Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V)
  <= passiveMeasure Set.univ • weightedBox.
```

This is the correct local conclusion.  Exact equality after restriction would
require additional product-saturation information about `V`; the punctured
determinant sector returned by the local theorem is not proved to have that
form.

## Local Domination Variant

For an arbitrary theta-domain measure `sourceMeasure`, define the same
passive-product comparison measure

```text
passiveSource = passiveMeasure.prod weightedBox.
```

The local theorem returns the same kind of open punctured sector `V` and leaves
the comparison as an explicit post-sector hypothesis:

```text
sourceMeasure.restrict V <= c • passiveSource,
c < infinity.
```

Under this assumption, mapping by `Case2PassiveTheta.yNext` gives

```text
Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V)
  <= c • Measure.map Case2PassiveTheta.yNext passiveSource
  = c • (passiveMeasure Set.univ • weightedBox).
```

Thus a.e. residual positivity and finite negative-power integrability transfer
from `weightedBox` to the restricted `yNext` marginal.  The residual-source
socket then gives the same source-side positivity and
`residualNegPowerIntegrableOn` conclusion for the chart-produced measure.

This is a domination wrapper.  It does not construct the domination hypothesis
from an original source prior or a determinant-chart Jacobian.

## Residual-Source Transfer

The selected-entry signed-box calculation supplies

```text
forall^ae y in weightedBox,
  0 < SelectedEntrySignedBox.CenterCoord.residual pivotNext y
```

and

```text
lintegral weightedBox
  (fun y => ENNReal.ofReal ((residual pivotNext y) ^ (-t))) < infinity
```

under

```text
0 <= t,
forall i, 0 < Rres i,
2*t < card(center.erase (J+2,J+2)) + 1.
```

If `passiveMeasure Set.univ < infinity`, the scalar domination above transfers
both the a.e. positivity and the finite lower integral to the restricted
`yNext` marginal.  The already-proved chart-produced residual-source socket
then gives:

```text
mu.restrict localSource = mu,
forall^ae E in mu.restrict localSource,
  0 < aoyagiCoordinateSquareSum (residualCoordinateMap E),
residualNegPowerIntegrableOn localSource mu t.
```

## Source Boundary

Aoyagi pp. 10-13 support the retained-passive p.13 coordinate/source chart, and
pp. 19-22 support the Case 2 selected-entry residual calculation.  The present
step is Lean measure bookkeeping over already formalized finite
selected-entry signed-box estimates.  It uses no quiver-paper evidence and no
new cited theorem.

## Nonclaims

This slice does not prove exact restricted `yNext` marginal equality,
determinant-chart Haar transport, raw-order Haar transport, source-prior
transport, exact passive-sector pushforward, source-image equality,
source-rank coverage, finite-integral transfer for the original source prior,
normal crossings, pole order, or RLCT extraction.
