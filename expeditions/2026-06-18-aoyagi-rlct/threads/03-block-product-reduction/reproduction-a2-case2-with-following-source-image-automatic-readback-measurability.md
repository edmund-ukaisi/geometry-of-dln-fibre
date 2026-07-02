# Reproduction - A2 Case 2 with-following source-image automatic readback measurability

Date: 2026-07-02.

Status: pen-and-paper reproduction for a local source-image bookkeeping
socket.  This note does not claim determinant-chart Haar transport, endpoint
Haar transport, raw-order Haar transport, source-prior identification,
source-image coverage, a Jacobian formula, normal crossings, pole order, or
RLCT extraction.

## Source Boundary

Aoyagi's Case 2 selected-pivot coordinate calculation, PDF pp. 19-21,
supplies the enlarged source coordinates.  The existing with-following local
source-chart package gives an open shrink `V` around a determinant-sector,
selected-pivot-nonzero point where:

```text
readback (sourceChart z) = z, for z in V,
sourceChart is injective on V,
sourceChart is continuous on V,
sourceChart '' V is measurable.
```

The extra following factor is carried by the chart as an ordinary coordinate;
the argument below uses only the local injective continuous chart and its
pointwise left inverse.

## Calculation

Let

```text
Theta = Case2PassiveThetaWithFollowingFactor ...
E = EdgeFamily
sourceChart : Theta -> E
readback : E -> Theta.
```

For a theta-domain reference measure `thetaReference`, restrict to the
measurable open set `V`.  On the subtype `V`, define

```text
sourceChartV : V -> E,
sourceChartV z = sourceChart z.
```

Because `sourceChart` is continuous and injective on the measurable set `V`,
Mathlib's measurable-embedding/Lusin-Souslin infrastructure gives

```text
MeasurableEmbedding sourceChartV.
```

To prove

```text
AEMeasurable readback
  (Measure.map sourceChart (thetaReference.restrict V)),
```

it is enough, after identifying the subtype pushforward with
`Measure.map sourceChart (thetaReference.restrict V)`, to prove
a.e.-measurability of

```text
readback o sourceChartV.
```

The pointwise left inverse gives

```text
readback (sourceChartV z) = z.val
```

on `V`, and the subtype inclusion `V -> Theta` is measurable.  Hence the
readback is a.e.-measurable for the chart-produced source-image reference.

Feeding this internally generated readback-measurability proof into the
generic bounded-density source-image pullback theorem gives:

```text
Measure.map readback
  (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict (sourceChart '' V))
<= c * thetaReference.restrict V
```

whenever the supplied density is locally bounded by `c` a.e. on the
chart-produced source-image reference restricted to `sourceChart '' V`.

## Checks

- The a.e. density bound remains an explicit hypothesis.  There is no
  external-measure density-identity hypothesis in this theorem; it starts
  directly from the chart-produced source-image reference with a supplied
  `withDensity`.
- The result concerns the actual local image `sourceChart '' V` only.
- The following factor introduces no additional measure-theoretic step in this
  argument.
- xhigh scout `Kepler the 2nd` identified this as an adjacent field-removal
  socket, not a source-prior or determinant-Haar frontier theorem.
