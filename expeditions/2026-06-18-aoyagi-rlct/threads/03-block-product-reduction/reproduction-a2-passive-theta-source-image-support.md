# Reproduction - A2 passive-theta source-image carrier and support

Date: 2026-06-30.

## Goal

After constructing a local passive-theta source-chart image

```text
sourceChart '' V,
```

record two elementary consequences:

1. `readback` is a right inverse to `sourceChart` on this image.
2. The corresponding pushed-forward theta-domain measure is supported on this
   image.

```text
(Measure.map sourceChart (thetaMeasure.restrict V)).restrict
  (sourceChart '' V)
= Measure.map sourceChart (thetaMeasure.restrict V).
```

This should remain image-support bookkeeping.  It should not say that the
image covers a source-rank stratum, that it is an original source prior, or
that any Haar/Jacobian transport has been identified.

## Calculation

The local left inverse says

```text
readback(sourceChart(theta)) = theta
```

for all `theta in V`.  Therefore if `E in sourceChart '' V`, choose
`theta in V` with `E = sourceChart(theta)`.  Then

```text
readback(E) = theta in V
sourceChart(readback(E)) = E.
```

This gives the target-carrier inverse statement; it uses only membership in
the already named local image.

Let `thetaMeasure` be any measure on the concrete passive-theta coordinate
domain and set

```text
nu = thetaMeasure.restrict V.
```

Since `V` is measurable, we have

```text
nu-a.e. theta, theta in V.
```

Therefore

```text
nu-a.e. theta, sourceChart theta in sourceChart '' V.
```

If `sourceChart '' V` is measurable and `sourceChart` is a.e. measurable with
respect to `nu`, the usual map-measure a.e. transfer gives

```text
Measure.map sourceChart nu-a.e. E, E in sourceChart '' V.
```

Restricting a measure to a measurable set that contains it almost everywhere
does not change the measure, so

```text
(Measure.map sourceChart nu).restrict (sourceChart '' V)
  = Measure.map sourceChart nu.
```

For the concrete Case 2 passive-theta source chart, the previous local image
proof already shrinks `V` inside the determinant-chart preimage.  On this
`V`, the source chart factors continuously as

```text
theta |-> retainedData(theta)
      |-> determinant-chart subtype
      |-> fixed-base retained-passive p.13 source chart.
```

Thus `sourceChart` is continuous on `V`, hence a.e. measurable with respect to
`thetaMeasure.restrict V`.  The same shrink also has the source-readback left
inverse and injectivity, and Lusin-Souslin gives `MeasurableSet (sourceChart ''
V)`.

## Boundary

This proves only support of a chart-produced pushforward on its own local
chart image and a right inverse on that same image.  It does not prove
source-rank coverage, source-image equality with any larger stratum, original
source-prior transport, determinant-chart or raw-order Haar transport, normal
crossings, pole order, or RLCT.
