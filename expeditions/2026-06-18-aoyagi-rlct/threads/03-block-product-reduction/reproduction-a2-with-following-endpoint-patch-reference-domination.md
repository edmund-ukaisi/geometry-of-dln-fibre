# Reproduction - A2 With-Following Endpoint-Patch Reference Domination

Date: 2026-07-07.

## Target

The latest formal-product and original-volume reference-source consumers still
take a determinant-side reverse domination hypothesis:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (referenceSource.restrict V).
```

For the actual p.13 chart-piece patch, the local theorem needed upstream is
slightly more precise.  Let

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece)
Omega_P = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

The goal is a local domination

```text
rawHaar.restrict Omega_P
  <= Cdet * Measure.map Y (referenceSource.restrict V)
```

with finite `Cdet`, assuming the chart piece is supported by the source-chart
image over the selected-entry source cylinder:

```text
chartPiece subset sourceChart '' (V inter sourceCylinder),
sourceCylinder = {z | z.1.yNext in signedBoxSet Rres}.
```

This is the determinant/reference input for the actual p.13/readback patch. It
is not a global determinant-chart Haar transport theorem.

## Source Calculation

Aoyagi's pp. 10-13 give the elementary block-coordinate algebra behind the
Case 2 p.13 source chart.  On the chosen determinant sector, the endpoint
theta coordinates give an endpoint tuple

```text
Y z.
```

The retained-passive raw-order map sends endpoint tuples to raw-order source
coordinates:

```text
rawOrderOnEndpoint y.
```

The p.13 raw chart then reads an edge-family point:

```text
rawChart (rawOrderOnEndpoint y).
```

The already established local source-chart package supplies, after shrinking:

```text
Y z in rawDetChart,
rawOrderOnEndpoint (Y z) in rawSourceSet,
rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z,
Y z = activeWriteback (activeChart z).
```

The last identity is the active selected-entry factorization: the endpoint
reference image is the active writeback of the selected-entry charted source
coordinates.  The measure theorem for this active chart is already proved in
Lean; Aoyagi's paper supplies the algebraic chart, not the global Haar
transport statement.

## Endpoint-Patch Containment

Take

```text
y in Omega_P.
```

Then

```text
y in rawDetChart,
rawOrderOnEndpoint y in rawSourceSet,
rawChart (rawOrderOnEndpoint y) in chartPiece.
```

By the chart-piece support hypothesis, choose

```text
z in V inter sourceCylinder
```

such that

```text
sourceChart z = rawChart (rawOrderOnEndpoint y).
```

For this same `z`, the local raw/source compatibility gives

```text
rawChart (rawOrderOnEndpoint (Y z)) = sourceChart z.
```

Thus the two raw-source points have the same p.13 raw-chart value:

```text
rawChart (rawOrderOnEndpoint y)
  = rawChart (rawOrderOnEndpoint (Y z)).
```

Both arguments lie in `rawSourceSet`, so injectivity of the p.13 raw chart on
`rawSourceSet` gives

```text
rawOrderOnEndpoint y = rawOrderOnEndpoint (Y z).
```

Both `y` and `Y z` lie in `rawDetChart`, so injectivity of the raw-order map on
`rawDetChart` gives

```text
y = Y z.
```

Finally

```text
Y z = activeWriteback (activeChart z),
```

and `z in V inter sourceCylinder`, hence

```text
Omega_P subset activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

## Measure Step

The active selected-entry endpoint theorem says that any endpoint patch
contained in this active writeback image is dominated by the named endpoint
reference image:

```text
rawHaar.restrict Omega_P
  <= Cdet * endpointReferenceImage.
```

By definition,

```text
endpointReferenceImage
  = Measure.map Y (referenceSource.restrict V).
```

Therefore

```text
rawHaar.restrict Omega_P
  <= Cdet * Measure.map Y (referenceSource.restrict V)
```

for a finite Haar-normalization scalar `Cdet`.

## Boundary

This proves only localized endpoint-patch domination for the concrete p.13 raw
patch whose chart piece is supported over the source cylinder.  It does not
prove full determinant-chart Haar transport, exact raw-Haar pushforward,
Haar-scalar normalization, source-density positivity, source-image coverage,
source-rank coverage, original-prior transport, normal crossings, pole order,
or RLCT extraction.
