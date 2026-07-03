# A2 Endpoint Density Readback Wrapper

Date: 2026-07-03.

## Local Calculation

Fix the same local shrink `V` already produced by the localized readback theorem.
For a measurable chart piece `chartPiece subset sourceChart '' V`, set

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece)
Q = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

The p.13 source-chart measurability lemma gives

```text
P subset rawSourceSet,
NullMeasurableSet Q rawHaar.
```

Assume, explicitly, the endpoint reference image identity on this endpoint
patch,

```text
endpointReferenceImage = (rawHaar.restrict Q).withDensity Jprod,
```

where

```text
Jprod(y) =
  ofReal(retainedPassiveFormalRawOrderJacobianProductAbsDetAt(y)).
```

Also assume the finite scalar and lower-density bound

```text
Cdet < infinity,
for a.e. y with respect to rawHaar.restrict Q,
  1 <= Cdet * Jprod(y).
```

The generic density-domination lemma gives

```text
rawHaar.restrict Q <= Cdet * endpointReferenceImage.
```

In this local naming, `endpointReferenceImage` is exactly

```text
Measure.map Y (referenceSource.restrict V).
```

Thus the determinant-side socket required by the existing localized
original-volume readback theorem is filled.  Feeding that domination and the
unchanged source-density lower bound into the existing theorem gives the same
readback conclusion:

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= (((cHaar^{-1}) * (Cdet * epsilon^{-1}))
        * coordinateSourceMeasure.restrict G).
```

## Boundary

This wrapper does not prove the endpoint reference image identity, the lower
bound for `Jprod`, the source-density lower bound, or the `epsilon` side
conditions; all remain explicit hypotheses.  It does not identify a determinant
chart with the active image, normalize any Haar scalar to `1`, prove raw-Haar
transport, original-prior transport, source-image coverage, normal crossings,
pole order, or RLCT extraction.
