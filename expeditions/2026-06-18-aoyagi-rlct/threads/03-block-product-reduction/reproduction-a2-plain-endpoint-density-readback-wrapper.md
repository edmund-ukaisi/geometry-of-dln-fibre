# A2 Plain Endpoint Density Readback Wrapper

Date: 2026-07-03.

## Local Calculation

Work in the plain `Case2PassiveTheta` source coordinates, not in the enlarged
with-following source.  The existing readback theorem already proves that
restricted original edge-family volume is dominated by the coordinate source
measure once a local determinant-side domination input is supplied:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map endpointTuple (passiveSource.restrict V).
```

The first Lean landing step uses this full determinant-chart socket directly.
Assume the actual endpoint image of the finite passive product source has a
weighted-Haar presentation on the full determinant chart:

```text
Measure.map endpointTuple (passiveSource.restrict V)
  = (rawHaar.restrict rawDetChart).withDensity Jprod,
```

and assume

```text
Cdet < infinity,
for a.e. y with respect to rawHaar.restrict rawDetChart,
  1 <= Cdet * Jprod(y).
```

The density-domination lemma gives exactly the determinant socket:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map endpointTuple (passiveSource.restrict V).
```

Together with the unchanged source-density lower bound

```text
epsilon <= sourceDensity(z)
```

on the returned shrink, the existing readback theorem gives

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= (((cHaar^{-1}) * (Cdet * epsilon^{-1}))
        * coordinateSourceMeasure.restrict G).
```

This full-chart version is stronger than Aoyagi's local patch calculation, but
it is a sound decomposition of the existing Lean theorem and keeps the endpoint
image identity explicit.  It is a readback-domination theorem only; the
finite-integral theorem can consume it later, but is not restated here.

## Patch-Local Target

For a measurable chart piece

```text
chartPiece subset sourceLocal,
chartPiece subset sourceChart '' V,
```

the natural p.13 endpoint patch is more precise than all of `rawDetChart`.
Set

```text
P = rawSourceSet inter p13SourceChart^{-1}(chartPiece),
Q = rawDetChart inter rawOrderOnEndpoint^{-1}(P).
```

Assume explicitly the endpoint reference image identity on this patch:

```text
endpointReferenceImage
  = (rawHaar.restrict Q).withDensity Jprod.
```

The generic density-domination lemma gives

```text
rawHaar.restrict Q <= Cdet * endpointReferenceImage.
```

The plain endpoint reference image is

```text
endpointReferenceImage = Measure.map endpointTuple (referenceSource.restrict V).
```

The existing finite passive-product theorem, however, consumes

```text
passiveSource = passiveMeasure.prod weightedBox.
```

Therefore the future patch-local wrapper must keep the passive-source
comparison visible with the correct domination direction:

```text
endpointReferenceImage
  <= d * Measure.map endpointTuple (passiveSource.restrict V).
```

In the intended reference case `d = 1`; for a non-reference passive measure,
this is a lower-domination assumption on the passive source, not a consequence
of an upper bound by the reference source.

## Boundary

The landed full-chart wrapper does not prove the endpoint image identity,
determinant-density lower bound, source-density lower bound, source-image
coverage, source-rank coverage, passive-source comparison, original-prior
transport, normal crossings, pole order, or RLCT extraction.  It also does not
prove the more precise p.13 patch-local endpoint theorem or the finite-integral
corollary.
