# Reproduction - A2 Case 2 reverse raw-source domination to source reference

Date: 2026-07-01.

## Claim

On the usual local Case 2 passive-theta raw-order/source-chart shrink, assume
the reverse raw-source domination

```text
rawHaar.restrict rawSourceSet
  <= D • Measure.map rawMap (thetaReference.restrict V).
```

Then the p.13 formal-product chart measure, restricted to any p.13 chart
piece, is dominated by the chart-produced source reference

```text
sourceRef := Measure.map sourceChart (thetaReference.restrict V).
```

Consequently, on any measurable p.13 chart piece, the restricted original
edge-family volume is dominated by the same source reference, with the inverse
p.13 Haar scalar:

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) • sourceRef.
```

This is not a proof of the reverse raw-source domination.  It is the exact
handoff from that missing lower-density/source-coverage comparison to the
existing original-volume/source-image finite-integral socket.

## Pen-And-Paper Check

Fix the local shrink `V` from the Case 2 two-stage theorem.  On this shrink the
raw-order chart and endpoint source chart satisfy, at the measure level,

```text
Measure.map rawChart (Measure.map rawMap (thetaReference.restrict V))
  = Measure.map sourceChart (thetaReference.restrict V).
```

The raw image of `thetaReference.restrict V` is supported in `rawSourceSet`.
Since the p.13 raw-order source chart is a.e. measurable on measures restricted
to `rawSourceSet`, it is also a.e. measurable for this raw image.  Mapping the
assumed reverse domination through `rawChart` gives

```text
Measure.map rawChart (rawHaar.restrict rawSourceSet)
  <= D • Measure.map rawChart
      (Measure.map rawMap (thetaReference.restrict V))
  = D • sourceRef.
```

The formal-product p.13 chart-measure identity says

```text
formalProductMeasure
  = (Measure.map rawChart (rawHaar.restrict rawSourceSet))
      .restrict p13SourceSet.
```

If `chartPiece subset p13SourceSet`, then restricting again gives

```text
formalProductMeasure.restrict chartPiece
  <= Measure.map rawChart (rawHaar.restrict rawSourceSet)
  <= D • sourceRef.
```

For a measurable chart piece, the p.13 original-volume bridge gives

```text
originalVolume.restrict chartPiece
  = cHaar^{-1} • formalProductMeasure.restrict chartPiece.
```

Composing the two dominations yields

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) • sourceRef.
```

## Boundary

The proof uses only measure functoriality, the already-formalized two-stage
source-chart identity, raw-image support in `rawSourceSet`, and the p.13
formal-product/original-volume scalar bridge.  It does not prove the reverse
raw-source domination, a bounded inverse Jacobian, determinant-chart Haar
transport, raw-Haar normalization, original source-prior transport,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
