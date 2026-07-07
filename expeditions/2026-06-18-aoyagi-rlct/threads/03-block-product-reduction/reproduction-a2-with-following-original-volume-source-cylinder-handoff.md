# A2 With-Following Original-Volume Source-Cylinder Handoff

Date: 2026-07-07.

## Target

Consume the source-cylinder formal-product domination theorem at the p.13
original-volume interface.

The intended Lean theorem takes a measurable chart piece satisfying

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

and a lower source-density bound on the same theta shrink, then returns a
finite scalar such that

```text
originalVolume.restrict chartPiece
  <= Dvol * Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Here

```text
Ddet = Cdet * eps^-1
Dvol = ((cHaar^-1 : NNReal) : ENNReal) * Ddet
coordinateSourceMeasure =
  (referenceSource.withDensity jacobianDensity).withDensity sourceDensity.
```

## Pen-And-Paper Reproduction

The previous source-cylinder handoff proves, on a local shrink, that

```text
formalProductMeasure.restrict chartPiece
  <= Ddet * Measure.map sourceChart (coordinateSourceMeasure.restrict V),
```

where

```text
Ddet = Cdet * eps^-1.
```

The hypotheses remain local and explicit: `chartPiece` is measurable,
`chartPiece subset sourceChart '' (V inter sourceCylinder)`, and
`eps <= sourceDensity` holds a.e. on `baseJ.restrict V`, with `eps` neither
zero nor infinity.

The p.13 original-volume bridge says that for any additive Haar measure
`rawHaar`, any measurable `chartPiece subset p13SourceSet`, and any source
measure `sourceRef`, formal-product domination

```text
formalProductMeasure.restrict chartPiece <= Ddet * sourceRef
```

implies

```text
originalVolume.restrict chartPiece
  <= (((cHaar^-1 : NNReal) : ENNReal) * Ddet) * sourceRef.
```

Here `cHaar` is the Haar scalar comparing the raw tuple Haar, after the fixed
p.13 linear equivalence, with `originalTupleVolume`.  No normalization to
`1` is used.

To compose the facts, first choose a local source-image shrink that proves
`sourceChart '' Vsource subset p13SourceSet`.  Then run the source-cylinder
formal-product theorem inside `Vsource`, returning a smaller `V`.  Since
`V subset Vsource`, the public hypothesis

```text
chartPiece subset sourceChart '' (V inter sourceCylinder)
```

implies `chartPiece subset p13SourceSet`, which is exactly the support
hypothesis needed by the original-volume bridge.  With

```text
sourceRef = Measure.map sourceChart (coordinateSourceMeasure.restrict V),
```

the bridge gives the desired original-volume domination.  Finiteness of
`Dvol` follows from finiteness of `Ddet` and the fact that a coerced `NNReal`
Haar scalar is finite in `ENNReal`.

## Boundary

This is local measure packaging.  It does not prove determinant-chart Haar
transport, exact raw-Haar pushforward, Haar-scalar normalization,
source-density positivity, source-image coverage beyond the returned local
chart, source-rank coverage, original-prior transport, readback domination,
normal crossings, pole order, or RLCT extraction.
