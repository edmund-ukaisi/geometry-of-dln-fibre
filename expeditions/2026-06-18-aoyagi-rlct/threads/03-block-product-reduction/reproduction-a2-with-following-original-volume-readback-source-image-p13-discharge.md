# Reproduction - A2 with-following original-volume readback with p.13 support discharged

Date: 2026-07-02.

## Scope

This note removes the explicit p.13 chart-piece containment hypothesis from the
with-following original-volume readback domination theorem, but only for chart
pieces already contained in the actual local source-chart image.

It still assumes:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

## Composition

First use the with-following p.13 support theorem to choose a local open set
`V0` with

```text
sourceChart '' V0 subset p13SourceSet.
```

Then use the existing with-following readback theorem inside `V0`.  It returns
a smaller local open set `V subset V0` with source-chart readback data and the
old conditional readback domination conclusion, provided the caller supplies
`chartPiece subset p13SourceSet`.

For this smaller `V`, any `chartPiece subset sourceChart '' V` is also contained
in `p13SourceSet`, because

```text
sourceChart '' V subset sourceChart '' V0 subset p13SourceSet.
```

Thus the old readback theorem applies without exposing the p.13 containment as
a caller hypothesis.

## Conclusion

Under the raw-pushforward equality, every measurable `chartPiece` contained in
the actual source-chart image has

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
Measure.map readback (originalVolume.restrict chartPiece)
  <= D • thetaReference.restrict G,
```

where

```text
D = ((cHaar^-1 : NNReal) : ENNReal) * 1.
```

## Boundary

Only the p.13 chart-piece containment field is discharged.  The theorem proves
no raw-Haar transport, determinant-chart Haar theorem, source-image coverage
beyond the local chart image, source-prior or original-prior transport, density
lower-bound removal, normal crossings, pole order, or RLCT extraction.
