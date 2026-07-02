# A2 with-following inverse-Haar original-volume readback density socket

Date: 2026-07-02.

## Source calculation

Work on the local with-following Case 2 source chart.  The preceding
inverse-Haar source-image bridge gives, after shrinking inside the caller
neighborhood, a set `V` such that:

```text
readback (sourceChart z) = z,
sourceChart is injective and continuous on V,
sourceChart '' V is measurable,
sourceChart '' V subset p13SourceSet.
```

It also says that if:

```text
map rawMap (thetaReference | V) = rawHaar | rawSourceSet,
```

then for every measurable `chartPiece subset sourceChart '' V`, with

```text
c =
  (map rawOrderMatrixTupleEquiv rawHaar).addHaarScalarFactor
    (originalTupleVolume d),
sourceRef = map sourceChart (thetaReference | V),
invHaarDensity = fun _ => c^-1,
```

we have:

```text
originalVolume | chartPiece
  = (sourceRef.withDensity invHaarDensity) | chartPiece
```

and:

```text
forall-ae E with respect to sourceRef | chartPiece,
  invHaarDensity E <= c^-1.
```

## Readback step

The generic p.13 readback-density socket applies to any chart map and readback
with:

```text
readback (sourceChart z) = z on V,
sourceChart injective and continuous on V,
originalVolume | chartPiece =
  ((map sourceChart (thetaReference | V)).withDensity volumeDensity)
    | chartPiece,
volumeDensity <= D a.e. on sourceRef | chartPiece.
```

Taking:

```text
volumeDensity = invHaarDensity,
D = c^-1,
coordinateSourceMeasure = thetaReference,
```

gives:

```text
readback is a.e. measurable with respect to originalVolume | chartPiece,
map readback (originalVolume | chartPiece)
  <= c^-1 * (thetaReference | G).
```

The inequality uses only `V subset G`, because the exact readback on
`sourceChart '' V` identifies:

```text
map readback (map sourceChart (thetaReference | V))
  = thetaReference | V
  <= thetaReference | G.
```

## Boundary

This is a consumer of the exact local source-image inverse-Haar bridge.  The
raw pushforward identity remains a hypothesis.  The theorem does not prove
determinant-Haar transport, raw-Haar transport, source-prior/original-prior
transport, source-image coverage beyond the local chart, source-rank coverage,
normal crossings, pole order, or RLCT extraction.
