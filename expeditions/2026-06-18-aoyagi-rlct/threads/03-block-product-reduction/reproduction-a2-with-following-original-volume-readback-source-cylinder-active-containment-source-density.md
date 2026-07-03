# A2 with-following original-volume readback from source-cylinder support

Date: 2026-07-03.

## Claim

The original-volume readback active-containment wrapper can discharge its
active endpoint-image containment hypothesis when the chart piece is supported
on the theta-side source cylinder:

```text
chartPiece subset sourceChart '' (V inter sourceCylinder),
sourceCylinder = {z | z.1.yNext in signedBox Rres}.
```

For the concrete p.13 raw patch

```text
P = rawSourceSet inter rawChart^{-1}(chartPiece),
endpointPatch = rawDetChart inter rawOrderOnEndpoint^{-1}(P),
```

the source-cylinder support, raw/source compatibility, injectivity of the raw
order and p.13 raw chart maps, and the active endpoint factorization prove

```text
endpointPatch subset activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

The existing original-volume active-containment wrapper then turns this into
readback domination by the coordinate-source measure, under the same a.e.
source-density lower bound by `epsilon`.

## Pen-and-paper containment calculation

Take

```text
y in rawDetChart inter rawOrderOnEndpoint^{-1}
      (rawSourceSet inter rawChart^{-1}(chartPiece)).
```

Then

```text
rawOrderOnEndpoint y in rawSourceSet,
rawChart(rawOrderOnEndpoint y) in chartPiece.
```

By source-cylinder support, there is a point

```text
z in V inter sourceCylinder
```

with

```text
sourceChart z = rawChart(rawOrderOnEndpoint y).
```

The local raw/source compatibility package gives, for this same `z`,

```text
Y z in rawDetChart,
rawOrderOnEndpoint(Y z) in rawSourceSet,
rawChart(rawOrderOnEndpoint(Y z)) = sourceChart z.
```

Therefore the two raw-source points have the same p.13 raw chart value:

```text
rawChart(rawOrderOnEndpoint y)
  = rawChart(rawOrderOnEndpoint(Y z)).
```

Since both raw-order images lie in `rawSourceSet`, injectivity of the p.13 raw
chart on `rawSourceSet` gives

```text
rawOrderOnEndpoint y = rawOrderOnEndpoint(Y z).
```

Since both `y` and `Y z` lie in `rawDetChart`, injectivity of the raw-order map
on `rawDetChart` gives

```text
y = Y z.
```

The active endpoint factorization finally gives

```text
Y z = activeWriteback(activeChart z).
```

Because `z in V inter sourceCylinder`, this proves the endpoint-patch
containment required by the active-containment readback wrapper.

## Measure composition

After the containment calculation, no new measure argument is needed.  The
already-proved original-volume active-containment wrapper consumes:

```text
chartPiece measurable,
chartPiece subset sourceChart '' V,
endpointPatch subset activeWriteback '' (activeChart '' (V inter sourceCylinder)),
epsilon <= sourceDensity a.e. on baseJ.restrict V,
epsilon != 0, infinity.
```

The source-cylinder support immediately implies ordinary support
`chartPiece subset sourceChart '' V` by projection.  The wrapper returns finite
`Cdet`, sets `D = Cdet * epsilon^{-1}`, and proves

```text
map readback (originalVolume.restrict chartPiece)
  <= ((cHaar^{-1}) * D) • coordinateSourceMeasure.restrict G.
```

## Boundary

This proves active containment only from source-cylinder support.  It does not
derive source-cylinder support from plain `chartPiece subset sourceChart '' V`;
that requires either shrinking with `V subset sourceCylinder` or a separate
C-one-readout support hypothesis.  It also does not prove source-density
positivity, endpoint-patch measurability beyond the concrete p.13 chart-piece
socket already consumed by the wrapper, determinant-chart Haar transport,
exact raw-Haar pushforward, Haar normalization, source coverage, source-rank
coverage, original source-prior transport, normal crossings, pole order, or
RLCT extraction.
