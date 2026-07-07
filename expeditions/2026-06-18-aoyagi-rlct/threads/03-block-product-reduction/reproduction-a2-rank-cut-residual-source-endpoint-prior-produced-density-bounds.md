# A2 rank-cut residual source from endpoint prior with produced density bounds

## Object-level calculation

Fix constants

```text
epsilon : ENNReal,
Kprior : Real.
```

Assume the source-image density pullback is continuous at the theta base point
and that the source density there is finite:

```text
ContinuousAt (sourceImageDensity o sourceChart) z0,
sourceImageDensity(sourceChart z0) < infinity.
```

Assume also the prior density is continuous at the edge-family base point.
Since the source chart is continuous at `z0` on the determinant sector, this
gives continuity of the pulled-back prior density:

```text
ContinuousAt (density o sourceChart) z0.
```

The strict basepoint inequalities

```text
epsilon < sourceImageDensity(sourceChart z0),
density(sourceChart z0) < Kprior
```

therefore give eventual non-strict bounds

```text
eventually near z0, epsilon <= sourceImageDensity(sourceChart z),
eventually near z0, density(sourceChart z) <= Kprior.
```

Choose an open neighborhood `Gbounds` where both bounds hold and run the
previous endpoint-prior rank-cut residual-source theorem inside

```text
Gshrink = G cap Gbounds.
```

It returns

```text
W subset Gshrink,
V subset W,
sourceChart '' V = p13SourceSet cap readback^{-1} V,
rankCutSource = (p13SourceSet cap readback^{-1} V) cap sourceStratum.
```

For the source lower bound, `W subset Gbounds` gives pointwise

```text
epsilon <= sourceDensity z
```

for all `z in W`, hence the required a.e. statement for
`baseJ.restrict W`.

For the prior upper bound, if `E in rankCutSource`, the image equality gives
`E = sourceChart z` for some `z in V`.  Since `V subset W subset Gbounds`, the
prior neighborhood gives

```text
density E = density(sourceChart z) <= Kprior.
```

Pointwise boundedness on the measurable set `rankCutSource` gives the required
a.e. statement for `originalVolume.restrict rankCutSource`.

The downstream endpoint-prior bridge still requires `epsilon != 0`.  The
separate hypothesis `epsilon != infinity` is not needed: it follows from

```text
epsilon < sourceImageDensity(sourceChart z0) < infinity.
```

## Boundary

This removes the explicit terminal source-density lower and prior-density
upper a.e. hypotheses from the endpoint-prior rank-cut residual-source chain,
provided fixed constants `epsilon` and `Kprior` satisfy strict basepoint
inequalities before the shrink is chosen.

It still does not prove endpoint-reference Haar transport, determinant/raw
Haar transport, source-prior transport, source-rank or analytic-atlas coverage,
normal crossings, pole order, or RLCT extraction.
