# A2 with-following full local source-image finite integral

## Claim

The radius-free continuous-at prior-density finite-integral wrapper is stated
for every measurable chart piece contained in the local source-chart image:

```text
chartPiece ⊆ sourceChart '' V.
```

For the natural local chart piece, take

```text
chartPiece = sourceChart '' V.
```

Then the chart-piece support hypothesis is tautological, and measurability is
already part of the local source-image package.  Therefore the product-residual
finite-integral statement holds over the whole local source-chart image.

## Pen-and-paper check

The existing local package returns an open source neighborhood `V` such that

```text
MeasurableSet (sourceChart '' V),
∀ E ∈ sourceChart '' V, E ∈ p13SourceSet,
```

and, for every measurable `chartPiece`,

```text
chartPiece ⊆ sourceChart '' V
==> ∫ residualIntegrand d(originalPrior.restrict chartPiece) < ∞.
```

Substitute `chartPiece = sourceChart '' V`.  The measurability input is the
returned `MeasurableSet (sourceChart '' V)`, and the containment input is

```text
sourceChart '' V ⊆ sourceChart '' V.
```

Thus the integral is finite on the full local source-chart image.

## Boundary

This is not global p.13 source-image coverage.  It does not prove that an
arbitrary p.13 source point lies in this image, nor that finitely many such
images cover a p.13 neighborhood.  It only removes the arbitrary chart-piece
parameter for the canonical local image produced by the source chart.
