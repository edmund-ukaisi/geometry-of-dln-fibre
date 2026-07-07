# Reproduction - A2 with-following original-volume readback on p.13/readback-preimage support

Date: 2026-07-07.

## Scope

This note packages the with-following original-volume readback bridge on the
same local chart pieces used by the p.13/readback-preimage finite-integral
wrapper.

The old readback bridge consumes:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet.
```

The new package should consume instead:

```text
MeasurableSet chartPiece
chartPiece subset p13SourceSet
chartPiece subset readback^{-1}(V)
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet.
```

It does not remove the raw-pushforward equality, prove Haar transport, prove
source-prior transport, or identify the original prior.

## Calculation

First shrink around the base point using the with-following local p.13 image
equality theorem.  It gives an open set `W` with

```text
z0 in W,
W subset G,
sourceChart '' W = p13SourceSet inter readback^{-1}(W),
forall z in W, readback (sourceChart z) = z.
```

Then apply the existing original-volume readback bridge inside `W`.  It returns
an open `V` with

```text
z0 in V,
V subset W,
forall z in V, readback (sourceChart z) = z,
sourceChart '' V is measurable,
```

and, for chart pieces in `sourceChart '' V`, the original-volume readback
domination by `thetaReference.restrict W`.

The image equality shrinks from `W` to `V`.  Since `V subset W` and
`readback (sourceChart z) = z` on `W`,

```text
sourceChart '' V = p13SourceSet inter readback^{-1}(V).
```

Indeed, the forward inclusion sends `sourceChart z` to the p.13 side by the
image equality for `W`, and its readback is `z`.  Conversely, if
`E in p13SourceSet` and `readback E in V`, then `readback E in W`, so the
`W` equality gives `E in sourceChart '' W`.  The point is represented by
`sourceChart (readback E)`, and the left-inverse/right-inverse bookkeeping in
the generic shrink lemma identifies this with `E`.

Therefore, for any chart piece satisfying

```text
chartPiece subset p13SourceSet
chartPiece subset readback^{-1}(V),
```

we get

```text
chartPiece subset sourceChart '' V.
```

Feed this derived image containment and the original p.13 containment into the
old readback bridge.

The old bridge returns:

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= D * thetaReference.restrict W.
```

Since `W subset G`,

```text
thetaReference.restrict W <= thetaReference.restrict G.
```

Composing scalar dominations gives the desired conclusion over `G`:

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= D * thetaReference.restrict G.
```

The a.e.-measurability conclusion is unchanged.

## Boundary

This is local support conversion plus the existing conditional
original-volume readback theorem.  It proves no determinant-chart Haar
transport, raw-order Haar transport, source-image coverage beyond this local
with-following chart, source-rank coverage, source-prior or original-prior
transport, normal crossings, pole order, or RLCT extraction.
