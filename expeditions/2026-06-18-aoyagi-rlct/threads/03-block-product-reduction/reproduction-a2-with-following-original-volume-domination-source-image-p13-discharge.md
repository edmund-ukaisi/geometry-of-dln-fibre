# Reproduction - A2 with-following original-volume domination with p.13 support discharged

Date: 2026-07-02.

## Scope

This note removes one local hypothesis from the with-following original-volume
domination theorem.  The old consumer required both:

```text
chartPiece subset sourceChart '' V
chartPiece subset p13SourceSet.
```

The local support theorem supplies

```text
sourceChart '' V subset p13SourceSet,
```

so the p.13 containment of `chartPiece` follows from the source-image
containment.

This does not remove the raw-pushforward equality, chart-piece measurability,
or actual source-image containment.

## Composition

First shrink inside the prescribed open set `G` using the with-following
source-chart p.13 support theorem.  It gives an open set `V0` with

```text
z0 in V0,
V0 subset G,
sourceChart '' V0 subset p13SourceSet.
```

Then apply the existing with-following original-volume/source-reference
domination theorem with `G = V0`.  It produces a smaller open set

```text
V subset V0.
```

Therefore, for any `E in sourceChart '' V`, write `E = sourceChart z` with
`z in V`.  Since `V subset V0`, we have `z in V0`, hence

```text
E in sourceChart '' V0 subset p13SourceSet.
```

Thus any `chartPiece subset sourceChart '' V` also satisfies

```text
chartPiece subset p13SourceSet.
```

Passing this derived containment to the old theorem yields the same conclusion:

```text
originalVolume.restrict chartPiece
  <= ((((cHaar^-1 : NNReal) : ENNReal) * 1) • sourceRef).
```

## Boundary

Only the p.13 chart-piece containment field is discharged.  The theorem still
requires:

```text
MeasurableSet chartPiece
chartPiece subset sourceChart '' V
Measure.map rawMap (thetaReference.restrict V) = rawHaar.restrict rawSourceSet.
```

It proves no raw-Haar transport, determinant-chart Haar theorem, source-image
coverage beyond the local chart image, source-prior or original-prior transport,
density lower-bound removal, normal crossings, pole order, or RLCT extraction.
