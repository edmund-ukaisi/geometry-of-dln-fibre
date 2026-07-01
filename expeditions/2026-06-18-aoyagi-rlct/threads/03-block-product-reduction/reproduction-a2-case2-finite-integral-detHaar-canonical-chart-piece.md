# A2 Case 2: canonical chart piece for the determinant-domination finite integral

Status: pen-and-paper reproduction checked; Lean target selected.

## Question

The determinant-domination finite-integral wrapper returns a local source
neighborhood `U` and a passive-theta shrink `V`.  Its consumer still supplies an
arbitrary measurable `chartPiece` with

```text
chartPiece subset U inter sourceStratum,
chartPiece subset sourceChart '' V.
```

For the Aoyagi p.13 local chart, the natural chart piece is the whole
intersection

```text
chartPiece := (U inter sourceStratum) inter sourceChart '' V.
```

The goal is to expose this canonical piece directly, so downstream A2 work no
longer has to restate the two subset proofs.

## Calculation

The existing same-shrink wrapper already returns:

```text
MeasurableSet (sourceChart '' V),
MeasurableSet (U inter sourceStratum),
```

and a finite-integral socket for every measurable `chartPiece` contained in
both sets.  Therefore the canonical intersection is measurable:

```text
MeasurableSet ((U inter sourceStratum) inter sourceChart '' V).
```

Its two containment proofs are projections:

```text
E in chartPiece  ->  E in U inter sourceStratum,
E in chartPiece  ->  E in sourceChart '' V.
```

Calling the existing socket with this chart piece gives the finite integral
under exactly the same determinant-side domination, source-density lower bound,
and prior-density bound, now stated on the canonical piece.

## Boundary

This is only a packaging corollary.  It does not prove the determinant-side
reverse domination, the lower bound for `sourceDensity`, determinant-chart Haar
transport, raw-Haar transport, source-image coverage, source-rank coverage,
original source-prior transport, normal crossings, pole order, or RLCT
extraction.
