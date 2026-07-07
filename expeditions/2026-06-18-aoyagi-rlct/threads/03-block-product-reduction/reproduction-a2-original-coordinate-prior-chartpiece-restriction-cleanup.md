# A2 reproduction: pushed coordinate prior restricted to a chart piece

## Status

Controller reproduction before Lean.  This is finite-dimensional measure
transport bookkeeping, independent of the analytic source-image hypotheses.

## Setup

Let

```text
toEdge x = tupleToEdgeFamily b ((canonicalCoord d).symm x)
edgeDensity E = coordDensity (canonicalCoord d (edgeFamilyMatrixTuple b E)).
```

For any measurable edge-family set `C`, the existing preimage transport theorem
proves

```text
Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict (toEdge^{-1}(C)))
=
(originalEdgeFamilyPrior b edgeDensity).restrict C.
```

Assume now that `chartPiece` is measurable and `chartPiece subset C`.

## Calculation

Apply the transport theorem first to `C`:

```text
Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict (toEdge^{-1}(C)))
= edgePrior.restrict C.
```

Restrict both sides to `chartPiece`:

```text
(Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict (toEdge^{-1}(C))))
    .restrict chartPiece
=
(edgePrior.restrict C).restrict chartPiece.
```

Since `chartPiece subset C`,

```text
(edgePrior.restrict C).restrict chartPiece = edgePrior.restrict chartPiece.
```

Apply the same transport theorem to `chartPiece`:

```text
Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict
    (toEdge^{-1}(chartPiece)))
= edgePrior.restrict chartPiece.
```

Combining these identities gives

```text
(Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict (toEdge^{-1}(C))))
    .restrict chartPiece
=
Measure.map toEdge
  ((originalCoordinatePrior d coordDensity).restrict
    (toEdge^{-1}(chartPiece))).
```

If the a.e.-measurability hypothesis for `coordDensity` is known on
`toEdge^{-1}(C)`, the hypothesis for `chartPiece` follows by absolute
continuity of the smaller restricted tuple volume measure, because
`tupleToEdgeFamily^{-1}(chartPiece) subset tupleToEdgeFamily^{-1}(C)`.

## Kill conditions

- `chartPiece` must be contained in `C`; otherwise restricting after mapping
  need not match restricting before mapping.
- Both sets must be measurable to use the existing transport theorem.
- The statement remains finite-dimensional coordinate transport.  It does not
  prove source-image density, determinant/raw Haar transport, source-rank
  coverage, normal crossings, pole order, or RLCT.
