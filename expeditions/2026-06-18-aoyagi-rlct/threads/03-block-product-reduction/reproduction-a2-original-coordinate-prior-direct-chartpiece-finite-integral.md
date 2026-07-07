# A2 reproduction: direct chart-piece coordinate-prior finite integral

## Status

Controller reproduction before Lean.  This is a narrow consumer of the
chart-piece restriction cleanup for the already proved pushed-coordinate-prior
p.13 finite-integral bridge.

## Setup

Let

```text
toEdge x = tupleToEdgeFamily b ((canonicalCoord d).symm x)
C = sourceChart '' V.
```

The existing p.13 bridge proves, for a measurable chart piece satisfying

```text
chartPiece subset sourceChart '' (V inter W),
```

the finite integral over

```text
((map toEdge ((originalCoordinatePrior d coordDensity).restrict
  (toEdge^{-1}(C)))).restrict chartPiece).prod nu.
```

The chart-piece restriction cleanup proves that if
`chartPiece subset C`, then this measure is equal to

```text
(map toEdge ((originalCoordinatePrior d coordDensity).restrict
  (toEdge^{-1}(chartPiece)))).prod nu.
```

## Calculation

From `chartPiece subset sourceChart '' (V inter W)` we get

```text
chartPiece subset sourceChart '' V
```

by projecting the source witness from `V inter W` to `V`.

Therefore the finite integral supplied by the existing p.13 theorem transfers
across the measure equality from the cleanup lemma and yields the same finite
integral for the directly restricted coordinate prior:

```text
map toEdge ((originalCoordinatePrior d coordDensity).restrict
  (toEdge^{-1}(chartPiece))).
```

No source-image, prior-density, Haar, or analytic hypothesis is changed.  The
new statement only exposes the final measure in the direct chart-piece form.

## Kill conditions

- The chart piece must remain contained in `sourceChart '' (V inter W)`;
  otherwise the p.13 readback/right-inverse part is not justified.
- The a.e.-measurability of `coordDensity` is still assumed on the larger
  preimage `toEdge^{-1}(sourceChart '' V)`, then restricted to the chart piece
  by absolute continuity.
- The result must not be read as constructing `sourceImageDensity`,
  identifying a source-chart prior, proving determinant/raw Haar transport,
  proving source-rank or atlas coverage, constructing normal crossings,
  computing pole order, or extracting RLCT.
