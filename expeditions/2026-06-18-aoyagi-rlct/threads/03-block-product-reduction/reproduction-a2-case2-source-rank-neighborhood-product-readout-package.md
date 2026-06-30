# A2 Case 2 source-rank-neighborhood product readout package

This note records the source-rank-neighborhood wrapper for the Case 2 p.13
product source chart.  It is independent of the quiver paper and uses only
Aoyagi's p.13 coordinate algebra already formalized in the local fixed-base
and Case 2 readout theorems.

## Setup

Let

```text
sourceChart theta =
  case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e theta
```

and let `productSourceChart(theta,u)` be the p.13 product-coordinate family
over this source chart.  For a source-rank stratum

```text
sourceStratum =
  paperEndpointFixedBaseSourceRankStratum ... sourceChart r rEdge
```

and a base point `theta₀`, later local arguments naturally work in

```text
nhdsWithin theta₀ sourceStratum.
```

## Calculation

The already-proved global Case 2 package chooses, for every `Rmax > 0`, a
radius `0 < R <= Rmax` such that every `theta` and every `u in ball(0,R)`
satisfy:

```text
regularCoordinateMap(productSourceChart(theta,u)) = u
residualCoordinateMap(productSourceChart(theta,u))
  =
residualCoordinateMap(sourceChart theta)
regularReadback(productSourceChart(theta,u)) = u
selectedInverseReadout(productSourceChart(theta,u))
  =
selectedInverseReadout(sourceChart theta)
sourceReadback(productSourceChart(theta,u)) has the canonical p.13 product fields.
```

Since this is uniform in `theta`, restricting the statement to
`nhdsWithin theta₀ sourceStratum` is only a filter wrapper:

```text
Filter.Eventually.of_forall
```

turns the global `forall theta` theorem into one eventual theorem along the
source-rank stratum.  No source-rank openness, coverage, image equality,
measure transport, or new determinant calculation is used.

## Boundary

The wrapper does not prove that the source chart covers a source-rank
neighborhood.  It also does not identify an original/source prior, prove a
Haar/Jacobian density identity, establish normal crossings, compute pole
order, or extract an RLCT.  It only packages already-proved readout facts in
the filter shape needed by later source-rank-local arguments.
