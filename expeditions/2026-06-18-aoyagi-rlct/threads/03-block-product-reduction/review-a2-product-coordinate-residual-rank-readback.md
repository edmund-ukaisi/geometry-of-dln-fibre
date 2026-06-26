# Review - A2 product-coordinate residual-rank readback

Date: 2026-06-26.

Reviewers: xhigh read-only checker `Lagrange the 2nd`, plus controller
Lean/API review.

## Verdict

Accepted for the stated pointwise rank-readback scope.

The theorem is mathematically sound: source-rank membership for the constructed
product-coordinate family gives the ranks of those constructed edges, and the
three p.13 block-rank formulas express those ranks as
`r + rank(residualBlock)`.  The fixed basepoint certificate identifies the
regular corner size with the source rank `r`.

## Lean Landing

The theorem landed in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`:

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum
```

The proof reuses the same endpoint/middle case split as the forward
source-rank membership theorem, then closes the natural-number subtraction by
`omega`.

## Boundary

This theorem is not source coverage.  It assumes the constructed
product-coordinate point is already in the source-rank stratum.  It does not
prove exact-rank openness, a local inverse, source/image equality, chart
coverage, source-measure transport, density/Jacobian identity, normal
crossings, pole order, or RLCT.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
