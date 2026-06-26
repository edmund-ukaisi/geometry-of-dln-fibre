# Statement Card - A2 product-coordinate residual-rank readback

Date: 2026-06-26.

## Claim

If the explicit p.13 multi-edge product-coordinate family is already in the
source-rank stratum at `(x,u)`, and `det(Ctop(u))` is a unit, then each base
Schur residual block has rank `rEdge p - r`.

## Lean Artifact

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum
```

Target file:
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`.

## Inputs Kept Explicit

- source-rank membership of `(x,u)` for the constructed product-coordinate
  family;
- the determinant-unit hypothesis for `Ctop(u)`;
- fixed basepoint chart data `U₀`, `hU₀`;
- the base edge family and source point.

## Nonclaims

This is not source coverage, not a local inverse, not exact-rank openness, not
source/image equality, not source-measure transport, not density/Jacobian
transport, not normal crossings, not pole order, and not RLCT.

## Verification Plan

Run:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
scripts/sorries
git diff --check
```
