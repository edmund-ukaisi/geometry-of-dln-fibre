# Statement Card - A2 source-dependent product family small-ball coordinate identities

Date: 2026-06-25.

## Claim

For a multi-edge chain, a base source family `CedgeBase`, and any positive
regular-coordinate radius `Rmax`, there is a smaller radius `R` with
`0 < R` and `R <= Rmax` such that the constructed source-dependent p.13
product family satisfies, eventually on the base source stratum and uniformly
for `u in ball(0,R)`,

```text
regularBlockCoordinateMap(CedgeProd(x,u)) = u
residualBlockCoordinateMap(CedgeProd(x,u)) =
  residualBlockCoordinateMap(CedgeBase x).
```

## Lean Artifact

```text
exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source
```

## Inputs Kept Explicit

- the base source family `CedgeBase`;
- source-stratum parameters `r` and `rEdge`;
- the fixed-base chart data `U0` and `hU0`;
- a positive outer regular radius `Rmax`.

## Nonclaims

No product chart, source coverage, continuity of the constructed family,
product-reduction certificate, triangular multiplier bound, measure transport,
normal-crossing statement, pole-order computation, or RLCT extraction is
proved here.

## Verification

Focused build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates`.
