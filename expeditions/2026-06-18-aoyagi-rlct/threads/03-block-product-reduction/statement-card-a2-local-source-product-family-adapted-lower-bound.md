# Statement Card - A2 local-source product-family adapted lower bound

Date: 2026-06-25.

## Claim

The explicit self-base multi-edge p.13 product-coordinate adapted lower bound
can be used on the measurable local source extracted from the source
certificate.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

## Inputs Kept Explicit

- fixed-base regular-coordinate source data;
- local continuity and self-base identity for `CedgeBase`;
- fixed-base edge-matrix measurability;
- positive maximum regular-coordinate radius.

## Discharged Input

The theorem constructs the measurable local source and transports the existing
source-rank-stratum p.13 product-family adapted lower bound to
`nhdsWithin x0 source`.  It also returns the equality
`nhdsWithin x0 source = nhdsWithin x0 sourceRankStratum`.

## Nonclaims

No signed-box residual chart, source image/coverage theorem, weighted
pushforward, Jacobian/source-density formula, residual or source-density
monomial-unit identity, normal-crossing theorem, pole-order computation, or
RLCT statement is proved.

## Verification

Focused build passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Full build also passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
