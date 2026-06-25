# Statement Card - A2 original-loss local integrability for the product family, edge-matrix form

Date: 2026-06-25.

## Claim

For the explicit self-base multi-edge p.13 product-coordinate family, the
original `lossDLN` local finite-integral theorem can be stated with
`ContinuousAt CedgeBase x0` and an explicit fixed-base edge-matrix measurability
hypothesis, rather than global `Continuous CedgeBase`.

## Planned Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
```

## Inputs Kept Explicit

- multi-edge shape `N = M + 2`;
- fixed-base complement data `U0, hU0`;
- `ContinuousAt CedgeBase x0`;
- self-base equality `CedgeBase x0 = reverseEdge Bv`;
- fixed-base edge-matrix measurability;
- signed-box source chart and weighted pushforward;
- residual monomial lower bound and source-density monomial upper bound;
- transported density continuity and positivity at `(x0,0)`.

## Nonclaims

No source chart, pushforward identity, residual monomial lower bound,
density/Jacobian formula, normal-crossing certificate, pole-order theorem, or
RLCT extraction is proved.

## Verification

Focused build passed:
`env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure`.

Full build and hygiene passed on 2026-06-25 using the worktree-local Lake
shared directory:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
scripts/sorries
git diff --check
```

The `scripts/sorries` summary was `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
