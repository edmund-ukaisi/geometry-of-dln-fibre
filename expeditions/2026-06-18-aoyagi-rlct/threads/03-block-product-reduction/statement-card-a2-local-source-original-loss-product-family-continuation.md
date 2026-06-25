# Statement Card - A2 local-source original-loss product-family continuation

Date: 2026-06-25.

## Claim

The measurable local-source package and explicit self-base multi-edge p.13
product-family adapted lower bound can be composed with the local-source
original-loss socket to return a continuation for finite local integrals of
the concrete endpoint `lossDLN`.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase
```

## Inputs Kept Explicit

- fixed-base regular-coordinate source data;
- local continuity and self-base identity for `CedgeBase`;
- fixed-base edge-matrix measurability;
- positive maximum regular-coordinate radius;
- for the returned continuation: residual positivity on the returned source,
  residual negative-power integrability on the returned source, an additive
  Haar regular-coordinate measure, and local density nonnegativity/boundedness.

## Discharged Inputs

The theorem constructs the measurable local source, carries source-rank data
and the `nhdsWithin` equality, constructs positive `R` and `c`, supplies the
explicit self-base multi-edge product-family adapted lower bound, and applies
the local-source original-loss finite-integral socket.

## Nonclaims

No signed-box residual chart, source image/coverage theorem, weighted
pushforward, Jacobian/source-density formula, residual or source-density
monomial-unit identity, residual integrability proof, normal-crossing theorem,
pole-order computation, or RLCT statement is proved.

## Verification

Focused build passed with the worktree-local Lake build and local shared-cache
path:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
```

Full build also passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
