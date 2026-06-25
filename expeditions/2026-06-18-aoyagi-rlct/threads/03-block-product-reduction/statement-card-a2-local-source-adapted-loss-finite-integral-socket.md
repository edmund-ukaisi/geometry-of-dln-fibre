# Statement Card - A2 local-source adapted-loss finite-integral socket

Date: 2026-06-25.

## Claim

The adapted-loss comparison finite-integral socket works over an explicit
local source set, not only over the full source-rank stratum.

## Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
```

## Inputs Kept Explicit

- measurable local source set;
- residual positivity and residual negative-power integrability on that source;
- local source-filter adapted lower bound;
- local source-filter adapted-to-loss comparison;
- local source-filter density nonnegativity and upper bound.

## Nonclaims

No adapted product-coordinate lower-bound proof, original `lossDLN` comparison,
local chart construction, source coverage, density/Jacobian transport,
normal-crossing extraction, pole order, or RLCT statement is proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
