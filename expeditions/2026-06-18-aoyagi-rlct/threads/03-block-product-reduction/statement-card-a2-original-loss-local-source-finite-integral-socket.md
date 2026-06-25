# Statement Card - A2 original-loss local-source finite-integral socket

Date: 2026-06-25.

## Claim

The local-source adapted-loss finite-integral socket specializes to the
original endpoint square-Frobenius `lossDLN` of a chain-coordinate tuple.

## Lean Name

```text
exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
```

## Inputs Kept Explicit

- measurable local source set;
- residual positivity on `mu.restrict source`;
- residual negative-power integrability on `source`;
- local source-filter adapted product-difference lower bound;
- local source-filter density nonnegativity and upper bound;
- fixed endpoint bases.

## Discharged Input

The adapted-to-loss comparison is proved for concrete `lossDLN` by finite
endpoint basis comparison and the adapted Frobenius-loss/square-sum identity.

## Nonclaims

No local chart construction, source coverage, signed-box pushforward,
Jacobian/source-density transport, residual or source-density monomial-unit
identity, product-coordinate adapted lower-bound proof, statistical/KL loss
comparison, normal-crossing extraction, pole order, or RLCT statement is
proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
