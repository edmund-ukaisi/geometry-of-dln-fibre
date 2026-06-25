# Statement Card - A2 local-source monomial-unit finite-integral wrapper

Date: 2026-06-25.

## Claim

The local-source signed-box p.13 finite-integral handoff can consume supplied
monomial-times-bounded-unit residual and source-density identities directly.

## Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix
```

## Inputs Kept Explicit

- measurable local source set;
- signed-box source chart and weighted pushforward for `mu.restrict source`;
- residual and source-density monomial-unit identities on the signed box;
- residual-unit lower bound and density-unit upper/nonnegative bounds;
- local source-filter loss and transported-density bounds;
- fixed-base edge-matrix measurability.

## Nonclaims

No local chart construction, source coverage, pushforward proof,
density/Jacobian formula, concrete monomial-unit production,
normal-crossing extraction, pole order, or RLCT statement is proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
