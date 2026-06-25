# Statement Card - A2 local-source signed-box and monomial-unit boundary

Date: 2026-06-25.

## Claim

The p.13 local finite-integral front end can be stated over an explicit local
source set, and signed-box residual/density monomial bounds can be derived from
monomial-times-bounded-unit data.

## Lean Names

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource
signedBox_monomialLower_sourceDensityBounds_of_monomialUnits
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

## Inputs Kept Explicit

- measurable local source set;
- source chart and weighted signed-box pushforward for that local source;
- residual and density monomial-unit identities or bounds on the signed box;
- source-filter loss and transported-density bounds over the local source;
- fixed-base edge-matrix measurability.

## Nonclaims

No local chart construction, source coverage, pushforward identity,
density/Jacobian formula, normal-crossing extraction, pole order, or RLCT
statement is proved.

## Verification

Focused and full builds passed with the worktree-local Lake cache:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb
```

`scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
`git diff --check` was clean.
