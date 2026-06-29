# Review - A2 regular-suspension reverse threshold shift

Date: 2026-06-29.

Reviewer: xhigh `Copernicus the 2nd`.

Status: passed.

## Scope

Reviewed the uncommitted Lean diff in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

for the reverse local regular-square threshold-shift slice, especially:

```text
base_power_scale_le_lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball
base_power_scale_le_lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod
lintegral_ofReal_base_power_lt_top_of_product_lt_top
lintegral_ofReal_residual_power_lt_top_of_product_lt_top
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
```

## Findings

No formalisation or mathematical inaccuracies were found.

## Soundness Notes

The real-power scaling is correct under `0 < a`: it rewrites

```text
a^(d/2-s) * 2^(-s)
```

as

```text
(2*a)^(-s) * (sqrt a)^d.
```

The product-level proof correctly adds `AEMeasurable a mu` and `[SFinite nu]`
before using `lintegral_prod`; the earlier forward theorem does not need this
because it uses only `lintegral_prod_le`.

The ENNReal cancellation step uses a nonzero constant

```text
ofReal(2^(-s)) * nu(ball(0,1)).
```

Nonzeroness comes from positivity of `2^(-s)` and positive Haar measure of the
unit ball.

The final iff does not overclaim: the reverse direction carries the local
upper bound `a <= R^2` a.e., while the forward direction remains stronger.

## Verification

The reviewer ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
```

and it passed.

## Residual Risk

The review covered only this Lean diff and its local supporting lemmas, not
future downstream uses.
