# Statement Card - A2 regular-suspension reverse threshold shift

Date: 2026-06-29.

## Claim

For a finite-dimensional real normed space `E` with additive Haar measure
`nu`, a base measure `mu`, and `a : alpha -> R`, the local square model

```text
a(x) + ||u||^2
```

has the expected reverse finite-integrability implication on a regular ball:
if `AEMeasurable a mu`, `R>0`, `a>0` a.e., `a<=R^2` a.e., and the product
lower integral at exponent `s>d/2` is finite, then

```text
int^- x, ofReal(a(x)^(d/2-s)) dmu < infinity.
```

Specialising `s = t+d/2`, this gives finite residual `a^(-t)` integrability
from finite product integrability at exponent `t+d/2`.

Combined with the previously proved forward theorem, Lean proves the local
model-integral iff for `t>0`.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Main theorems:

```text
base_power_scale_le_lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod
lintegral_ofReal_base_power_lt_top_of_product_lt_top
lintegral_ofReal_residual_power_lt_top_of_product_lt_top
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
```

## Proof Ingredients

- Pointwise lower bound on `ball(0,sqrt(a))`;
- inclusion `ball(0,sqrt(a)) subset ball(0,R)` from `a<=R^2` and `R>0`;
- Haar scaling `nu(ball(0,sqrt(a)))`;
- real-power identity
  `a^(d/2-s) * 2^(-s) = (2a)^(-s) * (sqrt(a))^d`;
- Tonelli via `lintegral_prod`, requiring `AEMeasurable a mu`;
- ENNReal cancellation by the nonzero finite constant
  `ofReal(2^(-s)) * nu(ball(0,1))`.

## Nonclaims

- No p. 13 chart coverage, density/Jacobian transport, or source-prior
  statement.
- No proof of residual integrability for Aoyagi's reduced residual chart.
- No removal of `a<=R^2`; dropping it over an infinite base would be false.
- No pole-order, normal-crossing, or RLCT claim.
