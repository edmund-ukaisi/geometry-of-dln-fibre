# Statement Card - A2 residual-power threshold-shift bridge

Date: 2026-06-25.

## Claim

Let `E` be a finite-dimensional real normed space with additive Haar measure
`nu`, let `mu` be a measure on a base measurable space `alpha`, and let
`a : alpha -> R`.  Put

```text
d = finrank_R(E).
```

If

```text
a(x) > 0  for mu-a.e. x,
t > 0,
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity,
```

then

```text
∫⁻ (x,u), ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-(t+d/2))) d(mu.prod nu)
<
infinity.
```

No finite-measure hypothesis on `mu` is used.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

## Proof Ingredients

- Variable-base product fiber estimate:
  `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale`;
- variable-base product finiteness theorem:
  `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top`;
- the substitution `s = t + finrank_R(E)/2`;
- arithmetic `finrank_R(E)/2 - s = -t`;
- `t>0`, giving the supercritical inequality `finrank_R(E)/2 < s`.

## Nonclaims

- No proof that Aoyagi's reduced residual coordinates satisfy the displayed
  residual negative-power hypothesis.
- No theorem for `a=0` on a positive-measure set.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
