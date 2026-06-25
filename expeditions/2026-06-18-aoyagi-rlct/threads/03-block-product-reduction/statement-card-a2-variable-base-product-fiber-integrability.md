# Statement Card - A2 variable-base product fiber integrability

Date: 2026-06-25.

## Claim

Let `E` be a finite-dimensional real normed space with additive Haar measure
`nu`, let `mu` be a measure on a base measurable space `alpha`, and let
`a : alpha -> R`.  Put

```text
p = finrank_R(E)/2 - s.
```

If

```text
a(x) > 0  for mu-a.e. x,
finrank_R(E)/2 < s,
∫⁻ x, ENNReal.ofReal (a(x)^p) dmu < infinity,
```

then

```text
∫⁻ (x,u), ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s)) d(mu.prod nu)
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
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

## Proof Ingredients

- Sharp fixed-positive-parameter fiber bound:
  `lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale`;
- Japanese-bracket finiteness:
  `lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top`;
- Tonelli inequality `lintegral_prod_le`;
- a.e. monotonicity of lower integrals over the base;
- constant pullout by `lintegral_mul_const'`;
- `ENNReal.mul_lt_top`.

## Nonclaims

- No proof that Aoyagi's residual base satisfies the displayed base-power
  hypothesis.
- No theorem for `a=0` on a positive-measure set.
- No endpoint or divergent-side theorem.
- No bounded-density/prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
