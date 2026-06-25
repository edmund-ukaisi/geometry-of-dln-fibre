# Statement Card - A2 sharp positive-parameter fiber scaling

Date: 2026-06-25.

## Claim

Let `E` be a finite-dimensional real normed space with additive Haar measure
`mu`, let `d=finrank_R(E)`, and let `a>0`.

The positive-parameter square model satisfies the whole-space scaling identity

```text
∫⁻ u, ENNReal.ofReal ((a + ||u||^2)^(-s)) dmu
  =
ENNReal.ofReal (a^(d/2-s))
  * ∫⁻ v, ENNReal.ofReal ((1 + ||v||^2)^(-s)) dmu.
```

Consequently, for any radius `R`,

```text
∫⁻ u, ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a + ||u||^2)^(-s)) dmu
<=
ENNReal.ofReal (a^(d/2-s))
  * ∫⁻ v, ENNReal.ofReal ((1 + ||v||^2)^(-s)) dmu.
```

If additionally `d/2<s`, then the ball-restricted lower integral is finite.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_comp_inv_smul_eq_mul_addHaar
DLNFibre.DLN.Aoyagi.ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
```

## Proof Ingredients

- Haar scaling for scalar multiplication on finite-dimensional real normed
  spaces;
- the substitution `u=sqrt(a) v`;
- norm homogeneity and `sqrt(a)^2=a`;
- `Real.mul_rpow` for positive factors;
- `Real.sqrt_eq_rpow` and `Real.rpow_add` for
  `sqrt(a)^d * a^(-s) = a^(d/2-s)`;
- monotonicity from ball restriction to whole-space lower integral;
- Mathlib Japanese-bracket integrability only for the final finiteness
  corollary.

## Nonclaims

- No variable-base product theorem.
- No residual-base integrability theorem for `a(x)^(d/2-s)`.
- No regular-variable threshold-shift theorem yet.
- No endpoint or divergent-side theorem.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
