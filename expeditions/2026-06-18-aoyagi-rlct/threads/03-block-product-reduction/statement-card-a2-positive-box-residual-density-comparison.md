# Statement Card - A2 positive-box residual/density comparison

Date: 2026-06-25.

## Claim

Let

```text
mu = Measure.pi (i |-> volume.restrict (0,R_i)).
```

Assume `R_i>0`, `c>0`, `C>=0`, `t>=0`, and

```text
2*t*k_i < h_i + 1
```

for every coordinate.  If, for `mu`-a.e. `x`,

```text
c * prod_i x_i^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i x_i^(h_i),
```

then

```text
int^- x, ofReal(loss(x)^(-t) * density(x)) dmu < infinity.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.ae_forall_pos_measure_pi_restrict_Ioo
DLNFibre.DLN.Aoyagi.loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
DLNFibre.DLN.Aoyagi.lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top
```

## Proof Ingredients

- positive-coordinate support of the positive-box product measure;
- `Real.rpow_le_rpow_of_nonpos`;
- `Real.mul_rpow`, `Real.rpow_mul`, and `Real.rpow_add`;
- `Real.finset_prod_rpow`;
- finite product positivity and nonnegativity;
- `lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top`.

## Nonclaims

- No signed-box or absolute-value theorem.
- No proof of Aoyagi chart construction or chart coverage.
- No proof of the residual lower bound for the actual p.13 residual.
- No analytic density/Jacobian transport theorem.
- No endpoint, divergent-side, or threshold equality theorem.
- No normal-crossing construction, pole order, or RLCT.
