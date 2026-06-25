# Statement Card - A2 signed-box residual/density comparison

Date: 2026-06-25.

## Claim

Let

```text
mu = Measure.pi (i |-> volume.restrict (-R_i,R_i)).
```

Assume `R_i>0`, `c>0`, `C>=0`, `t>=0`, and

```text
2*t*k_i < h_i + 1
```

for every coordinate.  If, for `mu`-a.e. `x`,

```text
c * prod_i |x_i|^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i |x_i|^(h_i),
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
DLNFibre.DLN.Aoyagi.ae_forall_abs_pos_measure_pi_restrict_Ioo_neg
DLNFibre.DLN.Aoyagi.integrableOn_abs_rpow_Ioo_neg_pos
DLNFibre.DLN.Aoyagi.lintegral_ofReal_abs_rpow_restrict_Ioo_neg_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_fintype_abs_monomialFactor_signedBox_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top
DLNFibre.DLN.Aoyagi.loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos
DLNFibre.DLN.Aoyagi.lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
```

## Proof Ingredients

- a.e. nonzero-coordinate support of the signed-box product measure;
- one-dimensional split of `|x|^p` into positive and reflected negative
  halves;
- `Measure.measurePreserving_neg`;
- `MeasureTheory.Integrable.fintype_prod`;
- `Real.rpow_le_rpow_of_nonpos`;
- `Real.mul_rpow`, `Real.rpow_mul`, and `Real.rpow_add`;
- `Real.finset_prod_rpow`;
- finite product positivity and nonnegativity;
- lower-integral monotonicity and constant extraction.

## Nonclaims

- No proof of Aoyagi chart construction or chart coverage.
- No proof of the residual lower bound for the actual p.13 residual.
- No analytic density/Jacobian transport theorem.
- No endpoint, divergent-side, or threshold equality theorem.
- No normal-crossing construction, pole order, or RLCT.
