# Statement Card - A2 radial finite-side integrability

Date: 2026-06-24.

## Claim

Let `E` be a nontrivial finite-dimensional real normed space with additive Haar
measure `mu`, and let `d = finrank_R(E)`.

For `R > 0`, the punctured radial model

```text
x |-> 1_(0,R)(||x||) * ||x||^(-t)
```

is integrable when `t < d`.  The displayed expression is the
indicator-extension by zero; it is not evaluated as a negative power at the
origin.

Consequently, for `a >= 0`, `s >= 0`, and `2s < d`,

```text
x |-> 1_(0,R)(||x||) * (||x||^2 + a)^(-s)
```

is integrable.  This is likewise the indicator-extension by zero.  Its
`ENNReal.ofReal` lower integral is finite.

## Lean Artifacts

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.integrable_norm_rpow_neg_indicator_Ioo
DLNFibre.DLN.Aoyagi.integrable_norm_sq_add_rpow_neg_indicator_Ioo
DLNFibre.DLN.Aoyagi.lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
```

## Proof Ingredients

- `MeasureTheory.integrable_fun_norm_addHaar`;
- `intervalIntegral.integrableOn_Ioo_rpow_iff`;
- the identity `r^(d-1) * r^(-t) = r^(d-1-t)` on `r > 0`;
- comparison `(r^2+a)^(-s) <= r^(-2s)` for `r > 0`, `a >= 0`, `s >= 0`;
- `lintegral_enorm_of_nonneg` for the `ENNReal.ofReal` handoff.

## Nonclaims

- No regular-variable `+k/2` threshold shift.
- No polar-coordinate equality for Euclidean balls.
- No lower or divergence side.
- No endpoint result at `2s = d`.
- No uniform asymptotic in `a`.
- No bounded-density or product-coordinate theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
