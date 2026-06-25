# Reproduction - A2 positive-box residual/density comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the elementary
positive-box bridge from separate loss and density bounds to monomial
domination.

## Scope

This slice proves a positive-box finite-side comparison.  It starts with
explicit a.e. bounds

```text
c * prod_i x_i^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i x_i^(h_i),
```

on the product positive-box measure, with `c>0`, `C>=0`, and `t>=0`.  Under
the strict inequalities `2*t*k_i<h_i+1`, Lean proves finite lower-integral
control of

```text
loss(x)^(-t) * density(x).
```

This is independent of the quiver paper and does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, normal-crossing extraction,
or any RLCT theorem.

## Calculation

Work at a point in the positive box, so every coordinate satisfies `x_i>0`.
Put

```text
M_k(x) = prod_i x_i^(2*k_i),
M_h(x) = prod_i x_i^(h_i).
```

Then `M_k(x)>0`.  From `c>0` and

```text
c * M_k(x) <= loss(x)
```

we get `loss(x)>0`.  Since `t>=0`, the exponent `-t` is nonpositive, so the
real-power order reverses:

```text
loss(x)^(-t) <= (c*M_k(x))^(-t)
              = c^(-t) * M_k(x)^(-t).
```

Multiplying by `density(x)>=0` gives

```text
loss(x)^(-t) * density(x)
  <= c^(-t) * M_k(x)^(-t) * density(x).
```

The density upper bound then gives

```text
loss(x)^(-t) * density(x)
  <= c^(-t) * M_k(x)^(-t) * C * M_h(x).
```

Because every `x_i>0`,

```text
M_k(x)^(-t)
  = prod_i (x_i^(2*k_i))^(-t)
  = prod_i x_i^(-2*t*k_i).
```

Combining this with `M_h` coordinate by coordinate gives

```text
M_k(x)^(-t) * M_h(x)
  = prod_i x_i^(h_i - 2*t*k_i).
```

Thus

```text
loss(x)^(-t) * density(x)
  <= (c^(-t) * C) * prod_i x_i^(h_i - 2*t*k_i).
```

The constant `A=c^(-t)*C` is nonnegative because `c>0` and `C>=0`.  The
landed positive-box monomial domination theorem then proves the finite
lower-integral conclusion under `2*t*k_i<h_i+1`.

## Lean Shape

Lean proves these theorems in

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

```text
ae_forall_pos_measure_pi_restrict_Ioo
loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos
lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top
```

The first lemma records that the positive-box product measure is a.e.
supported on points with all coordinates positive.  The pointwise helper
performs the elementary real-power calculation.  The finite theorem feeds the
resulting a.e. upper bound into
`lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top`.

## Role In The Aoyagi Route

This is the first theorem in the monomial-chart direction that derives the
landed domination hypothesis from separate loss and density estimates.  Later
work still has to produce those estimates from Aoyagi's actual analytic
charts, and still has to handle signed boxes or absolute values.

## Nonclaims

- No signed-box or absolute-value monomial theorem.
- No proof that Aoyagi's product-residual charts satisfy the supplied bounds.
- No density or prior transport theorem from an analytic Jacobian calculation.
- No finite chart cover theorem.
- No endpoint theorem at `2*t*k_i=h_i+1`.
- No divergent-side theorem or threshold equality.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
