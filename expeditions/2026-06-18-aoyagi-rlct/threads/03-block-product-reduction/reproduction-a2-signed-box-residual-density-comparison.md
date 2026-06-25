# Reproduction - A2 signed-box residual/density comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the elementary
signed-box bridge from absolute-monomial loss/density bounds to finite
lower-integral control.

## Scope

This slice proves the signed-box analogue of the positive-box monomial
comparison.  It starts with explicit a.e. bounds on

```text
mu = Measure.pi (i |-> volume.restrict (-R_i,R_i))
```

namely

```text
c * prod_i |x_i|^(2*k_i) <= loss(x),
0 <= density(x),
density(x) <= C * prod_i |x_i|^(h_i),
```

with `R_i>0`, `c>0`, `C>=0`, and `t>=0`.  Under the strict inequalities
`2*t*k_i<h_i+1`, Lean proves finite lower-integral control of

```text
loss(x)^(-t) * density(x).
```

This is independent of the quiver paper and does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, normal-crossing extraction,
or any RLCT theorem.

## One-Dimensional Signed Integrability

For `R>0` and `p>-1`,

```text
int_{-R}^{R} |x|^p dx
  = int_{-R}^{0} (-x)^p dx + int_0^R x^p dx
  = 2 * int_0^R x^p dx
  < infinity.
```

Lean proves this by:

- using Mathlib's positive-interval theorem for `x^p` on `(0,R)`;
- transporting the negative half by the measure-preserving reflection
  `x |-> -x`;
- adding the singleton `{0}`, whose measure is zero;
- combining `(-R,0]` and `(0,R)` into `(-R,R)`.

For finitely many coordinates, `MeasureTheory.Integrable.fintype_prod`
turns the one-dimensional integrability statements into

```text
int^- x, ofReal (prod_i |x_i|^(p_i)) dmu < infinity
```

whenever every `p_i>-1`.  The Aoyagi exponent specialization is
`p_i = h_i - 2*t*k_i`, so the strict hypothesis `2*t*k_i<h_i+1` is exactly
`p_i>-1`.

## Pointwise Loss/Density Calculation

Work at a point away from all coordinate hyperplanes, so every `|x_i|>0`.
Put

```text
M_k(x) = prod_i |x_i|^(2*k_i),
M_h(x) = prod_i |x_i|^(h_i).
```

Then `M_k(x)>0`.  From `c>0` and

```text
c * M_k(x) <= loss(x)
```

we get `loss(x)>0`.  Since `t>=0`, the exponent `-t` is nonpositive, so real
powers reverse order:

```text
loss(x)^(-t) <= (c*M_k(x))^(-t)
              = c^(-t) * M_k(x)^(-t).
```

Multiplying by `density(x)>=0` and then using the density upper bound gives

```text
loss(x)^(-t) * density(x)
  <= c^(-t) * M_k(x)^(-t) * C * M_h(x).
```

Because every `|x_i|>0`,

```text
M_k(x)^(-t)
  = prod_i (|x_i|^(2*k_i))^(-t)
  = prod_i |x_i|^(-2*t*k_i).
```

Combining this with `M_h` coordinate by coordinate gives

```text
M_k(x)^(-t) * M_h(x)
  = prod_i |x_i|^(h_i - 2*t*k_i).
```

Thus

```text
loss(x)^(-t) * density(x)
  <= (c^(-t) * C) * prod_i |x_i|^(h_i - 2*t*k_i).
```

The signed-box product measure is a.e. supported away from every coordinate
hyperplane: for each coordinate the singleton `{0}` has volume zero, and
finite products preserve the a.e. coordinatewise statement.  Therefore the
pointwise comparison applies a.e.; the coordinate hyperplanes require no
pointwise control.

## Lean Shape

Lean proves these theorems in

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

```text
ae_forall_abs_pos_measure_pi_restrict_Ioo_neg
integrableOn_abs_rpow_Ioo_neg_pos
lintegral_ofReal_abs_rpow_restrict_Ioo_neg_lt_top
lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top
lintegral_ofReal_fintype_abs_monomialFactor_signedBox_lt_top
lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top
lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top
loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos
lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top
```

## Role In The Aoyagi Route

This removes the positive-orthant limitation from the elementary monomial
finite-side comparison.  Later work still has to produce the supplied
absolute-monomial loss and density estimates from Aoyagi's actual analytic
charts.

## Nonclaims

- No proof that Aoyagi's product-residual charts satisfy the supplied bounds.
- No density or prior transport theorem from an analytic Jacobian calculation.
- No finite chart cover theorem.
- No endpoint theorem at `2*t*k_i=h_i+1`.
- No divergent-side theorem or threshold equality.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
