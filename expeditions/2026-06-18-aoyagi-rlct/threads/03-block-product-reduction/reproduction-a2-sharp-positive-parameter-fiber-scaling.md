# Reproduction - A2 sharp positive-parameter fiber scaling

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the fixed
positive-parameter fiber scaling estimate.

## Scope

This slice strengthens the fixed positive-parameter supercritical theorem from
mere finiteness to the sharp parameter dependence.  Let `E` be a
finite-dimensional real normed space with additive Haar measure `mu`, and let

```text
d = finrank_R(E).
```

For `a>0`, the target whole-space identity is

```text
∫ (a + ||u||^2)^(-s) du
  =
a^(d/2-s) * ∫ (1 + ||v||^2)^(-s) dv.
```

The identity itself is a Haar-scaling identity and does not require
`d/2<s`.  The supercritical hypothesis `d/2<s` is used only to know that the
Japanese-bracket integral on the right is finite.

## Change Of Variables

Set

```text
c = sqrt(a).
```

Since `a>0`, we have `c>0` and `c^2=a`.  Use the change of variables

```text
u = c v.
```

Additive Haar measure on a finite-dimensional real vector space scales by

```text
dmu(c v) = c^d dmu(v).
```

Equivalently, for lower integrals of nonnegative functions,

```text
∫ f(c^(-1) u) du = c^d ∫ f(v) dv.
```

The norm calculation is

```text
||c v||^2 = c^2 ||v||^2 = a ||v||^2,
```

so

```text
a + ||c v||^2
  =
a * (1 + ||v||^2).
```

Both factors are positive, hence real powers multiply:

```text
(a * (1 + ||v||^2))^(-s)
  =
a^(-s) * (1 + ||v||^2)^(-s).
```

Putting the measure factor and integrand factor together gives

```text
c^d * a^(-s)
  =
(sqrt(a))^d * a^(-s)
  =
a^(d/2) * a^(-s)
  =
a^(d/2-s).
```

This proves the whole-space scaling identity.

## Ball Bound

For any real radius `R`, the ball-supported lower integral is bounded by the
whole-space lower integral:

```text
∫ 1_{ball(0,R)}(u) (a+||u||^2)^(-s) du
  <=
∫ (a+||u||^2)^(-s) du.
```

Combining with the scaling identity gives

```text
∫ 1_{ball(0,R)}(u) (a+||u||^2)^(-s) du
  <=
a^(d/2-s) * ∫ (1+||v||^2)^(-s) dv.
```

If `d/2<s`, the Japanese-bracket integral is finite, so the ball-supported
positive-parameter fiber integral is finite with the displayed sharp
parameter dependence.

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

```text
lintegral_comp_inv_smul_eq_mul_addHaar
ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul
lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale
lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical
```

The first theorem is the reusable lower-integral Haar-scaling identity.  The
second theorem is the pointwise `ENNReal.ofReal` identity for the positive
parameter square model.  The third theorem is the whole-space scaling equality.
The fourth theorem restricts to a metric ball by monotonicity.  The fifth
theorem combines the ball bound with the Japanese-bracket finiteness theorem.

## Role In The Threshold Picture

This is the fixed-fiber estimate needed before integrating over a residual
base where the parameter is a function `a(x)`.  It supplies the correct
power

```text
a(x)^(d/2-s)
```

that should appear in the next product theorem.

## Nonclaims

- No product theorem with a base function `a(x)` approaching zero.
- No proof that `∫ a(x)^(d/2-s)` is finite in the Aoyagi residual variables.
- No regular-variable `+dim(E)/2` threshold shift theorem yet.
- No endpoint theorem or lower/divergence theorem.
- No uniform asymptotic statement as `a -> 0+`.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT theorem.
