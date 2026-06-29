# Reproduction - A2 regular-suspension reverse threshold shift

Date: 2026-06-29.

Status: pen-and-paper reproduced; Lean formalised for the local model
integral.

## Source Anchor

Aoyagi PDF p. 13 displays the product-difference block

```text
P1 (prod_s A^(s) - [E_r 0; 0 0]) P2
  =
[ C1 - E_r        -F2
  -F3     prod_s C^(s) - F3 F2 ].
```

The regular variables are the entries of `C1 - E_r`, `F2`, and `F3`.
Their count is

```text
k = r^2 + r(H(1)-r) + r(H(L+1)-r)
  = -r^2 + r(H(1)+H(L+1)).
```

The local model after the finite square-sum comparison is

```text
G(x,u) = a(x) + ||u||^2,
```

where `a(x)` is the reduced residual square loss and `u` is the regular
coordinate vector of dimension `k`.

## Reverse Calculation

Let `E` be a finite-dimensional real normed space with additive Haar measure
`nu`.  Put

```text
d = finrank_R(E).
```

Fix a regular ball radius `R > 0` and exponent

```text
s > d/2.
```

Assume locally

```text
a(x) > 0,
a(x) <= R^2
```

for almost every base point.  The second inequality is not cosmetic: it
ensures

```text
ball(0, sqrt(a(x))) subset ball(0, R).
```

For `u` in `ball(0, sqrt(a))`,

```text
||u||^2 <= a,
a + ||u||^2 <= 2a.
```

Since `-s <= 0`, real-power monotonicity gives

```text
(2a)^(-s) <= (a + ||u||^2)^(-s).
```

Integrating over the smaller ball gives the fiber lower bound

```text
ofReal((2a)^(-s)) * nu(ball(0, sqrt(a)))
  <= int^-_u 1_{ball(0,R)}(u) ofReal((a+||u||^2)^(-s)) dnu.
```

Haar scaling gives

```text
nu(ball(0, sqrt(a)))
  = ofReal((sqrt(a))^d) * nu(ball(0,1)).
```

For `a > 0`,

```text
a^(d/2 - s) * 2^(-s)
  = (2a)^(-s) * (sqrt(a))^d.
```

Thus each good fiber satisfies

```text
ofReal(a^(d/2-s)) * (ofReal(2^(-s)) * nu(ball(0,1)))
  <= fiberIntegral(x).
```

Tonelli then integrates this lower bound over the base.  This is where the
reverse direction needs the additional hypothesis

```text
AEMeasurable a mu.
```

The earlier forward theorem avoided measurability by using only
`lintegral_prod_le`; the reverse uses equality with the iterated integral.

## Threshold Form

Set

```text
s = t + d/2.
```

Then

```text
d/2 - s = -t.
```

The lower bound becomes

```text
(int^-_x ofReal(a(x)^(-t)) dmu)
*
(ofReal(2^(-(t+d/2))) * nu(ball(0,1)))
  <=
int^-_(x,u) 1_{ball(0,R)}(u)
  ofReal((a(x)+||u||^2)^(-(t+d/2))) d(mu.prod nu).
```

The constant on the left is nonzero because `2^(-(t+d/2)) > 0` and Haar
measure gives positive mass to `ball(0,1)`.  Therefore finite product
integrability implies finite residual `t`-power integrability.

Together with the previously banked forward theorem, this proves the local
model-integral iff:

```text
product integral at exponent t+d/2 is finite
iff
residual integral of a^(-t) is finite,
```

under `AEMeasurable a`, `R>0`, `t>0`, `a>0` a.e., and `a<=R^2` a.e.

## Why The Upper Bound Is Needed

Without a local upper bound on `a`, the fixed-radius regular fiber can behave
for large `a` like

```text
a^(-(t+d/2)).
```

This may be integrable over an infinite base even when `a^(-t)` is not.  Thus
`a <= R^2` a.e. or an equivalent local restriction is a real hypothesis, not a
Lean artifact.

## Lean Shape

Lean formalises the reverse side in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

with:

```text
ofReal_two_mul_base_rpow_neg_le_ofReal_add_norm_sq_rpow_neg_of_mem_ball_sqrt
fiber_sqrt_ball_lower_le_lintegral_add_norm_sq_pos
base_power_scale_le_lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball
base_power_scale_le_lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod
lintegral_ofReal_base_power_lt_top_of_product_lt_top
lintegral_ofReal_residual_power_lt_top_of_product_lt_top
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_iff_residual_power_lt_top
```

The focused build passed with

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
```

## Nonclaims

- No original source-prior or Jacobian transport.
- No p. 13 analytic chart coverage.
- No proof that Aoyagi's residual coordinates satisfy the residual
  integrability hypothesis.
- No treatment of a positive-measure zero set of `a`.
- No removal of the local upper bound `a <= R^2`.
- No pole-order statement.
- No normal-crossing construction or RLCT extraction.
