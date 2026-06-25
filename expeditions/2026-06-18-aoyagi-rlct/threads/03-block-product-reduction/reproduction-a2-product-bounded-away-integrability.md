# Reproduction - A2 product bounded-away integrability

Date: 2026-06-25.

Status: pen-and-paper reproduction for the regular-ball product estimate away
from the residual zero set.

## Scope

This is a local nonsingularity brick for the regular-square suspension
picture.  If the residual/base term is bounded below by a positive constant on
the base factor, then adding regular square variables does not create a
singularity on a bounded regular ball.  The estimate is valid for every
nonnegative exponent `s`; it does not compute the threshold at the residual
zero set.

## Setup

Let `X` be a measurable base space with finite measure `mu`.  Let `E` be a
nontrivial finite-dimensional real normed space with additive Haar measure
`nu`.  Let

```text
a : X -> R,
epsilon > 0,
s >= 0.
```

Assume

```text
epsilon <= a(x)
```

for `mu`-almost every `x`.

We consider the lower integral over `X x E`

```text
∫ ENNReal.ofReal
    (1_{ball(0,R)}(u) * (a(x) + ||u||^2)^(-s))
  d(mu x nu).
```

No positivity hypothesis on `R` is needed for this estimate: every metric ball
has finite additive Haar measure in a finite-dimensional real normed space.
If `R <= 0`, the ball is empty.

## Pointwise Bound

For almost every pair `(x,u)`,

```text
epsilon <= a(x) <= a(x) + ||u||^2.
```

Since `epsilon > 0` and `-s <= 0`, real powers reverse the inequality:

```text
(a(x) + ||u||^2)^(-s) <= epsilon^(-s).
```

Multiplying by the ball indicator gives the pointwise majorization

```text
1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s)
  <=
1_{ball(0,R)}(u) * epsilon^(-s).
```

Passing through `ENNReal.ofReal` preserves this inequality.

## Product Integral

The right-hand side depends only on the regular variable:

```text
g(u) = ENNReal.ofReal (epsilon^(-s))  on ball(0,R),
g(u) = 0                              outside ball(0,R).
```

Its regular-factor lower integral is finite because

```text
∫ g dnu = ENNReal.ofReal(epsilon^(-s)) * nu(ball(0,R)),
```

and both factors are finite.  Tonelli/product factorization gives

```text
∫_{X x E} g(u) d(mu x nu)
  =
mu(X) * ∫_E g(u) dnu,
```

which is finite because `mu` is finite.  The original product lower integral
is bounded by this finite majorant.

## Lean Shape

Lean theorem:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
```

Hypotheses:

```text
[IsFiniteMeasure mu],
[nu.IsAddHaarMeasure],
epsilon > 0,
forall mu-a.e. x, epsilon <= a x,
s >= 0.
```

Conclusion:

```text
∫⁻ z : alpha x E, ENNReal.ofReal
  (1_{ball(0,R)}(z.2) * (a(z.1)+||z.2||^2)^(-s))
  d(mu.prod nu)
< infinity.
```

## Role In The Threshold Picture

This proves the easy away-from-zero side: over a base region where the
residual loss is bounded below, regular square variables contribute no local
singularity.  The true threshold-shift theorem still has to analyze
neighborhoods where `a(x)` can approach zero and control the fiber integral in
terms of a negative power of `a(x)`.

## Nonclaims

- No regular-variable `+ dim(E)/2` threshold shift.
- No theorem for the singular base region where `a(x)` approaches zero.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT theorem.
