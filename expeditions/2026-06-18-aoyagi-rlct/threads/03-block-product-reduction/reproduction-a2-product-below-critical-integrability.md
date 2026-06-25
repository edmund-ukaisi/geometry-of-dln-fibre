# Reproduction - A2 product below-critical integrability

Date: 2026-06-24.

Status: pen-and-paper reproduction for the first product-coordinate analytic
brick after the open-ball radial estimate.

## Scope

This proves only the below-regular-critical case.  If the exponent already
satisfies

```text
2s < dim(E),
```

then adding any nonnegative base loss term over a finite base measure preserves
finiteness of the lower integral over a regular open ball.  This does not prove
the regular-variable `+ dim(E)/2` threshold shift, which requires the harder
case `s >= dim(E)/2` and asymptotic information in the base term.

## Setup

Let `X` be a measurable base space with finite measure `mu`.  Let `E` be a
nontrivial finite-dimensional real normed space with additive Haar measure
`nu`, and let

```text
d = finrank_R(E).
```

Let `a : X -> R` be a base loss term satisfying `a(x) >= 0` almost everywhere.
Let `R > 0`, `s >= 0`, and `2s < d`.

We consider the lower integral on `X x E`

```text
∫ ENNReal.ofReal
    (1_{ball(0,R)}(u) * (a(x) + ||u||^2)^(-s))
  d(mu x nu).
```

The Lean representative writes the ball support as an indicator function.

## Domination

For almost every pair `(x,u)`, we have both

```text
a(x) >= 0
```

and

```text
u != 0.
```

The second condition holds because additive Haar measure on the regular factor
is nonatomic, hence the product measure ignores `X x {0}`.

On the ball and away from the origin,

```text
0 < ||u||^2 <= a(x) + ||u||^2.
```

Since `-s <= 0`, real powers reverse the inequality:

```text
(a(x) + ||u||^2)^(-s) <= (||u||^2)^(-s).
```

Outside the ball, both indicator-extended integrands are zero.  Thus, almost
everywhere,

```text
1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s)
  <=
1_{ball(0,R)}(u) * (||u||^2)^(-s).
```

Passing through `ENNReal.ofReal` preserves this inequality.

## Product Integral

The right-hand side depends only on `u`, so Tonelli's product formula gives

```text
∫_{X x E} g(u) d(mu x nu)
  =
mu(X) * ∫_E g(u) dnu,
```

where

```text
g(u) = ENNReal.ofReal
  (1_{ball(0,R)}(u) * (||u||^2)^(-s)).
```

The regular factor integral is finite by the previously proved open-ball
radial theorem with residual parameter `a = 0`, because `2s < d`.  The base
factor `mu(X)` is finite by hypothesis.  Therefore the product integral is
finite.

## Lean Shape

The intended Lean theorem is:

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

with hypotheses:

```text
[IsFiniteMeasure mu],
[nu.IsAddHaarMeasure],
R > 0,
∀ᵐ x ∂mu, 0 <= a x,
s >= 0,
2*s < finrank_R(E).
```

No measurability of `a` is required for this lower-integral finiteness theorem,
because the proof only uses a.e. domination by a measurable finite-integral
majorant.

## Nonclaims

- No regular-variable `+ dim(E)/2` threshold shift.
- No theorem for `s >= dim(E)/2`.
- No endpoint theorem at `2s = dim(E)`.
- No lower or divergence theorem.
- No uniform asymptotic in the base term.
- No bounded-density/prior transport.
- No Aoyagi p.13 analytic chart or Jacobian theorem.
- No normal-crossing construction, pole order, or RLCT.
