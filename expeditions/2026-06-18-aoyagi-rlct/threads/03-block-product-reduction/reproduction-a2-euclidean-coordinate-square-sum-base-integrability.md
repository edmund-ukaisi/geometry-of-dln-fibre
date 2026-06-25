# Reproduction - A2 Euclidean coordinate square-sum base integrability

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a local
Euclidean residual-coordinate model.

## Scope

This slice proves a concrete finite-dimensional base-integrability fact for
Aoyagi's square-sum convention when the base variables themselves are Euclidean
coordinates:

```text
S(x) = aoyagiCoordinateSquareSum (fun i => x_i) = sum_i x_i^2.
```

It is independent of the quiver paper and does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, or regular-coordinate additivity.  It also does not prove
the corresponding fact for Aoyagi's actual residual product map
`D = prod_s C^(s)`.

## Calculation

Let `eta` be a finite nonempty index type and let
`x : EuclideanSpace ℝ eta`.  Mathlib's Euclidean space is the `L^2` Pi space,
so

```text
||x||^2 = sum_i x_i^2.
```

Therefore

```text
aoyagiCoordinateSquareSum (fun i => x_i) = ||x||^2.
```

If `x != 0`, then `||x|| > 0`, hence `||x||^2 > 0`, so `S(x)>0`.
For a nonatomic measure, the singleton `{0}` has measure zero; hence

```text
S(x)>0
```

almost everywhere.

For the lower-integral estimate, the existing radial theorem proves that, on a
finite-dimensional real normed vector space with additive Haar measure,

```text
∫_ball(0,R) ofReal((||x||^2+a)^(-t)) dx < infinity
```

when

```text
R>0,  a>=0,  t>=0,  2*t < finrank_R(E).
```

Apply this with

```text
E = EuclideanSpace ℝ eta,
a = 0,
finrank_R(E) = card eta.
```

Using `||x||^2 = S(x)`, this gives

```text
∫_ball(0,R) ofReal(S(x)^(-t)) dx < infinity
```

for

```text
R>0,  t>=0,  2*t < card eta.
```

The restricted-measure form follows because, for the measurable ball,

```text
∫ x, ball.indicator f x dmu
  = ∫ x, f x d(mu.restrict ball).
```

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

```text
aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero
ae_aoyagiEuclideanCoordinateSquareSum_pos
ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top
lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

The lower-integral theorems use an arbitrary additive Haar measure on
`EuclideanSpace ℝ eta`; the a.e. positivity theorem uses only nonatomicity.
The final theorem composes these two inputs with the existing variable-base
square-model product estimate.

## Role In The Aoyagi Route

This closes the simplest residual-base model: a finite coordinate vector with
loss `sum_i x_i^2` has the expected local negative-power integrability
threshold `card eta / 2`.  The composed product theorem feeds this base
integrability directly into the square-suspension product socket when the base
measure is restricted to a coordinate ball.

The actual Aoyagi residual model is not a free coordinate vector.  It is a
product residual `D = prod_s C^(s)`, and proving its negative-power
integrability remains a separate residual normal-crossing/product-map task.

## Nonclaims

- No proof of residual-base integrability for `D = prod_s C^(s)`.
- No proof that the p.13 residual product coordinates are locally equivalent
  to independent Euclidean coordinates.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No use of Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate
  additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
