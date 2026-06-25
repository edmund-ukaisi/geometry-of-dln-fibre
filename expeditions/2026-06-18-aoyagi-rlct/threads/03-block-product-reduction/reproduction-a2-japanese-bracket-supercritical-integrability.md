# Reproduction - A2 Japanese-bracket supercritical integrability

Date: 2026-06-25.

Status: pen-and-paper reproduction for the global supercritical finite-side
model and fixed positive-parameter comparison.

## Scope

This is the first supercritical analytic brick after the below-critical and
bounded-away product estimates.  It proves global finiteness for the model

```text
(1 + ||x||^2)^(-s)
```

when

```text
finrank_R(E) / 2 < s,
```

and then proves global finiteness for each fixed positive parameter

```text
(a + ||x||^2)^(-s),  a > 0.
```

It does not yet prove the sharp scaled bound by
`a^(finrank_R(E)/2-s)`, and it does not prove a product theorem over a base
where `a=a(y)` can approach zero.

## Japanese-Bracket Model

Mathlib's Japanese-bracket theorem says that for additive Haar measure on a
finite-dimensional real normed space,

```text
((1 : R) + ||x||^2)^(-r/2)
```

is integrable whenever

```text
finrank_R(E) < r.
```

Set

```text
r = 2s.
```

The hypothesis `finrank_R(E)/2 < s` is equivalent to

```text
finrank_R(E) < 2s,
```

so Mathlib gives integrability of

```text
((1 : R) + ||x||^2)^(-(2s)/2)
  =
((1 : R) + ||x||^2)^(-s).
```

Since the integrand is nonnegative, real integrability gives finiteness of the
`ENNReal.ofReal` lower integral.

## Fixed Positive Parameter

Let `a > 0`.  Put

```text
c = min(a,1).
```

Then `c > 0`, `c <= a`, and `c <= 1`.  Hence for every `x`,

```text
c * (1 + ||x||^2) <= a + ||x||^2.
```

Because `s >= 0`, the exponent `-s` is nonpositive and real powers reverse the
inequality:

```text
(a + ||x||^2)^(-s)
  <=
(c * (1 + ||x||^2))^(-s).
```

By positivity of both factors,

```text
(c * (1 + ||x||^2))^(-s)
  =
c^(-s) * (1 + ||x||^2)^(-s).
```

The right-hand side is a constant multiple of the Japanese-bracket model, so
it is integrable.  Therefore

```text
∫⁻ x, ENNReal.ofReal ((a + ||x||^2)^(-s)) < infinity.
```

## Lean Shape

Lean proves:

```text
integrable_one_add_norm_sq_rpow_neg
lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
```

in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

## Role In The Threshold Picture

This proves that the regular fiber is globally integrable in the supercritical
range once the residual parameter is fixed positive.  The next needed theorem
is the sharp parameter-dependent bound

```text
∫ (a + ||u||^2)^(-s) du <= C * a^(finrank_R(E)/2 - s),
```

for `a > 0` and `finrank_R(E)/2 < s`.  That bound is what can be integrated
over the residual base to prove the regular-variable threshold shift.

## Nonclaims

- No sharp `a^(finrank/2-s)` dependence.
- No product theorem with a base function `a(y)` approaching zero.
- No regular-variable `+ dim(E)/2` threshold shift.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT theorem.
