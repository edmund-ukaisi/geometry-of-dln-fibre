# Reproduction - A2 variable-base product fiber integrability

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the first
variable-base product theorem using the sharp fixed-fiber estimate.

## Scope

Let `E` be a finite-dimensional real normed space with additive Haar measure
`nu`, let `mu` be a measure on a base space `alpha`, and write

```text
d = finrank_R(E),       p = d/2 - s.
```

The theorem proves product finiteness for

```text
(a(x) + ||u||^2)^(-s)
```

on `alpha x ball(0,R)` when:

```text
a(x) > 0  for mu-a.e. x,
d/2 < s,
∫⁻ x, ENNReal.ofReal (a(x)^p) dmu < infinity.
```

The base measure need not be finite.  The base-side size is entirely carried
by the displayed lower-integral hypothesis.

## Fiber Bound

The previous sharp fixed-parameter theorem gives, for every `a0>0`,

```text
∫⁻ u, ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a0 + ||u||^2)^(-s)) dnu
<=
ENNReal.ofReal (a0^p) * K,
```

where

```text
K = ∫⁻ v, ENNReal.ofReal ((1 + ||v||^2)^(-s)) dnu.
```

Under `d/2<s`, the Japanese-bracket theorem gives

```text
K < infinity.
```

Applying this with `a0=a(x)` is legitimate for `mu`-a.e. `x` by the strict
positivity hypothesis.

## Product Estimate

Let

```text
F(x,u)
  =
ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s)).
```

For nonnegative lower integrals, Tonelli's inequality gives

```text
∫⁻ z, F(z) d(mu.prod nu)
  <=
∫⁻ x, ∫⁻ u, F(x,u) dnu dmu.
```

Using the fiber bound for a.e. `x`,

```text
∫⁻ x, ∫⁻ u, F(x,u) dnu dmu
  <=
∫⁻ x, ENNReal.ofReal (a(x)^p) * K dmu.
```

Since `K < infinity`, the constant can be pulled out:

```text
∫⁻ x, ENNReal.ofReal (a(x)^p) * K dmu
  =
(∫⁻ x, ENNReal.ofReal (a(x)^p) dmu) * K
  <
infinity.
```

This proves the product lower integral is finite.

## Why Strict Positivity

In the supercritical range, `p=d/2-s<0`.  The intended singular behavior at
`a=0` is not represented by a useful finite real number.  Lean's `Real.rpow`
is totalized, so a theorem phrased with only `0 <= a(x)` could silently say
the wrong thing at zeros.  This slice therefore assumes `0<a(x)` a.e. and
separates the remaining zero-set analysis from the base-power theorem.

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top
```

The first theorem is the product bound by the base-power integral times the
Japanese-bracket constant.  The second theorem combines that bound with the
finite-base-power hypothesis and `K<infinity`.

The proof uses `lintegral_prod_le`, so it does not need an a.e.-measurability
hypothesis for the product integrand or for `a`.  It also does not require
`mu` to be a finite measure.

## Role In The Threshold Picture

This is the variable-base measure-theoretic bridge promised by the sharp
fiber estimate.  A remaining finite-side input for Aoyagi's source variables
is to prove the residual-base hypothesis

```text
∫⁻ x, ENNReal.ofReal (a(x)^(d/2-s)) dmu < infinity
```

from the reduced residual model.  Endpoint, lower/divergence,
bounded-density, chart/Jacobian, and RLCT extraction questions remain separate.

## Nonclaims

- No proof of the residual-base integrability hypothesis.
- No theorem covering a positive-measure zero set of `a`.
- No endpoint theorem or lower/divergence theorem.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT theorem.
