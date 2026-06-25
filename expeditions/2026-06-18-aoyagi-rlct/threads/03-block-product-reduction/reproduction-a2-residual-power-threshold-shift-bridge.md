# Reproduction - A2 residual-power threshold-shift bridge

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the finite-side
residual-power form of the variable-base product theorem.

## Scope

Let `E` be a finite-dimensional real normed space with additive Haar measure
`nu`, let `mu` be a measure on a base space `alpha`, and let

```text
a : alpha -> R
```

be the residual square-loss parameter.  The intended regular-square model is

```text
a(x) + ||u||^2
```

on `alpha x ball(0,R)`.  Write

```text
d = finrank_R(E).
```

This slice proves the finite-side threshold-shift implication:

```text
a(x) > 0  for mu-a.e. x,
t > 0,
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity
```

imply

```text
∫⁻ (x,u), ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-(t+d/2))) d(mu.prod nu)
<
infinity.
```

The base measure need not be finite, and no measurability hypothesis on `a` is
used because the proof uses lower-integral inequalities.

## Calculation

The already-proved variable-base theorem says that for an exponent `s` with

```text
d/2 < s,
```

the product lower integral of `(a(x)+||u||^2)^(-s)` over
`alpha x ball(0,R)` is bounded by

```text
(∫⁻ x, ENNReal.ofReal (a(x)^(d/2-s)) dmu)
*
(∫⁻ u, ENNReal.ofReal ((1+||u||^2)^(-s)) dnu).
```

Set

```text
s = t + d/2.
```

Then `t>0` gives `d/2 < s`, and the base exponent becomes

```text
d/2 - s = d/2 - (t+d/2) = -t.
```

Thus the finite base integral required by the variable-base theorem is exactly

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity.
```

The Japanese-bracket factor is finite by the supercritical theorem because
`d/2<s`.  Multiplying two finite `ENNReal` values gives the desired product
finiteness.

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

```text
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale
lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top
```

The first theorem is the explicit product bound after substituting
`s=t+d/2`.  The second theorem combines it with the finite residual
negative-power hypothesis.

## Role In The Aoyagi Route

This theorem is the finite-side analytic bridge matching the informal
threshold shift

```text
tau(a + ||u||^2) >= tau(a) + d/2
```

for exponents strictly below the shifted threshold.  It is not a complete
threshold equality and does not address the endpoint or divergent side.

For Aoyagi p. 13, a later slice still has to prove that the reduced residual
model supplies the base hypothesis

```text
∫⁻ x, ENNReal.ofReal (a(x)^(-t)) dmu < infinity
```

for the relevant `t`, after the actual analytic chart and density/prior
transport have been constructed or supplied.

## Nonclaims

- No proof that Aoyagi's reduced residual coordinates satisfy the residual
  negative-power hypothesis.
- No theorem for a positive-measure zero set of `a`.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No bounded-density/prior transport theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT extraction.
