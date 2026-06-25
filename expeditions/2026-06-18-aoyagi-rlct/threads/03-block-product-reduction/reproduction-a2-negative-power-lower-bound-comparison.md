# Reproduction - A2 negative-power lower-bound comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a model-loss
comparison brick.

## Scope

The next residual-base target is a monomial-chart integrability criterion.
One reusable elementary step is this comparison:

```text
if b(x) >= c * a(x) with c>0,
then b(x)^(-t) <= c^(-t) * a(x)^(-t)
```

for `t>=0`, on points where `a(x)>0`.  This slice formalises exactly that
lower-integral transfer.

It is independent of the quiver paper and does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, normal-crossing extraction,
or any RLCT theorem.

## Calculation

Assume

```text
c > 0,
t >= 0,
a(x) > 0,
c * a(x) <= b(x).
```

Then `c*a(x)>0`.  Since the exponent `-t` is nonpositive, real powers reverse
order on the positive half-line:

```text
b(x)^(-t) <= (c*a(x))^(-t).
```

The positive-factor rule gives

```text
(c*a(x))^(-t) = c^(-t) * a(x)^(-t).
```

Therefore, pointwise almost everywhere,

```text
ofReal(b(x)^(-t))
  <= ofReal(c^(-t)) * ofReal(a(x)^(-t)).
```

Taking lower integrals and pulling out the constant gives

```text
∫ ofReal(b(x)^(-t))
  <= ofReal(c^(-t)) * ∫ ofReal(a(x)^(-t)).
```

Thus finiteness of the `a`-integral implies finiteness of the `b`-integral.

## Lean Shape

Lean proves the following in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

```text
lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
```

The theorem is stated for an arbitrary measure space and arbitrary real-valued
functions `a,b : alpha -> ℝ`.  The positivity and lower-bound assumptions are
almost-everywhere assumptions, so the theorem can be applied directly to
restricted local chart measures.

## Role In The Aoyagi Route

This is a comparison socket for residual monomial charts.  Later, if a chart
proves

```text
residualLoss(z) >= c * monomialModel(z),
```

then finite negative-power integrability of the monomial model transfers to
the residual loss.

## Nonclaims

- No proof that any Aoyagi residual chart satisfies such a lower bound.
- No proof of monomial integrability.
- No finite chart cover theorem.
- No bounded-density/prior theorem.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
