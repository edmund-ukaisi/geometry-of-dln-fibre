# Reproduction - A2 regular square-suspension integrability target

Date: 2026-06-24.

Status: pen-and-paper target statement; not yet formalised in Lean.

## Source-Motivated Role

Aoyagi PDF p. 13 asserts the regular-variable contribution after separating
the p. 13 block variables.  The finite source-side work now proves that the
literal full p. 13 block square-sum is locally comparable with

```text
regularBlockSquareSum + residualBlockSquareSum.
```

The next analytic theorem needed independently of Aoyagi Lemma 1 and Theorem 4
is a product-coordinate integrability statement for adding regular square
variables to a residual loss.

## Target Theorem

Let `k >= 1`.  Let `U` be a small ball in `R^k`, let `V` be a finite-measure
neighborhood in `R^m`, and let

```text
g : V -> [0, infinity]
```

be measurable and nonnegative.  Let `F` be a nonnegative measurable full loss
on `U x V`, and let `rho` be a measurable density.  Assume there are positive
constants `a`, `A`, `b`, and `B` such that on `U x V`

```text
a * (|u|^2 + g y) <= F (u,y) <= A * (|u|^2 + g y),
b <= rho (u,y) <= B.
```

For the local power-integrability threshold

```text
tau(h) = sup { t >= 0 : h^(-t) is locally integrable },
```

the target conclusion is

```text
tau(F with density rho) = k/2 + tau(g).
```

More concretely, after comparability reduces to the model loss

```text
G(u,y) = |u|^2 + g(y),
```

Fubini and polar coordinates give

```text
integral_U (|u|^2 + a)^(-t) du
  = const * integral_0^eps r^(k-1) (r^2 + a)^(-t) dr.
```

If `t < k/2`, the inner integral is uniformly finite in `a >= 0`.

If `t > k/2`, the substitution `r = sqrt(a) s` gives

```text
integral_U (|u|^2 + a)^(-t) du  asymp  a^(k/2 - t),
```

with both sides infinite at `a = 0`.  Therefore, for `t > k/2`,

```text
G^(-t) is locally integrable on U x V
  iff
g^(-(t-k/2)) is locally integrable on V.
```

The borderline `t = k/2` is irrelevant for the threshold equality.

## Aoyagi p.13 Specialisation

For p. 13, the regular dimension is

```text
c = r^2 + r(H^(L+1)-r) + (H^(1)-r)r,
```

so the threshold shift is `c/2`, which is the already formalised
`aoyagiTheorem2RegularTerm L H r` under the endpoint bounds.

The finite source-side comparison now supplies the model-loss comparability
input, but only after a genuine analytic chart has provided product
coordinates and a bounded positive density.

## Lean Implications

This theorem is larger than the current Aoyagi-specific source-side algebra.
Formalising it would likely require a separate analytic/measure-theory module
with:

- a local integrability-threshold definition;
- product-measure Fubini/Tonelli setup for Euclidean balls;
- polar-coordinate integral estimates for `(|u|^2 + a)^(-t)`;
- comparability lemmas for bounded positive densities and equivalent losses.

It should not mention normal-crossing certificates or RLCT extraction.  Once a
full p. 13 analytic regular-suspension chart is constructed, this theorem can
justify the regular square-variable threshold shift before the single allowed
normal-crossing extraction citation is applied elsewhere.

## Nonclaims

- No Lean formalisation yet.
- No construction of the p. 13 analytic product chart.
- No proof of chart coverage or Jacobian/prior compatibility for Aoyagi's
  variables.
- No pole-order theorem.
- No use of Aoyagi Lemma 1 or Theorem 4.
- No normal-crossing-to-RLCT extraction.
