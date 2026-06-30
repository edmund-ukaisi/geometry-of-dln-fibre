# Reproduction - A2 external source product-domination handoff

Date: 2026-06-30.

## Goal

Record the measure-theoretic handoff needed by Target B.  The theorem should
not construct an original DLN source prior.  It should only say that, once an
external source measure is already known to be locally dominated by the
chart-produced source measure with a finite scalar, finite product integrals
transfer to that external measure.

## Calculation

Let `mu` be the chart-produced source measure on a local source set and let
`nu` be an external source measure restricted to the same local set.  Let
`eta` be an s-finite regular-coordinate measure, usually a Haar measure on
the regular variables.

Assume the explicit finite-scalar domination

```text
nu <= c * mu
```

with `c < infinity`.  For any measurable product set `A`,
Fubini/`Measure.prod_apply` gives

```text
(nu x eta)(A)
  = integral_x eta({y | (x,y) in A}) dnu(x).
```

Since `nu <= c * mu`,

```text
integral_x eta(A_x) dnu(x)
  <= integral_x eta(A_x) d(c * mu)(x)
   = c * integral_x eta(A_x) dmu(x)
   = c * (mu x eta)(A).
```

Thus

```text
nu.prod eta <= c * mu.prod eta.
```

Consequently, for any nonnegative integrand `F`,

```text
integral F d(nu.prod eta)
  <= integral F d(c * mu.prod eta)
   = c * integral F d(mu.prod eta).
```

If the right-hand product integral is finite and `c < infinity`, then the
external-source product integral is finite.

## Boundary

This is only a domination consumer.  It does not prove that the original DLN
source prior is dominated by any retained-passive or passive-theta
chart-produced measure.  It also does not provide a local inverse, source-image
coverage, Jacobian comparison for the external prior, normal crossings, pole
order, or RLCT extraction.
