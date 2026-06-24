# Reproduction - A2 radial finite-side integrability

Date: 2026-06-24.

Status: pen-and-paper reproduction for a narrow radial Lean brick.

## Scope

This is the first radial estimate behind the regular-square theorem.  It
proves only the finite side below the critical exponent.  It does not prove a
threshold theorem, a lower/divergence estimate, a uniform asymptotic in the
residual parameter, Aoyagi's p. 13 analytic chart, or any RLCT extraction.

## Radial Model

Let `E` be a nontrivial finite-dimensional real normed space with additive
Haar measure `mu`, and set

```text
d = finrank_R(E).
```

For a radial function `f(||x||)`, Mathlib's Haar-to-sphere formula reduces
integrability over `E` to one-dimensional integrability on `(0,infinity)`:

```text
Integrable (x |-> f(||x||)) dmu
  iff
IntegrableOn (r |-> r^(d-1) f(r)) (0,infinity).
```

Take

```text
f(r) = 1_(0,R)(r) * r^(-t).
```

This notation means the indicator-extension by zero used in Lean:
outside `(0,R)`, the function is zero and does not evaluate the negative power
at the origin.

Then the one-dimensional integrand is, on `(0,R)`,

```text
r^(d-1) * r^(-t) = r^(d-1-t).
```

The standard real-power criterion says

```text
r^q is integrable on (0,R) iff -1 < q.
```

Thus the radial model is integrable when

```text
-1 < d - 1 - t,
```

equivalently `t < d`.

## Shifted Quadratic Finite Side

For the regular-square integrand, take real parameters

```text
a >= 0,  s >= 0,  R > 0,
```

and consider

```text
1_(0,R)(||x||) * (||x||^2 + a)^(-s).
```

Again, this is the indicator-extension by zero, not a real-power evaluation at
`||x|| = 0`.

On the punctured radial interval `0 < r < R`, we have

```text
r^2 <= r^2 + a.
```

Since `-s <= 0`, real powers reverse this inequality:

```text
(r^2 + a)^(-s) <= (r^2)^(-s).
```

For `r > 0`,

```text
(r^2)^(-s) = r^(-2s).
```

Therefore

```text
1_(0,R)(||x||) * (||x||^2 + a)^(-s)
  <=
1_(0,R)(||x||) * ||x||^(-2s).
```

The radial model with `t = 2s` proves integrability whenever

```text
2s < d.
```

This is exactly the finite side for the zero-residual critical exponent
`s < d/2`, but it is stated without claiming endpoint behavior or the final
threshold shift.

## Why the Punctured Radius Interval Appears

The formula uses `1_(0,R)(||x||)`, not `1_[0,R](||x||)`.  This avoids making a
direct real-valued claim at the origin, where negative powers are singular.
For nontrivial additive Haar measure on a finite-dimensional real normed
space, the origin is null, so later work can replace punctured balls by balls
only after proving and applying the corresponding null-set transfer.

## Lean Shape

The Lean theorem family is:

```text
integrable_norm_rpow_neg_indicator_Ioo
integrable_norm_sq_add_rpow_neg_indicator_Ioo
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top
```

The last theorem is only an `ENNReal.ofReal` lower-integral finiteness handoff
from the real-valued integrability theorem.

## Nonclaims

- No lower bound or divergence theorem.
- No endpoint theorem at `2s = d`.
- No uniform bound in `a`.
- No asymptotic comparison to `a^(d/2-s)`.
- No product-coordinate threshold theorem.
- No Aoyagi p. 13 analytic chart, density, or Jacobian construction.
- No normal-crossing construction, pole order, or RLCT theorem.
