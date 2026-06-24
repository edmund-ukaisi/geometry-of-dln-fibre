# Reproduction - A2 null-origin radial integrability transfer

Date: 2026-06-24.

Status: pen-and-paper reproduction for a narrow null-origin transfer brick.

## Scope

This is the next bridge after the punctured radial finite-side theorem.  It
removes the puncture at the origin only up to almost-everywhere equality for a
nonatomic additive Haar measure.  It does not prove endpoint behavior,
divergence, uniform asymptotics, bounded-density transport, a product-coordinate
threshold theorem, Aoyagi's p.13 analytic chart/Jacobian construction, normal
crossings, pole order, or RLCT.

## Null-Origin Equality

Let `E` be a normed additive group with a measure `mu` satisfying
`NoAtoms mu`.  Then `{0}` is null, equivalently `x != 0` for `mu`-almost every
`x`.

For any function `phi : R -> beta` with `beta` carrying a zero value, compare
the two radial indicator-extensions by zero

```text
x |-> 1_(0,R)(||x||) * phi(||x||)
x |-> 1_(-infinity,R)(||x||) * phi(||x||).
```

The only possible disagreement is at `||x|| = 0`.  If `x != 0`, then

```text
0 < ||x||.
```

Therefore

```text
||x|| in (0,R)  iff  ||x|| < R.
```

So the two indicator functions agree for almost every `x`.

## Transfer To The Quadratic Integrand

Take

```text
phi(r) = (r^2 + a)^(-s).
```

The already-proved punctured theorem gives integrability of

```text
x |-> 1_(0,R)(||x||) * (||x||^2 + a)^(-s)
```

under

```text
R > 0,  a >= 0,  s >= 0,  2s < finrank_R(E).
```

The a.e. equality transfers real-valued integrability to

```text
x |-> 1_(-infinity,R)(||x||) * (||x||^2 + a)^(-s).
```

It also transfers the finite `ENNReal.ofReal` lower-integral statement by
`lintegral_congr_ae`.

## Open-Ball Form

The open ball centered at zero is pointwise the same radial support:

```text
x in Metric.ball 0 R  iff  dist x 0 < R  iff  ||x|| < R.
```

Thus the open-ball theorem is only a pointwise rewrite of the `Iio` radial
support theorem:

```text
x |-> 1_{Metric.ball 0 R}(x) * (||x||^2 + a)^(-s)
```

is integrable under the same hypotheses.

## Why This Is Only Almost-Everywhere

When `a = 0` and `0 < s`, the expression `(||x||^2)^(-s)` is singular at
`x = 0` in the intended analytic reading.  The nonpunctured `Iio` and ball
representatives include the origin and rely on Lean's total point value there.
The theorem transfers by a.e. equality and integrability ignores changes on
null sets; it should therefore not be read as a pointwise regularity statement
at the origin.

## Lean Shape

The intended Lean theorem family is:

```text
ae_eq_norm_indicator_Ioo_Iio
integrable_norm_sq_add_rpow_neg_indicator_Iio
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top
norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio
integrable_norm_sq_add_rpow_neg_indicator_ball
lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top
```

The generic a.e. equality needs only `[NoAtoms mu]`.  The quadratic
integrability corollaries use the existing additive Haar hypotheses from the
punctured radial theorem, which provide the required no-atoms fact.

## Nonclaims

- No closed-ball theorem or boundary-sphere nullity.
- No endpoint theorem at `2s = finrank`.
- No lower or divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density theorem.
- No product-coordinate `+k/2` threshold theorem.
- No Aoyagi p.13 analytic chart or Jacobian theorem.
- No normal-crossing construction, pole order, or RLCT.
