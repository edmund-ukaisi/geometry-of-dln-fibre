# Reproduction - A2 one-sided regular-suspension integrability

Date: 2026-06-24.

Status: pen-and-paper reproduction for a narrow analytic Lean brick.

## Scope

This is a one-sided product-measure estimate toward the regular-variable
integrability theorem.  It is independent of Aoyagi Lemma 1, Theorem 4,
normal-crossing extraction, and the quiver-based paper.

The statement does not prove the threshold shift by `k/2`.  It proves only
that, over a finite extra factor, adding a nonnegative term to an ENNReal loss
cannot destroy finiteness of a nonnegative singular integral.

## Calculation

Let `a : X -> [0,infinity]` and `q : Y -> [0,infinity]`.  For `s >= 0` and
any `(x,y)` we have

```text
a x <= a x + q y.
```

The function `u |-> u^s` on `ENNReal` is monotone for `s >= 0`, hence

```text
(a x)^s <= (a x + q y)^s.
```

Taking inverses reverses the inequality:

```text
(a x + q y)^(-s)
  = ((a x + q y)^s)^(-1)
 <= ((a x)^s)^(-1)
  = (a x)^(-s).
```

Therefore Tonelli monotonicity gives

```text
∫_{X x Y} (a x + q y)^(-s) d(mu x nu)
  <= ∫_{X x Y} (a x)^(-s) d(mu x nu).
```

If `nu` is finite and `a^(-s)` is integrable over `X`, then the right side is
the product

```text
(∫_X (a x)^(-s) dmu) * nu(Y),
```

which is finite.  Hence the left side is finite.

For restricted neighborhoods `u subset X`, `t subset Y`, the same argument
applies to the measures `mu.restrict u` and `nu.restrict t`.  The only new
input is `nu t < infinity`, which makes `nu.restrict t` finite.

## Lean Shape

The Lean formalisation uses `ENNReal` powers directly:

```text
(a x + q y) ^ (-s)
```

rather than `Real.rpow`, because real powers at zero would hide the intended
singularity.  The resulting lemmas are product-measure estimates for arbitrary
measurable spaces, not Euclidean balls.

## What This Does Not Prove

- No polar-coordinate estimate for `(||u||^2 + b)^(-s)`.
- No equivalence with the residual integral at exponent `s - k/2`.
- No local integrability-threshold definition.
- No p. 13 product chart, density bound, or Jacobian theorem.
- No pole-order statement.
- No RLCT extraction.

The result is nevertheless useful because it isolates the Tonelli/comparison
part of the later regular-square theorem and keeps the hard radial estimate
separate.
