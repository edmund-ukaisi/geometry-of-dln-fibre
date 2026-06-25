# Review - A2 adapted product-difference loss-comparison finite integral

Date: 2026-06-25.

Reviewer: xhigh `Beauvoir the 5th`, read-only.

## Verdict

Accepted at the conditional comparison scope.

The theorem is mathematically sound when the supplied hypotheses are

```text
c * S(x,u) <= adaptedSquareSum(x,u),
c0 * adaptedSquareSum(x,u) <= loss(x,u),
0 < c,
0 < c0.
```

Multiplication of the first inequality by nonnegative `c0` gives

```text
c0 * (c * S(x,u)) <= c0 * adaptedSquareSum(x,u),
```

and transitivity with the supplied loss comparison gives the p.13 local loss
lower bound with constant `c0 * c`.

## Lean Notes

The reviewer recommended using the constant order `c0 * c`, because this is
the expression naturally produced by `mul_le_mul_of_nonneg_left`.  Positivity
is `mul_pos hc0 hc`.  This avoids needing a separate square-sum
nonnegativity proof.

The implemented proof follows this shape:

```text
mul_le_mul_of_nonneg_left (hadapted_lower x u hu) (le_of_lt hc0)
```

then a `calc` chain to the supplied `hloss_cmp`.

## Nonclaims Check

The review required the theorem to state that `hloss_cmp` is the unproved
loss-comparison bridge.  The theorem does not identify the adapted square-sum
with the original DLN/statistical loss, does not construct the p.13 product
chart, does not prove chart coverage, does not transport Jacobian or density
factors, does not prove residual source hypotheses, and does not produce
normal crossings, pole order, or RLCT.

