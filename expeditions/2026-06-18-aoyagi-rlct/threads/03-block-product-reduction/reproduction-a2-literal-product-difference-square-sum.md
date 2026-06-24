# Reproduction - A2 literal product-difference square-sum

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 displays the literal product-difference block

```text
[ C1 - Er        -F2
  -F3      prod_s C^(s) - F3 F2 ].
```

Earlier A2 slices named the cleaned coordinate family

```text
C1 - Er,   F2,   F3,   prod_s C^(s)
```

and its square-sum.  This slice returns to the literal displayed block and
names the finite square-sum attached to its scalar entries.

## Calculation

For arbitrary block matrices

```text
X  : Matrix iota iota R,
F2 : Matrix iota nu R,
F3 : Matrix mu iota R,
D  : Matrix mu nu R,
```

the scalar entries of the literal p. 13 block are indexed by the same disjoint
sum as the cleaned product-difference coordinate index:

```text
regular index     -> entries of X, -F2, -F3,
residual index    -> entries of D - F3 F2.
```

The square-sum over this disjoint sum is therefore

```text
sum entries(X)^2 + sum entries(-F2)^2 + sum entries(-F3)^2
  + sum entries(D - F3 F2)^2.
```

Because `(-a)^2 = a^2`, this is

```text
sum entries(X)^2 + sum entries(F2)^2 + sum entries(F3)^2
  + sum entries(D - F3 F2)^2.
```

Equivalently,

```text
literalSquareSum(X,F2,F3,D)
  =
regularSquareSum(X,F2,F3)
    + residualSquareSum(D - F3 F2).
```

This is the finite square-sum form of the literal p. 13 loss before any local
comparison with the cleaned loss.

## Boundary

This slice only expands the scalar square-sum of the displayed signed/corrected
block.  It is the literal-loss counterpart to the cleaned square-sum split.

## Nonclaims

- No comparison between `D - F3 F2` and `D`.
- No proof that the literal square-sum is locally comparable to the cleaned
  square-sum.
- No analytic generator transport.
- No regular-coordinate chart construction.
- No Jacobian/prior compatibility theorem.
- No normal crossings, pole order, or RLCT extraction.
