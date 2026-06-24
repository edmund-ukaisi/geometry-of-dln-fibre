# Reproduction - A2 cleaned coordinate square-sum

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 separates the post-product-reduction generator families into
regular block entries

```text
C1 - Er,   F2,   F3
```

and the reduced residual product block

```text
prod_s C^(s).
```

The literal displayed product-difference block has signs and the lower-right
correction `prod_s C^(s) - F3 F2`.  Earlier A2 slices proved only the
entry-ideal cleanup from that literal block to the cleaned four-family

```text
C1 - Er,   F2,   F3,   prod_s C^(s).
```

This slice concerns the square-sum attached to the cleaned coordinate family,
not the literal signed/corrected block.

## Calculation

For a finite scalar coordinate family `f : eta -> R`, define the algebraic
square-sum

```text
sum_{c : eta} f(c)^2.
```

The cleaned product-difference coordinate index is the disjoint sum

```text
AoyagiProductDifferenceCoordinateIndex(iota, mu, nu)
  =
AoyagiRegularBlockCoordinateIndex(iota, mu, nu)
  +
AoyagiResidualBlockCoordinateIndex(mu, nu).
```

Its value function restricts to the regular-coordinate value on the left
summand and to the residual-coordinate value on the right summand.  Therefore
finite summation over the disjoint sum gives

```text
sum_{c : product-difference} value(c)^2
  =
sum_{c : regular} regularValue(c)^2
  +
sum_{c : residual} residualValue(c)^2.
```

Specializing to the fixed-base suffix-state maps gives the same identity for
the cleaned p. 13 source coordinate maps:

```text
squareSum(productDifferenceCoordinateMap x)
  =
squareSum(regularBlockCoordinateMap x)
  +
squareSum(residualBlockCoordinateMap x).
```

## Boundary

This is finite algebraic loss bookkeeping for the cleaned generator family.
It is a useful input for a later regular-suspension proof because it names the
regular and residual square-sum decomposition.

## Nonclaims

- No equality with the literal signed/corrected block Frobenius square-sum.
- No analytic generator transport from the literal block to the cleaned family.
- No analytic coordinate chart or local inverse.
- No source-rank openness or chart coverage.
- No Jacobian/prior compatibility theorem.
- No normal crossings, pole order, or RLCT extraction.
