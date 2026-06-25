# Statement Card - A2 adapted product-difference triangular multiplier comparison

## Statement

For finite matrices over an ordered ring, coordinate square-sums are bounded
under left and right multiplication:

```text
squareSum(L M R) <= squareSum(L) * squareSum(R) * squareSum(M).
```

Consequently, if the p. 13 triangular identity

```text
[[I,0],[F3,I]] * T * [[I,F2],[0,I]] = [[Ctop,0],[0,D]]
```

holds, and the product of the two triangular multiplier square-sums is at most
`K`, then every `c >= 0` with `c*K <= 1` satisfies

```text
c * squareSum([Ctop-I, -F2; -F3, D-F3F2])
  <= squareSum(T - [I,0;0,0]).
```

## Lean Names

```text
matrixCoordinateSquareSum_mul_le_mul
matrixCoordinateSquareSum_mul_mul_le_mul
const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_fromBlocks_neg_neg_sub_mul
AoyagiProductDifferenceCoordinateIndex.const_mul_literalCoordinateSquareSum_le_productDifferenceSquareSum_of_triangularBlockProduct
```

## Source

Aoyagi p. 13 product-difference display, plus the elementary finite
Frobenius/Cauchy-Schwarz estimate for matrix multiplication.

## Dependencies

- finite row/column index types;
- ordered-ring square-sum arithmetic;
- the p. 13 triangular block identity;
- a supplied finite multiplier bound `squareSum(L) * squareSum(R) <= K`.

## Nonclaims

No original DLN loss comparison, covariance lower bound, basis norm
equivalence, multiplier boundedness theorem, analytic chart construction,
Jacobian/prior transport, regular-suspension theorem, normal crossings, pole
order, or RLCT extraction is proved.
