# Statement Card - A2 regular-suspension finite loss comparison

Date: 2026-06-24.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
aoyagiCoordinateSquareSum_nonneg
aoyagiCoordinateSquareSum_continuousAt
aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero
aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero
aoyagi_sq_sub_le_two_mul_sq_add_two_mul_sq
aoyagi_sq_add_le_two_mul_sq_add_two_mul_sq
aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul
aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul
AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3
AoyagiRegularBlockCoordinateIndex.f2SquareSum_le_regularSquareSum
AoyagiRegularBlockCoordinateIndex.f3SquareSum_le_regularSquareSum
AoyagiProductDifferenceCoordinateIndex.correctedResidualSquareSum_le_two_mul_residual_add_two_mul_product
AoyagiProductDifferenceCoordinateIndex.residualSquareSum_le_two_mul_correctedResidual_add_two_mul_product
AoyagiProductDifferenceCoordinateIndex.productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum
AoyagiProductDifferenceCoordinateIndex.four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_three_mul_coordinateSquareSum_of_product_le_regular
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_three_mul_literalCoordinateSquareSum_of_product_le_regular
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one
AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one
```

## Statement Shape

For finite matrices over an ordered commutative ring, Lean proves the
finite square-sum comparison between the literal p. 13 scalar family

```text
X, -F2, -F3, D - F3 * F2
```

and the cleaned scalar family

```text
X, F2, F3, D.
```

The small-neighborhood finite theorem assumes

```text
squareSum(F2) + squareSum(F3) <= 1
```

and proves both inequalities

```text
literalSquareSum <= 2 * cleanedSquareSum,
cleanedSquareSum <= 2 * literalSquareSum.
```

Lean also keeps a weaker abstract socket: if the product correction
`squareSum(F3*F2)` is already controlled by the regular square-sum, then the
two square-sums are mutually bounded with factor `3`.

## Scope

Finite ordered-ring square-sum algebra only.  The row-column Cauchy-Schwarz
estimate is formalised as a finite-sum inequality for matrix multiplication.
The three real-topology lemmas listed above are a separate ambient
continuity-to-smallness slice; they do not depend on the p. 13 matrix
structure.

## Nonclaims

No analytic chart, local inverse, p. 13 source-stratum smallness wrapper,
regular-coordinate theorem, Fubini/polar shift theorem, normal-crossing
certificate construction, pole-order theorem, or RLCT extraction is proved.
