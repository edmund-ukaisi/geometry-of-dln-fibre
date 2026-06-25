# Reproduction - A2 adapted product-difference triangular multiplier comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the finite
adapted product-difference square-sum comparison.

## Source Anchor

Aoyagi p. 13 uses triangular endpoint changes to put the product-difference
matrix into the displayed block form

```text
[[C1 - Er, -F2],
 [-F3, prod_s C^(s) - F3 F2]].
```

The finite algebra needed here is one direction of norm comparison: if the
triangular changes have bounded coordinate square-sums, then the p. 13 literal
block square-sum is bounded above by a constant times the untransformed
product-difference square-sum in the adapted endpoint coordinates.

## Derivation

Let

```text
L = [[I, 0], [F3, I]],
R = [[I, F2], [0, I]],
T0 = [[I, 0], [0, 0]].
```

Assume that the adapted product-difference matrix `T` satisfies the p. 13
triangular block identity

```text
L T R = [[Ctop, 0], [0, D]].
```

Subtracting the base rank block gives

```text
L (T - T0) R =
[[Ctop - I, -F2],
 [-F3, D - F3 F2]].
```

This is the literal p. 13 product-difference block.  Therefore the literal
coordinate square-sum is the coordinate square-sum of `L (T-T0) R`.

For finite matrices, the entrywise square-sum satisfies the Frobenius-style
estimate

```text
squareSum(A B) <= squareSum(A) * squareSum(B).
```

Applying it twice gives

```text
squareSum(L (T-T0) R)
  <= squareSum(L) * squareSum(R) * squareSum(T-T0).
```

If the multiplier product is bounded by `K` and `c*K <= 1`, then

```text
c * squareSum(literal p.13 block)
  <= squareSum(T - T0).
```

The constant condition is deliberately weak: `K` is supplied by a local
boundedness argument for the endpoint multipliers, and `c` can be chosen small
enough downstream.

## Lean Shape

Lean proves the generic finite square-sum estimates and the p. 13 block
comparison in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with names

```text
matrixCoordinateSquareSum_mul_le_mul
matrixCoordinateSquareSum_mul_mul_le_mul
const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le
AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_fromBlocks_neg_neg_sub_mul
AoyagiProductDifferenceCoordinateIndex.const_mul_literalCoordinateSquareSum_le_productDifferenceSquareSum_of_triangularBlockProduct
```

## Boundary

This is finite adapted-coordinate matrix algebra.  It does not prove:

- comparison with `lossDLN` or the original statistical loss;
- covariance lower bounds for the data distribution;
- basis or chart norm equivalence for the original network coordinates;
- local boundedness of the triangular multipliers from continuity;
- source-rank openness, source coverage, or analytic chart construction;
- Jacobian or prior density transport;
- regular-suspension Fubini/polar shift;
- normal crossings, pole order, or RLCT extraction.
