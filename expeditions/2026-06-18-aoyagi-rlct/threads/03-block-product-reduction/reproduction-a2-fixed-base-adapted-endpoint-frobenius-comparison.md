# Reproduction - A2 fixed-base adapted endpoint Frobenius comparison

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean implementation.

## Source Anchor

Aoyagi p. 13 works with the product-difference matrix after the deterministic
block product reduction.  In the fixed-base Lean model, the endpoint bases are
chosen from the base paper chain `B` and a complement

```text
U0 complement ker(total product of B).
```

The base endpoint product in these adapted bases is the rank block

```text
T0 = [[I, 0], [0, 0]].
```

The variable endpoint product for a reversed-edge family `Cedge` is the
fixed-base total matrix `T(x)`.

## Derivation

Let

```text
E_x p = Cedge x p
T(x) = paperEndpointFixedBaseTotalMatrixOfReverseEdges(B, U0, E_x)
T(base) = paperEndpointFixedBaseTotalMatrixOfReverseEdges(B, U0, reverseEdge B).
```

The adapted endpoint basis was built so that the base chain maps the
transported through-subspace basis isomorphically, has zero lower-left endpoint
block, and kills the source complement.  Thus

```text
T(base) = [[I, 0], [0, 0]] = T0.
```

The existing adapted product-difference square-sum is therefore exactly

```text
sum_{i,j} (T(x) - T(base))_{i,j}^2
  = sum_{i,j} (T(x) - T0)_{i,j}^2.
```

For any finite real matrix `M`,

```text
trace(M^T M)
  = sum_j (M^T M)_{j,j}
  = sum_j sum_i M_{i,j} M_{i,j}
  = sum_i sum_j M_{i,j}^2.
```

Taking `M = T(x) - T0` gives

```text
trace((T(x) - T0)^T (T(x) - T0))
  = adapted product-difference square-sum at x.
```

This is the Frobenius square in the fixed adapted endpoint bases.  It is a
coordinate identity, not a basis-independent analytic comparison.

## Lean Shape

The Lean implementation is in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with the core names

```text
matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum
paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero
paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss
paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
```

The product-reduction consequences are rewrite wrappers:

```text
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceFrobeniusLoss
PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_of_productReductionCertificate_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceFrobeniusLoss_selfBase_nhdsWithin_source
```

## Boundary

This proves only the fixed-basis endpoint Frobenius identity and its direct
composition with already-landed finite p. 13 product-reduction bounds.  It does
not identify this loss with the original `lossDLN`, does not compare original
network-coordinate Frobenius norms under a basis change, does not construct the
paper's analytic product chart, and does not prove source-rank openness,
density/Jacobian transport, regular-suspension additivity, normal crossings,
pole order, or RLCT extraction.
