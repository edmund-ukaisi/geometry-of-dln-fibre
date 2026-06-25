# Reproduction - A2 fixed-base triangular multiplier local boundedness

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for removing the
separately supplied local triangular multiplier bound in the fixed-base
self-base case.

## Source Anchor

Aoyagi p. 13 uses the deterministic triangular endpoint multipliers

```text
L(x) = [[I, 0], [lowerLeftBlock S(x).L, I]],
R(x) = [[I, -S(x).B], [0, I]],
```

where `S(x)` is the fixed-base suffix state produced by the product-reduction
recursion.  The previous source-filter bound kept

```text
squareSum(L(x)) * squareSum(R(x)) <= Kmul
```

as an eventual input.  In the self-base fixed chart, continuity of `Cedge` at
the paper chain gives continuity of the suffix-state fields and hence local
boundedness of this finite product.

## Derivation

Let

```text
SL(x) = squareSum(L(x)),
SR(x) = squareSum(R(x)),
M(x)  = SL(x) * SR(x).
```

The coordinate functions of `lowerLeftBlock S(x).L` and `-S(x).B` are
continuous at `x0`, using the fixed-base suffix-state field-continuity theorem
and the automatic self-base determinant-chart hypotheses.  The block matrices
`L(x)` and `R(x)` are therefore continuous coordinatewise.  Finite sums and
products preserve continuity, so `M` is continuous at `x0`.

A continuous real-valued function is locally bounded above: on a neighborhood
of `x0`,

```text
M(x) <= max (M(x0) + 1) 1.
```

This gives a positive bound `Kmul > 0`.  Weakening the ambient neighborhood to
the source-rank filter gives the same bound on

```text
nhdsWithin x0 (paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge).
```

With `c = Kmul^{-1}`, we have `c > 0`, `0 <= c`, and `c*Kmul <= 1`.  The
already-landed source-filter adapted product-difference theorem then gives

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

eventually on the source-rank filter.

## Lean Shape

Lean proves the generic local-boundedness helpers and the fixed-base p. 13
consequences in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```

with names

```text
continuousAt_eventually_le_self_add_one
continuousAt_exists_pos_eventually_le
aoyagiCoordinateSquareSum_exists_pos_eventually_le_of_continuousAt
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le
paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source
```

## Boundary

This proves only local boundedness of the deterministic finite triangular
multiplier square-sum product and uses it in the adapted fixed-base
product-difference square-sum comparison.  The right-hand side is not the
original DLN/statistical loss.  The theorem does not prove source-rank
openness, covariance lower bounds, basis norm equivalence, analytic chart
construction, Jacobian/prior transport, regular-suspension Fubini or polar
shift, normal crossings, pole order, or RLCT extraction.
