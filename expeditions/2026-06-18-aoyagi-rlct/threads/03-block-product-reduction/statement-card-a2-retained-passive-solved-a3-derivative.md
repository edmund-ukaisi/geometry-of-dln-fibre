# Statement Card - A2 Retained-Passive Solved A3 Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
differentiableAt_matrix_mul
differentiableAt_retainedPassiveA3WithoutLast
differentiableAt_residualFactorProduct_C
differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a3-derivative.md
```

## Claim

At tuple determinant-chart points over `Real`, the solved full lower-left
family

```text
z |-> (ofTopologyTuple z).toCoordinateData.solvedA3 p
```

is differentiable for every `p : Fin (M+1)`.

The checkpoint also proves the differentiability ingredients needed for that
claim: zeroed-final lower-left seeds, stored `C` residual products, solved
`A1` residual products, and the lower-left product-tail sum.

## Method

The proof mirrors the existing continuity chain:

```text
continuous_retainedPassiveA3WithoutLast
continuous_residualFactorProduct_C
continuous_residualFactorProduct_solvedA1_detChart_subtype
continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype
continuous_solvedA3_detChart_subtype
```

The new analytic input is heterogeneous finite matrix multiplication as a
differentiable bounded-bilinear map.  The inverse in the tail sum uses the
existing determinant-unit matrix inverse derivative and the existing determinant
unit theorem for solved-`A1` residual products.

## Role

This closes the second solved-family derivative component needed before the
full retained-passive raw-order differentiability theorem.

## Nonclaims

No full raw-order derivative, tangent equivalence, determinant formula,
Jacobian density, measure pushforward, image equality, source-rank coverage,
normal crossings, pole order, or RLCT statement is proved here.

