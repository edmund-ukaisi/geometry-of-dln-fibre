# Reproduction - A2 Retained-Passive Solved A3 Derivative

Date: 2026-06-26.

Status: pen-and-paper reproduction for the lower-left derivative foothold.
The Lean checkpoint proves differentiability only; it does not identify a
linear tangent map or determinant.

## Coordinate Setup

The retained-passive lower-left seed has

```text
A3seed_q = ell_q     for q < M
A3seed_M = 0.
```

The solved full lower-left family keeps the passive entries and solves the
last entry from the active endpoint equation:

```text
solvedA3_q = A3seed_q                  for q < M
solvedA3_M = -(F3 - EarlyTail) * CtopLast.
```

Here

```text
EarlyTail =
  retainedPassiveLowerLeftProductTailSum solvedA1
    (retainedPassiveA3WithoutLast A3seed) C 0

CtopLast =
  residualFactorProduct solvedA1 (Fin.last (M+1)) (Fin.last M).castSucc.
```

The tail sum unfolds by decreasing induction:

```text
Tail_p =
  -(CProduct_{p+1..last} * A3early_p * A1Product_{p..last}^{-1})
  + Tail_{p+1}.
```

## Differentiability Reproduction

The zeroed-final lower-left family is differentiable componentwise: the final
slot is constant zero, and the other slots are tuple projections.

The stored residual `C` product is differentiable by the same recursion as its
continuity proof.  The product is rectangular, so the Lean proof uses the
bounded-bilinear matrix multiplication helper built from
`matrixMulContinuousLinearMap`, not ring `.mul`.

The solved-`A1` residual product is differentiable on the tuple determinant
chart by descending induction, using the already-proved solved-`A1`
differentiability for each factor.

For the lower-left tail sum, the induction step uses:

```text
CProduct(z)
A3early_p(z)
(A1Product(z))^{-1}
Tail_{p+1}(z).
```

The inverse is differentiable at the base point because the determinant-chart
hypothesis gives determinant units for the solved-`A1` factors, and hence for
the residual product.  The two products are heterogeneous matrix products, so
they use the same bounded-bilinear multiplication helper.

The final solved-`A3` entry is then a product of

```text
-(F3 - EarlyTail)
```

and `CtopLast`, both differentiable.  Non-final entries are projections of
`A3seed`.

## Lean Scope

The Lean checkpoint adds:

```text
differentiableAt_matrix_mul
differentiableAt_retainedPassiveA3WithoutLast
differentiableAt_residualFactorProduct_C
differentiableAt_residualFactorProduct_solvedA1_of_mem_topologyTupleDetChartSet
differentiableAt_retainedPassiveLowerLeftProductTailSum_of_mem_topologyTupleDetChartSet
differentiableAt_solvedA3_of_mem_topologyTupleDetChartSet
```

The next theorem should assemble differentiability of
`topologyTupleEdgeRawOrder` from the solved-`A1`, solved-`A3`, `F2full`, `C`,
and raw-order component formulas.

## Nonclaims

No full raw-order derivative, tangent equivalence, determinant formula,
Jacobian density, measure pushforward, image equality, source-rank coverage,
normal crossings, pole order, or RLCT statement is proved here.

