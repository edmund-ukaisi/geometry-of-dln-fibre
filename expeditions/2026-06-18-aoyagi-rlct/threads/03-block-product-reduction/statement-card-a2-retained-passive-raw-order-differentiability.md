# Statement Card - A2 Retained-Passive Raw-Order Differentiability

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Names

```text
differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-differentiability.md
```

## Claim

At every tuple determinant-chart point over `Real`, the retained-passive
target-coordinate endomap

```text
topologyTupleEdgeRawOrder :
  TopologyTuple rho kappa Real -> TopologyTuple rho kappa Real
```

is differentiable.

## Method

The proof packages the six component formulas:

```text
topologyTupleEdgeRawOrder_A1passive
topologyTupleEdgeRawOrder_F2
topologyTupleEdgeRawOrder_A3passive
topologyTupleEdgeRawOrder_C
topologyTupleEdgeRawOrder_Ctop
topologyTupleEdgeRawOrder_F3
```

using the landed solved-family differentiability theorems for `A1` and `A3`,
projection differentiability for `F2full` and `C`, and the rectangular matrix
product helper `differentiableAt_matrix_mul`.

## Role

This closes the differentiability-only stage for the retained-passive
raw-order tuple map.  The next derivative-layer task is to define and prove
the formal tangent map/equivalence and then prove determinant unitness before
any Jacobian density or measure pushforward statement.

## Nonclaims

No formal derivative formula, tangent equivalence, determinant formula,
Jacobian density, measure pushforward, image equality, source-rank coverage,
normal crossings, pole order, or RLCT statement is proved here.

