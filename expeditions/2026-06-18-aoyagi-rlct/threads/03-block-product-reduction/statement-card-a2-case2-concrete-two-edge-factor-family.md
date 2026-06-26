# Statement Card - A2 Case 2 concrete two-edge factor family

## Claim

For the displayed Case 2 post-pivot chain

```text
tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1),
```

the concrete two-edge residual-factor product is exactly Aoyagi's displayed
post-pivot lower product `D_(J+1) * C'_+`.  With a supplied successor
source-chart entrywise readout, the same concrete product upgrades to the
successor selected-entry `CenterCoord.chartMap` matrix.

## Lean Names

```text
case2PostPivotTwoEdgeDomain
case2PostPivotFreeTwoEdgeFactorFamily
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

## Boundaries

This is conditional finite plumbing.  It removes the generic endpoint-family,
endpoint-equivalence, and factor-identity sockets for the concrete displayed
two-edge chain.  The successor entrywise readout, source production of
`Cprime`, successor source data, source/image equality, measure transport,
normal crossings, pole order, and RLCT remain supplied or open.
