# Statement Card - A2 Case 2 post-pivot compatible residual-factor identity

## Decision

Killed as a source-backed theorem. Aoyagi's Case 2 calculation supplies the
post-pivot two-edge product `D_(J+1) * C'_+`, but it does not identify that
product with the successor selected-entry `CenterCoord.chartMap` matrix.

## Boundary

The next selected-entry chart is on the next residual block `D_(J+1)`, not on
the product `D_(J+1) * C'_+`. Any theorem using the product as a selected-entry
coordinate matrix must keep the entrywise successor readout, endpoint
equivalence, and source data explicit.

## Lean Consequence

No new Lean theorem is promoted from this audit. The existing conditional
theorems remain the correct interface:

```text
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor
```

## Nonclaims

No construction of successor selected-entry coordinates, no source/image
equality, no source-measure transport, no normal crossings, no pole order, and
no RLCT theorem.

