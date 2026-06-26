# Reproduction - A2 Case 2 concrete two-edge factor family

Date: 2026-06-26.

Status: Lean targets implemented.

## Source Boundary

Aoyagi p. 13 uses ordered products of residual factors in the reduced
coordinates.  The Case 2 calculation on pp. 19-22 displays the continuing
post-pivot lower product as a two-factor product:

```text
D_(J+1) * C'_+.
```

The existing Lean bridge
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix`
connects a generic two-edge `residualFactorProduct` to this displayed product,
but it leaves the endpoint family, endpoint equivalences, and the two factor
identities as hypotheses.

This note records the concrete specialization where the two-edge endpoint
family is chosen to be exactly the displayed Case 2 chain

```text
tau -> Case2ResidualColIndex n S (J+1) -> Case2ResidualRowIndex n S (J+1).
```

## Calculation

Define the three endpoint types by

```text
kappa_0 = tau,
kappa_1 = Case2ResidualColIndex n S (J+1),
kappa_2 = Case2ResidualRowIndex n S (J+1).
```

Define the two supplied factors by

```text
C_0 = case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime,
C_1 = case2DisplayedPostPivotResidualBlock n hS hcont residual.
```

The generic two-edge unfold gives

```text
residualFactorProduct C 2 0 = C_1 * C_0.
```

With the above endpoint choices the row, middle, and right endpoint
equivalences are all reflexive, and the reindexed factor identities are
definitionally the two defining equations of `C_1` and `C_0`.  Hence the
generic bridge specializes to

```text
residualFactorProduct C 2 0
  = case2DisplayedPostPivotResidualBlock n hS hcont residual
      * case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime
  = case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime.
```

## Lean Targets

Implemented in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`:

```text
case2PostPivotTwoEdgeDomain
case2PostPivotFreeTwoEdgeFactorFamily
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct
```

Implemented in
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`:

```text
residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

This is a socket reducer.  It removes the generic endpoint family, endpoint
equivalences, and factor-identity hypotheses when the caller is already using
the displayed Case 2 two-edge chain.

## Nonclaims

- No source-produced successor chart family is constructed.
- No endpoint equivalence between Aoyagi's relabelled paper indices and a
  separate successor chart is proved.
- No construction of `Cprime = Q^-1 C` as successor source data is proved.
- No selected-entry center-coordinate readout is proved.
- No source/image equality, measure transport, normal crossings, pole order, or
  RLCT theorem is proved.
