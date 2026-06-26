# Statement card - A2 retained-passive Case 2 synthetic data

## Claim

There is a synthetic two-edge retained-passive coordinate datum whose active
`C` factors are exactly Aoyagi's displayed post-pivot Case 2 residual block and
following factor.  This datum lies in the finite retained-passive determinant
chart, and its residual-factor product satisfies the successor selected-entry
matrix identity under the same explicit entrywise successor-source readout as
the concrete Case 2 two-edge bridge.

## Lean artifacts

File:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`

Definitions/theorems:

```lean
case2PostPivotRetainedPassiveData

case2PostPivotRetainedPassiveData_detChart

case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise

case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise
```

## Proved inputs

- `case2PostPivotFreeTwoEdgeFactorFamily` supplies the concrete active two-edge
  Case 2 `C` family.
- `case2PostPivotRetainedPassiveData_detChart` proves the determinant-chart
  condition from identity `Ctop` and identity passive `A1`.
- `residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise`
  supplies the concrete two-edge selected-entry readout once the entrywise
  successor-source formula is assumed.

## Supplied inputs

- the entrywise successor-source readout for `D_(J+1) * C'_+`;
- the endpoint equivalence `eNext : tau ~= Case2ResidualColIndex n S (J+1)`.
- the successor-continuation hypothesis
  `hnext : J + 2 <= prefixMinNat n (S + 1)`.

## Nonclaims

No source chart or source edge family is constructed.  No longer
retained-passive suffix is sliced or transported to the two-edge chain.  No
fixed-base edge realization, weighted pushforward, Jacobian/source-density
theorem, original-loss comparison, normal crossings, pole order, or RLCT
extraction is proved.  The theorem is finite matrix bookkeeping for a synthetic
two-edge datum.
