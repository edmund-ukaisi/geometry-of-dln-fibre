# Statement Card - A2 Case 2 with-following endpoint active readout

## Statement

For the enlarged Case 2 passive-theta endpoint topology tuple

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z,
```

the finite active readout from the endpoint tuple returns the active
selected-entry source chart:

```text
activeReadout (Y z)
  = ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

Consequently,

```text
Measure.map (activeReadout o Y) referenceSource
```

is the same product reference measure already obtained from the active
selected-entry source-coordinate COV.

## Kill Condition

The claim would be false if `Y` did not already store the selected-entry
charted `C 1` block, or if the independent following-factor constructor did
not read back through `C 0` as the supplied matrix `z.2`.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- `ofTopologyTuple_topologyTuple`.
- `endpointTransport_symm_endpointTransport`.
- `case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor`.
- The existing active selected-entry source-coordinate COV.

## Lean Targets

```text
Case2PassiveThetaWithFollowingFactor.endpointRetainedData_C_one_submatrix_eq_displayedPostPivotResidualBlock
Case2PassiveThetaWithFollowingFactor.endpointRetainedData_C_zero_submatrix_eq_followingFactor
Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout
Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_activeReadout_comp_referenceSource_eq_prod
```

## Nonclaims

No endpoint determinant-chart Haar equality, no raw-map pushforward, no
raw-order Jacobian insertion, no formal-product/source-image domination, no
source-image coverage, no normal crossings, no pole order, and no RLCT
extraction.

