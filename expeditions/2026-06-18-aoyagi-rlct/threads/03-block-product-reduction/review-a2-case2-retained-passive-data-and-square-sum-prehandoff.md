# Review - A2 Case 2 retained-passive data and square-sum prehandoffs

Date: 2026-06-28.

Reviewer: xhigh `Kepler`.

Verdict: PASS.  No blocking findings.

## Findings

The two Lean endpoints are finite-algebra readouts and are scoped correctly:

```text
case2PostPivotSelectedEntryRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
aoyagiCoordinateSquareSum_case2PostPivotSelectedEntrySourceReadback_residualFactorProduct_eq_successorSelectedEntryCenter_residual
```

The datum-level theorem exposes the stored `C` product of the explicit
retained-passive datum.  The square-sum theorem reads the explicit
source-readback product through the selected-entry center-coordinate square-sum.
Neither theorem claims fixed-base endpoint transport, source-chart realization,
local-source membership, measure/Jacobian transport, coverage, normal crossings,
pole order, or RLCT.

The reproduction, statement cards, and ledgers accurately keep the fixed-base
endpoint transport blocker explicit: the constructed Case 2 datum is indexed by
`case2PostPivotTwoEdgeDomain`, while the fixed-base p.13 sockets are indexed by
`throughSubspaceEndpointComplementIndex`.

## Controller Verification

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge` passed.
`git diff --check`, `scripts/sorries`, and touched-Lean-file forbidden-marker
search were clean.  Direct axiom-footprint probes for both new endpoints
reported `[propext, Classical.choice, Quot.sound]`.
