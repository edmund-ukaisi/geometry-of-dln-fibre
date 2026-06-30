# Statement card - A2 Case 2 passive theta coordinate domain

Date: 2026-06-30.

## Statement

Introduce a concrete full passive-sector coordinate object for the Case 2
post-pivot selected-entry retained-passive chart:

```text
Case2PassiveTheta =
  (A1passive, F2, A3passive, Ctop, F3, yNext).
```

The object feeds into the existing passive retained datum
`case2PostPivotSelectedEntryRetainedPassiveDataWithPassive`, and its topology
tuple lies in the retained-passive determinant chart whenever `Ctop.det` and
all passive `A1passive.det` are units.

## Lean Targets

Future module:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSector.lean
```

Expected public names:

```text
Case2PassiveTheta.PassiveFields
Case2PassiveTheta
Case2PassiveTheta.A1passive
Case2PassiveTheta.F2
Case2PassiveTheta.A3passive
Case2PassiveTheta.Ctop
Case2PassiveTheta.F3
Case2PassiveTheta.yNext
case2PassiveThetaPivotNext
case2PassiveThetaPivotNonzero
case2PassiveThetaDetSector
case2PassiveThetaPuncturedDetSector
case2PassiveThetaRetainedData
case2PassiveThetaEndpointRetainedData
case2PassiveThetaTopologyTuple
case2PassiveThetaEndpointTopologyTuple
case2PassiveThetaRetainedData_detChart
case2PassiveThetaEndpointRetainedData_detChart
case2PassiveThetaTopologyTuple_mem_detChartSet
case2PassiveThetaEndpointTopologyTuple_mem_detChartSet
```

## Nonclaims

No measure theorem is claimed.  In particular this does not remove the live
determinant-chart pushforward hypothesis, prove source-prior transport, prove
exact/dominated passive-sector Haar transport, construct normal crossings,
compute pole order, or extract RLCT.

## Reproduction

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-theta-coordinate-domain.md
```

## Review

```text
threads/03-block-product-reduction/review-a2-case2-passive-theta-coordinate-domain.md
```
