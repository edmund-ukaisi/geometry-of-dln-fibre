# Review: A2 retained-passive raw-order source-chart composition

Reviewer: xhigh `Godel the 3rd`.

Verdict: PASS.

## Checks

- The theorem
  `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData`
  faithfully unfolds the raw-order source chart and uses the existing
  determinant-chart inverse theorem
  `topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder`.
- The determinant-chart hypothesis `hz` is exactly the needed scope.
- The result is thin but not wrapper churn: it names a useful source-family
  presentation identity before edge-matrix extraction, whereas the older
  readout theorem only identifies extracted edge matrices.
- The docstring, reproduction boundary, and statement-card nonclaims remain
  within reduced fixed-base retained-passive source-map bookkeeping.

## Nonclaims checked

The theorem does not prove original DLN source-rank coverage, selected-entry
factor alignment, pivot provenance or all-pivot coverage, measure/prior
transport, normal crossings, pole order, or RLCT.

## Verification

Focused module build passed.  Direct axiom-footprint check reports:

```text
[propext, Classical.choice, Quot.sound]
```
