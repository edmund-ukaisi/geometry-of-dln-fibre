# Review: A2 retained-passive topology-tuple punctured-sector transport

## Source-Scope Verdict

PASS.  Xhigh source-scope scout `Laplace the 4th` found that this checkpoint
is source-safe if stated as repo-local topology/chart packaging around already
reproduced Aoyagi p.13 and Case 2 formulas.

The source content is not the topology tuple infrastructure itself.  Aoyagi
pp. 10-13 support the retained-passive p.13 block/product coordinates, and the
existing Case 2 selected-entry notes support the residual chart calculation.
The topology tuple, raw-order chart, and sector packaging are Lean-side
infrastructure.

## Lean/API Route Verdict

PASS.  Xhigh Lean/API scout `Locke the 4th` found that the route is supported
by existing API:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
case2PostPivotSelectedEntryRetainedPassiveDataWithPassive_endpointTransport_detChart
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
topologyTuple_mem_topologyTupleDetChartSet
mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
```

The expected proof route is to get determinant-chart membership for
`retainedData z`, convert it to topology-tuple determinant membership, push it
through the raw-order maps-to theorem, apply the raw-order source-chart
identity, and reuse the existing punctured-sector inverse readout.

## Nonclaims

No source-image equality, source-rank coverage, determinant-chart Haar
transport, raw/source Haar theorem, external/original source-prior comparison,
measure pushforward theorem, Jacobian formula, normal crossings, pole order,
or RLCT extraction.

## Implementation Review

PASS.  Xhigh implementation review by `Singer the 4th` found no blocking
issue.

Checks:

- The theorem is a narrow pointwise bridge: it returns an open `V`, proves
  topology-tuple determinant-chart membership, proves raw-order
  source-recursive determinant-chart membership, identifies the raw-order p.13
  source chart with the direct `sourceChart`, and keeps inverse readout
  equality on the returned punctured sector.
- The sector is explicitly the determinant-domain neighborhood intersected
  with `{z | z.2 pivotNext != 0}`.
- The inverse readout equality uses the pivot condition through the existing
  punctured-sector readout theorem.
- Determinant-chart membership is reconstructed from local-source membership
  plus `sourceReadback_detChart_of_sourceRecursiveDetChart`; raw-order
  membership follows from
  `mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet`.
- No hidden measure, Haar, source-prior, source-image, source-rank,
  normal-crossing, pole-order, RLCT, or quiver-facing claim was found.

Focused build passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
```

Only pre-existing dependency linter warnings in
`ProductReductionStepRegularDensity.lean` appeared.
