# Statement Card - A2 Retained-Passive Raw-Order Inverse Chart

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
topologyTupleRawOrderSourceRecursiveDetChartSet
topologyTupleEdgeRawOrderInverse
mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
image_topologyTupleEdgeRawOrder_detChartSet
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-inverse-chart.md
```

## Review

```text
review-a2-retained-passive-raw-order-inverse-chart.md
```

## Claim

The retained-passive raw-order target map sends the tuple determinant chart
onto the raw-order encoding of the source-recursive determinant edge chart,
and the explicit inverse is obtained by rebuilding the edge family and applying
the existing source readback.

## Role

This supplies the target-domain bookkeeping needed before a formal tangent
equivalence or determinant-unit theorem.  It prevents the later Jacobian layer
from confusing the source determinant chart with a raw tuple chart that happens
to have the same ambient product type.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

## Nonclaims

No derivative formula, tangent equivalence, determinant unit theorem,
determinant formula, density, measure transport, source-rank coverage, normal
crossing, pole order, or RLCT statement is part of this slice.
