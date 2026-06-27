# Statement Card - A2 Retained-Passive Raw-Order Topological Chart

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
continuous_rawEdgeTupleA1
continuous_rawEdgeTupleA3
continuous_edgeFamilyOfRawOrderTuple
continuous_edgeFamilyRawOrderTuple
isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
continuous_topologyTupleEdgeRawOrder_detChart_subtype
continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph
topologyTupleEdgeRawOrder_openPartialHomeomorph
```

## Reproduction

```text
reproduction-a2-retained-passive-raw-order-topological-chart.md
```

## Verification

Review:

```text
review-a2-retained-passive-raw-order-topological-chart.md
```

passed by xhigh read-only explorer `Peirce the 4th`.

Focused and full builds passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

## Claim

The raw-order target chart is open, and the retained-passive raw-order map is
a homeomorphism and ambient open partial homeomorphism from the tuple
determinant chart onto that raw-order target chart, with inverse given by raw
edge-family reassembly followed by source readback.

## Role

This turns the set-level inverse chart into a usable topological chart for the
future derivative/Jacobian layer.  It keeps the target domain explicit before
any determinant-unit argument.

## Nonclaims

No inverse differentiability, derivative formula, tangent equivalence,
determinant unit theorem, determinant formula, density, measure transport,
source-rank coverage, normal crossing, pole order, or RLCT statement is part
of this slice.
