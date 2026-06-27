# Review - A2 Retained-Passive Raw-Order Topological Chart

Date: 2026-06-26.

Reviewer: Peirce the 4th, xhigh read-only explorer.

## Verdict

No findings.

## Checks

Peirce checked the raw-order topological chart slice in
`RetainedPassiveCoordinatesTopology.lean`.

The review confirmed that raw block reassembly and readout continuity are by
finite projections and `fromBlocks`:

```text
continuous_rawEdgeTupleA1
continuous_rawEdgeTupleA3
continuous_edgeFamilyOfRawOrderTuple
continuous_edgeFamilyRawOrderTuple
```

The raw-order target openness is exactly the continuous preimage of
`sourceRecursiveDetChartSet` under `edgeFamilyOfRawOrderTuple`:

```text
isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
```

The forward and inverse subtype-continuity statements compose the intended
maps, and the subtype homeomorphism and ambient open partial homeomorphism use
the already-landed maps-to, inverse, open, and continuity fields:

```text
continuous_topologyTupleEdgeRawOrder_detChart_subtype
continuousAt_topologyTupleEdgeRawOrderInverse_of_mem_rawOrderSourceRecursiveDetChartSet
continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
topologyTupleDetChartSet_rawOrderSourceRecursiveDetChartSet_homeomorph
topologyTupleEdgeRawOrder_openPartialHomeomorph
```

Peirce also checked that the reproduction and statement card match the formal
claim and keep the nonclaims explicit.

## Nonclaims

The review found no inverse differentiability, derivative formula, tangent
equivalence, determinant unit/formula, Jacobian density, measure transport,
normal-crossing, pole-order, RLCT, quiver-paper/result dependency, `sorry`,
`admit`, `axiom`, or `unsafe` introduced by this slice.
