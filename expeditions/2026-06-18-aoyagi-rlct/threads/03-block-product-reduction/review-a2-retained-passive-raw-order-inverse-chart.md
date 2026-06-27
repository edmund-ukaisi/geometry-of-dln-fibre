# Review - A2 Retained-Passive Raw-Order Inverse Chart

Date: 2026-06-26.

Reviewer: Meitner the 4th, xhigh read-only explorer.

## Verdict

No findings.

## Checks

Meitner checked the new raw-order target chart and inverse-on-chart layer in
`RetainedPassiveCoordinatesTopology.lean`.

The review confirmed that

```text
topologyTupleRawOrderSourceRecursiveDetChartSet
```

is exactly the preimage of `sourceRecursiveDetChartSet` under
`edgeFamilyOfRawOrderTuple`, so it is the raw-order encoding of the
source-recursive edge-family chart.

The inverse directions were checked:

```text
topologyTupleEdgeRawOrderInverse_topologyTupleEdgeRawOrder
```

uses `sourceReadback_edgeMatrix_eq`, the readback-after-source direction on
the determinant chart.

```text
topologyTupleEdgeRawOrder_topologyTupleEdgeRawOrderInverse
```

uses `edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart`, the
source-after-readback direction on the raw-order target chart.

The image theorem then uses the map-into-target lemma forward and the explicit
inverse witness backward.

The reproduction and statement card were also checked against the Lean proof
shape, including the formulas `Y = {y | S y in Z}`, `H(F z) = z`, `F(H y) =
y`, and the set-image equality.

## Nonclaims

The review found no determinant formula, Jacobian, measure transport,
normal-crossing, pole-order, RLCT, or quiver-paper/result dependency introduced
by this slice.
