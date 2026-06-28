# Statement card: A2 retained-passive raw-order source-chart image

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## New names

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
image_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_eq_sourceEdgeFamilySet
```

## Content

The first name exposes the canonical raw-order retained-passive source map

```text
y |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
       (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

The readout theorem proves that, on the raw-order source-recursive determinant
chart, its fixed-base edge matrices are exactly `edgeFamilyOfRawOrderTuple y`.
The image theorem proves that its image of the raw-order source-recursive
determinant chart is precisely
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0`.
The existing private canonical source-chart realisation helper in
`RetainedPassiveLocalJacobianMeasure.lean` now delegates to the public readout
theorem.

## Proof idea

Forward direction: raw-order inverse lands in the determinant chart, fixed-base
retained-passive edge-matrix readout reduces the source chart to the inverse
datum's edge matrix, and
`topologyTupleEdgeRawOrder (topologyTupleEdgeRawOrderInverse y) = y` identifies
that edge matrix with the raw-order source tuple.

Reverse direction: for an edge family in the fixed-base source set, read back
its fixed-base edge matrices.  The source-readback datum is in the determinant
chart and reconstructs the original continuous edge family, so the raw-order
source chart maps its topology tuple back to that edge family.

## Nonclaims

This is reduced retained-passive source-image bookkeeping.  It does not prove
source-rank coverage in the original DLN parameters, measure or prior
transport, a Jacobian formula, residual a.e. positivity, finite negative-power
integrability, normal crossings, pole order, or RLCT extraction.
