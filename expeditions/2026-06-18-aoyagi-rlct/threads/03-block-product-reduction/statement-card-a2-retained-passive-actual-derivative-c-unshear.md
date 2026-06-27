# Statement Card - A2 Retained-Passive Actual Derivative C Unshear

Status: reproduced and Lean-proved; review pending.

## Claim

For a retained-passive tuple `z` in the determinant chart, tangent vector `v`,
and edge `p : Fin (M+1)`, the actual Frechet derivative of the raw-order map
has the expected lower-right block after the target shear by the lower-left
block:

```text
((D raw z) v).C p
  + rawEdgeTupleA3 ((D raw z) v) p * coord.F2 p.castSucc
= v.C p - coord.solvedA3 p * v.F2 p.
```

Here `raw = topologyTupleEdgeRawOrder`, `coord = (ofTopologyTuple z).toCoordinateData`,
and `D raw z` is the ambient Frechet derivative `fderiv R raw z`.

## Lean Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

New theorem names:

```text
rawEdgeTupleA3_topologyTupleEdgeRawOrder
fderiv_topologyTupleEdgeRawOrder_C_component_unshear_apply
fderiv_topologyTupleEdgeRawOrder_C_unshear_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-actual-derivative-formal-shear-bridge.md
```

Review:

```text
review-a2-retained-passive-actual-derivative-c-unshear.md
```

## Dependencies

- raw block formula `topologyTupleEdgeRawOrder_C`;
- raw lower-left readout formula `rawEdgeTupleA3_topologyTupleEdgeRawOrder`;
- differentiability of `solvedA3` on `topologyTupleDetChartSet`;
- projection derivatives for the stored `C` and `F2` coordinates;
- the bilinear product rule for finite matrix multiplication.

## Nonclaims

This does not prove the full equality between
`topologyTupleEdgeRawOrderFDerivAbsDet` and
`retainedPassiveFormalRawOrderJacobianAbsDetAt`.  It does not prove a signed
or absolute determinant formula for the full actual derivative, a measure
pushforward, source-prior transport, source-rank coverage, normal crossings,
pole order, or RLCT.
