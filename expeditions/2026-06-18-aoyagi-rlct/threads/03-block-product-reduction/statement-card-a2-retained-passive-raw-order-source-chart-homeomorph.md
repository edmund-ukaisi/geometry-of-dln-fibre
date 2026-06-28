# Statement card: A2 retained-passive raw-order source-chart homeomorphism

## Lean target

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## New names

```text
detChart_topologyTupleDetChartSet_homeomorph
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceEdgeFamily_homeomorph_apply
```

## Content

The first helper records the homeomorphism between determinant-chart
retained-passive data and determinant-chart topology tuples.  The second
composes that helper with the existing raw-order determinant-chart
homeomorphism and fixed-base source edge-family homeomorphism.

The `toFun` of the second homeomorphism is exposed by the apply theorem as the
canonical raw-order source chart

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0.
```

Its inverse is the fixed-base source readback followed by `topologyTuple` and
`topologyTupleEdgeRawOrder`.

## Nonclaims

This is reduced fixed-base retained-passive local inverse and continuity data.
It does not prove original DLN source-rank coverage, source prior or measure
transport, a new Jacobian formula, residual positivity or integrability,
normal crossings, pole order, or RLCT extraction.
