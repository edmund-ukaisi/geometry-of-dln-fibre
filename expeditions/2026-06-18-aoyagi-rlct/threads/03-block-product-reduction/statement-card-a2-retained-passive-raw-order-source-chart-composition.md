# Statement card: A2 retained-passive raw-order source-chart composition

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean
```

## New name

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData
```

## Content

For a retained-passive tuple `z` in `topologyTupleDetChartSet`, the public
raw-order source chart applied to `topologyTupleEdgeRawOrder z` is exactly the
direct fixed-base source family obtained from `ofTopologyTuple z`:

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0
  (topologyTupleEdgeRawOrder z)
=
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
  (ofTopologyTuple z).
```

## Proof idea

Unfold the raw-order source chart.  Its body reads back by
`topologyTupleEdgeRawOrderInverse` and then realizes the resulting
retained-passive data as a source edge family.  On `topologyTupleDetChartSet`,
the existing inverse theorem gives

```text
topologyTupleEdgeRawOrderInverse (topologyTupleEdgeRawOrder z) = z,
```

so the two source-family definitions agree pointwise.

## Nonclaims

This is reduced retained-passive determinant-chart bookkeeping.  It does not
prove original DLN source-rank coverage, factor alignment for an actual
`sourceReadback` point, selected-entry pivot nonzero provenance, selected-entry
chart coverage, measure or prior transport, normal crossings, pole order, or
RLCT extraction.
