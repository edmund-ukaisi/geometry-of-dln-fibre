# A2 retained-passive raw-order source-chart composition

## Claim

On the retained-passive determinant chart, composing the raw-order tuple map
with the public raw-order source chart is the same as directly realizing the
original retained-passive tuple as a fixed-base source edge family.

## Reproduction

Fix endpoint bases `W`, base edge maps `B`, the endpoint complement `U0`, and
write

```text
rho = Fin (finrank K U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0.
```

For a retained-passive product tuple `z`, the direct fixed-base source family is

```text
Psi(z) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple z).
```

The public raw-order source chart is

```text
Phi(y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

Assume `z` is in the retained-passive determinant chart.  The tuple topology
API proves that raw-order readback is a left inverse on this chart:

```text
topologyTupleEdgeRawOrderInverse (topologyTupleEdgeRawOrder z) = z.
```

Substituting this equality into the definition of `Phi` gives

```text
Phi(topologyTupleEdgeRawOrder z)
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
      (ofTopologyTuple z)
  = Psi(z).
```

No edge-matrix reconstruction, image theorem, or measure statement is needed
for this pointwise identity.  It only exposes a direct presentation of the
same reduced retained-passive source family already used internally in the
raw-order source-chart image proof.

## Boundary

This is determinant-chart source-map bookkeeping.  It does not prove original
DLN source-rank coverage, retained-passive-to-selected-entry factor alignment,
pivot provenance, selected-entry chart coverage, measure or prior transport,
normal crossings, pole order, or RLCT extraction.
