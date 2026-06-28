# A2 retained-passive raw-order source-chart product-density pushforward

Status: controller reproduced; Lean target selected.

## Claim

The public raw-order retained-passive source chart gives a direct
source-production pushforward statement for the solved-`A1` product determinant
density.

## Reproduction

Write

```text
rho = Fin (finrank R U0)
kappa' = throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U0
S = topologyTupleDetChartSet
T = topologyTupleRawOrderSourceRecursiveDetChartSet
Jprod(z) = retainedPassiveFormalRawOrderJacobianProductAbsDetAt z
```

The public raw-order source chart is

```text
sourceChart(y)
  = paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0 y
  = paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
      (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

For an additive Haar measure `m`, the already-proved product-density raw-order
change of variables says that for every a.e.-measurable target map `psi` on `T`,

```text
map (fun z => psi (topologyTupleEdgeRawOrder z))
  ((m.restrict S).withDensity (fun z => ofReal (Jprod z)))
=
map psi (m.restrict T).
```

Specialise this to `psi = sourceChart`.  The a.e.-measurability input is the
canonical raw source-chart measurability theorem, since `sourceChart` is
definitionally the canonical chart already used in the local-source measure
handoff.

This gives

```text
map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
  ((m.restrict S).withDensity (fun z => ofReal (Jprod z)))
=
map sourceChart (m.restrict T).
```

It remains to expose the target as the fixed-base source edge-family set.  The
source-image theorem proves

```text
sourceChart '' T
=
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W B U0 hU0.
```

Hence `sourceChart y` lies in the source edge-family set for every `y in T`.
Since `T` is null-measurable, this is true for `(m.restrict T)`-a.e. `y`; by
a.e. map transfer, `map sourceChart (m.restrict T)` is supported on the source
edge-family set.  Therefore

```text
(map sourceChart (m.restrict T)).restrict sourceEdgeFamilySet
=
map sourceChart (m.restrict T).
```

Combining the two identities gives the direct product-density source-chart
pushforward with the target restriction displayed.

## Boundary

This is a reduced fixed-base retained-passive source-production and
product-density pushforward theorem.  It does not construct an original DLN
source prior, prove full source-rank coverage, identify a selected-entry
signed-box density, prove residual positivity or integrability, produce normal
crossings, compute pole order, or extract an RLCT.
