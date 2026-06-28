# Statement card: A2 retained-passive canonical local formal/product-density COV

## Lean target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

## New names

Private helper facts:

```text
retainedPassiveP13CanonicalSourceChart_aemeasurable
retainedPassiveP13CanonicalSourceChart_realize
```

Public wrappers:

```text
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalRawOrderAbsDet
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet
```

## Content

The canonical fixed-base retained-passive p.13 local source now has the same
formal and solved-`A1` product density chart-measure identity as the realized
socket.  The theorem uses the canonical source chart

```text
y |-> paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
       (ofTopologyTuple (topologyTupleEdgeRawOrderInverse y)).
```

The private helper facts prove that this source chart is a.e.-measurable on
the raw-order source-recursive determinant chart and realizes the raw-order
edge family there.

## Proof idea

On `T`, `topologyTupleEdgeRawOrderInverse` lands in the determinant chart and
is continuous.  After applying `ofTopologyTuple`, the existing retained-passive
p.13 source-chart continuity theorem gives a.e.-measurability.  The realization
identity is the same raw-order inverse computation as in the older abstract
canonical theorem:

```text
topologyTupleEdgeRawOrder (topologyTupleEdgeRawOrderInverse y) = y.
```

The public wrappers call the realized formal/product local-source theorem with
`Cedge = id`, the canonical source chart, the a.e.-measurability helper, and
the realization helper.

## Nonclaims

This removes the external realization hypothesis only for the canonical
retained-passive chart-produced local source.  It does not construct an
original source prior, identify signed-box densities, prove normal crossings,
compute pole order, or extract an RLCT.
