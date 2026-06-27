# A2 retained-passive composed weighted COV

## Scope

This note records the measure-map composition step after the retained-passive
raw-order weighted change of variables.  It is a bridge theorem, not a new
Jacobian theorem.

It is independent of the quiver paper.  It does not prove determinant-density
continuity, inverse-density measurability, source-prior transport, original DLN
source pushforward, normal crossings, pole order, or RLCT.

## Setup

Let

```text
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
f = topologyTupleEdgeRawOrder,
J(z) = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

For an additive Haar measure `m` on the tuple coordinate space, the previous
checkpoint proves

```text
Measure.map f ((m.restrict S).withDensity (ofReal o J)) = m.restrict T.
```

Let `ψ : TopologyTuple -> β` be any downstream measurable target map.  The
intended use is `ψ = edgeFamilyOfRawOrderTuple`, or later the fixed-base
continuous edge-family realization composed with that raw-order readback.  The
bridge should not choose such a realization prematurely.

## Calculation

Write

```text
μ = (m.restrict S).withDensity (ofReal o J).
```

Assume:

```text
ψ is a.e.-measurable with respect to m.restrict T.
```

The raw-order map `f` is continuous on the determinant-chart subtype, hence
a.e.-measurable with respect to `m.restrict S`; by absolute continuity of
`withDensity`, it is also a.e.-measurable with respect to `μ`.

Using the weighted COV identity, the measurability assumption transfers to

```text
ψ is a.e.-measurable with respect to Measure.map f μ.
```

Mathlib's `AEMeasurable.map_map_of_aemeasurable` then gives

```text
Measure.map (fun z => ψ (f z)) μ
  = Measure.map ψ (Measure.map f μ)
  = Measure.map ψ (m.restrict T).
```

This is the complete generic bridge.

## Edge-family specialization

The raw-order topology file proves the definitional readback identity

```text
edgeFamilyOfRawOrderTuple (topologyTupleEdgeRawOrder z)
  = topologyTupleEdgeMatrix z.
```

Therefore, whenever `edgeFamilyOfRawOrderTuple` is a.e.-measurable on
`m.restrict T`, the generic bridge specializes to

```text
Measure.map topologyTupleEdgeMatrix μ
  =
Measure.map edgeFamilyOfRawOrderTuple (m.restrict T).
```

This says only that the weighted retained-passive coordinate chart can be
read as an edge-family pushforward after raw-order COV.  It is not the original
DLN source measure, not a source-prior density theorem, and not a local-source
coverage theorem.

## Inverse-density companion

The previous inverse-density checkpoint proves, with explicit a.e.-measurability
hypotheses on the forward density, inverse density, and composed inverse
density,

```text
Measure.map f (m.restrict S) = (m.restrict T).withDensity G,
```

where

```text
G(y) = ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y).
```

If `ψ` is a.e.-measurable with respect to `m.restrict T`, then it is also
a.e.-measurable with respect to `(m.restrict T).withDensity G` by absolute
continuity.  Therefore the same `map_map` calculation gives

```text
Measure.map (fun z => ψ (f z)) (m.restrict S)
  = Measure.map ψ ((m.restrict T).withDensity G).
```

The edge-family specialization again rewrites the left side through
`edgeFamilyOfRawOrderTuple_topologyTupleEdgeRawOrder`:

```text
Measure.map topologyTupleEdgeMatrix (m.restrict S)
  =
Measure.map edgeFamilyOfRawOrderTuple ((m.restrict T).withDensity G).
```

This companion remains conditional exactly where the inverse-density theorem is
conditional.  It does not prove the required a.e.-measurability hypotheses.
