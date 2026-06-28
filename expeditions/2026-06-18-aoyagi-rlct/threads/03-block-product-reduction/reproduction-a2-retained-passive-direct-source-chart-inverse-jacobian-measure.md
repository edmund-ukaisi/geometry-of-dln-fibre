# Reproduction - A2 retained-passive direct source chart inverse-Jacobian measure

## Shape

Let

```text
rho := Fin (Module.finrank R U0)
kappa' := throughSubspaceEndpointComplementIndex
  (reverseVertex W) (reverseEdge W B) U0
S := topologyTupleDetChartSet rho kappa'
T := topologyTupleRawOrderSourceRecursiveDetChartSet rho kappa'
Phi := topologyTupleEdgeRawOrder : TopologyTuple rho kappa' R -> TopologyTuple rho kappa' R
```

The direct determinant-chart p.13 source chart is

```text
directChart z :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0
    (ofTopologyTuple z).
```

The public raw-order source chart is

```text
rawChart y :=
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0 y.
```

The target theorem should identify the direct determinant-chart source measure
with the raw-order source-chart measure carrying the inverse-Jacobian density:

```text
map directChart (m.restrict S)
  =
map rawChart
  ((m.restrict T).withDensity
    (fun y => ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y))).
```

Here `m` is a Haar measure on the retained-passive topology-tuple space.

## Calculation

The already proved inverse-Jacobian change-of-variables theorem says that for
any a.e.-measurable downstream map `psi`,

```text
map (fun z => psi (Phi z)) (m.restrict S)
  =
map psi
  ((m.restrict T).withDensity
    (fun y => ofReal (topologyTupleEdgeRawOrderInverseJacobianDensity y))).
```

Apply this with `psi := rawChart`.  The required a.e.-measurability is the
existing retained-passive raw-order source-chart measurability theorem:

```text
retainedPassiveP13CanonicalSourceChart_aemeasurable.
```

The left-hand map is then

```text
map (fun z => rawChart (Phi z)) (m.restrict S).
```

For every `z in S`, the pointwise source-chart identity gives

```text
rawChart (Phi z) = directChart z.
```

This is exactly

```text
paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_eq_sourceEdgeFamilyOfData.
```

Since `S` is null-measurable for `m`,

```text
ae_restrict_mem₀ : for a.e. z in m.restrict S, z in S,
```

so the pointwise identity holds a.e. on `m.restrict S`.  `Measure.map_congr`
therefore replaces `map (rawChart o Phi) (m.restrict S)` by
`map directChart (m.restrict S)`.

## Boundary

This proves a retained-passive chart-layer source-measure comparison between
determinant-chart coordinates and raw-order coordinates with the inverse
Jacobian density.  It is a finite chart change-of-variables consequence.

It does not identify the original external DLN source prior, compare that
external prior with this chart measure, prove source-rank coverage, prove
selected-entry residual positivity, prove normal crossings, compute pole
order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The direct fixed-base retained-passive p.13
source-edge-family pushforward of determinant-chart Haar measure equals the
raw-order p.13 source-chart pushforward of the inverse-Jacobian weighted
raw-order determinant-chart measure.

**Assumed.** Finite-dimensional fixed-base context, measurable/Borel
structures on the topology-tuple and edge-family spaces, and Haar measure on
the topology-tuple coordinate space.

**Deferred.** Original external prior transport, source-rank coverage,
selected-entry positivity/integrability, normal crossings, pole order, and
RLCT extraction.
