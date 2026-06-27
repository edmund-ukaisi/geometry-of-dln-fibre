# Reproduction - A2 Retained-Passive Canonical Local-Source COV

Date: 2026-06-27.

Status: pen-and-paper reproduction for the canonical fixed-base
retained-passive source-edge-family specialization of the raw-order
local-source change of variables.

## Setup

Let

```text
S = topologyTupleDetChartSet,
T = topologyTupleRawOrderSourceRecursiveDetChartSet,
Phi = topologyTupleEdgeRawOrder,
g = topologyTupleEdgeRawOrderInverse,
J(z) = topologyTupleEdgeRawOrderFDerivAbsDet z.
```

The previous local-source COV theorem starts from an arbitrary target-side
realization map

```text
sourceChart : TopologyTuple -> alpha
```

and a continuous edge-family readout `Cedge : alpha -> EFam`.  It requires:

```text
sourceChart is a.e.-measurable on m.restrict T,
fixedBaseEdgeMatrix(Cedge(sourceChart y)) = edgeFamilyOfRawOrderTuple y
for all y in T.
```

For the canonical specialization, take

```text
EFam = forall p, reverseVertex p.castSucc ->L[Real] reverseVertex p.succ,
Cedge(E) = E,
sourceChart(y) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    (ofTopologyTuple (g y)).
```

This is still a raw-coordinate chart-produced source edge-family measure, not
the original DLN source prior.

## Canonical Realization

Take `y in T` and put

```text
data_y = ofTopologyTuple (g y).
```

The raw-order inverse theorem gives `g y in S`, so `data_y` is in the
determinant chart.  The fixed-base retained-passive realization theorem gives

```text
fixedBaseEdgeMatrix(sourceChart y) = data_y.edgeMatrix.
```

By definition of `topologyTupleEdgeMatrix`,

```text
data_y.edgeMatrix = topologyTupleEdgeMatrix (g y).
```

The raw-order readback theorem gives `Phi (g y) = y` on `T`.  The raw-order
decoder theorem gives

```text
edgeFamilyOfRawOrderTuple (Phi (g y)) = topologyTupleEdgeMatrix (g y).
```

Therefore

```text
fixedBaseEdgeMatrix(sourceChart y) = edgeFamilyOfRawOrderTuple y.
```

This is exactly the realization hypothesis required by the previous theorem,
now with no external realization map.

## A.E.-Measurability

The target chart `T` is open, hence null-measurable for the Borel Haar measure.
On the subtype `T`, the inverse chart

```text
y |-> g y
```

is continuous and lands in `S`.  Composing with `ofTopologyTuple` gives a
continuous map from `T` to retained-passive coordinate data; because `g y in S`,
this map lands in the determinant-chart subtype.  The named fixed-base
retained-passive source chart is continuous on that determinant-chart subtype.

Thus the canonical `sourceChart` is continuous on `T`.  Since the edge-family
target is assumed to carry its Borel measurable structure, `ContinuousOn` gives
`AEMeasurable sourceChart (m.restrict T)`.

## COV Specialization

The identity edge readout `Cedge(E)=E` is continuous.  The realization and
a.e.-measurability checks above discharge the remaining hypotheses of the
previous local-source COV theorem.  Hence, for

```text
mu = Measure.map sourceChart (m.restrict T),
localSource = retained-passive local source for Cedge = id,
```

Lean proves

```text
mu.restrict localSource =
  Measure.map (sourceChart o Phi)
    ((m.restrict S).withDensity (fun z => ofReal (J z))).
```

## Lean Scope

The Lean checkpoint adds:

```text
measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet
```

in `RetainedPassiveLocalMeasure.lean`.

## Nonclaims

This proves a canonical chart-produced retained-passive local-source COV
identity.  It does not identify the original DLN source prior, prove a
selected-entry image equality, prove source-rank coverage, compute an explicit
determinant formula, produce normal crossings, compute a pole order, or
extract an RLCT.
