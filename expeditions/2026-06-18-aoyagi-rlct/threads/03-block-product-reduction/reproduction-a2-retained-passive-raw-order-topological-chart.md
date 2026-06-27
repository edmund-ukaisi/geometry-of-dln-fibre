# Reproduction - A2 Retained-Passive Raw-Order Topological Chart

Date: 2026-06-26.

Status: pen-and-paper reproduction for the raw-order target chart as a
topological chart.  This is finite topology and coordinate bookkeeping only.
It does not prove differentiability of the inverse, identify a derivative, or
state any Jacobian, measure, normal-crossing, pole-order, or RLCT consequence.

## Setup

Use the notation from the inverse-chart reproduction:

```text
X = topologyTupleDetChartSet
Z = sourceRecursiveDetChartSet
R E = edgeFamilyRawOrderTuple E
S y = edgeFamilyOfRawOrderTuple y
F z = topologyTupleEdgeRawOrder z = R (topologyTupleEdgeMatrix z)
H y = topologyTupleEdgeRawOrderInverse y = topologyTuple (sourceReadback (S y)).
```

The previous slice proved the set-level target chart

```text
Y = { y : TopologyTuple | S y in Z }
```

and the inverse identities `H(F z)=z` for `z in X` and `F(H y)=y` for
`y in Y`.

## Continuity of the Raw Block Maps

The map `S` rebuilds each edge as

```text
fromBlocks A_p B_p C_p D_p
```

where each component is a coordinate projection from `TopologyTuple`:
`rawEdgeTupleA1`, `F2`, `rawEdgeTupleA3`, and `C`.  The endpoint cases in
`rawEdgeTupleA1` and `rawEdgeTupleA3` are handled by the stored endpoint
fields `Ctop` and `F3`.  Since `fromBlocks` is entrywise coordinate
reassembly, `S` is continuous.

The map `R` extracts the raw tuple fields from an edge family using finite
block projections:

```text
E p.succ .toBlocks_11
E p       .toBlocks_12
E p.castSucc .toBlocks_21
E p       .toBlocks_22
E 0       .toBlocks_11
E (last M).toBlocks_21.
```

Each block projection is a submatrix projection, hence continuous, and the
finite product of these projections is continuous.  Thus `R` is continuous.

## Openness

The existing topology layer proves `Z` is open in edge-family space.  Since
`Y = S^{-1}(Z)` and `S` is continuous, `Y` is open in the raw-order tuple
space.

## Subtype Homeomorphism

The source map from `X` to `Y` is continuous because it is the composition of:

```text
z |-> topologyTupleEdgeMatrix z
R
```

on the determinant-chart subtype.  The inverse map from `Y` to `X` is
continuous because it is the composition:

```text
y |-> S y
sourceReadback
topologyTuple
```

on the raw-order source-recursive chart.  The existing `continuousAt`
source-readback theorem applies at every `y in Y`, because `S y in Z`.

Together with the set-level inverse identities from the previous slice, these
continuous maps give a homeomorphism:

```text
X ≃ₜ Y.
```

## Ambient Open Partial Homeomorphism

The same data can be packaged as an ambient open partial homeomorphism on the
raw tuple space:

```text
source = X
target = Y
toFun = F
invFun = H.
```

The source is open by `isOpen_topologyTupleDetChartSet`; the target is open by
the preimage argument above.  The maps-to and inverse fields are exactly the
set-level inverse-chart lemmas from the previous slice.  The continuity fields
use the subtype-continuity facts just reproduced.

## Nonclaims

No differentiability of `H`, no formal tangent equivalence, no determinant
unit theorem, no determinant formula, no Jacobian density, no measure
pushforward, no source-rank coverage, no normal crossing, no pole order, and
no RLCT statement is proved by this slice.
