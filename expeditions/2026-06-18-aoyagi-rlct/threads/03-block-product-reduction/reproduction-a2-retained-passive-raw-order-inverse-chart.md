# Reproduction - A2 Retained-Passive Raw-Order Inverse Chart

Date: 2026-06-26.

Status: pen-and-paper reproduction for the raw-order target chart and its
set-level inverse.  This is finite coordinate bookkeeping only.  It does not
identify a derivative, prove a Jacobian determinant statement, transport
measure, produce normal crossings, or state an RLCT consequence.

## Setup

Let

```text
X = topologyTupleDetChartSet
Z = sourceRecursiveDetChartSet
```

where `X` is the retained-passive determinant chart in product tuple
coordinates and `Z` is the source-recursive determinant chart in edge-family
coordinates.

Write

```text
G : TopologyTuple -> EdgeFamilyTuple
G z = topologyTupleEdgeMatrix z

R : EdgeFamilyTuple -> TopologyTuple
R E = edgeFamilyRawOrderTuple E

S : TopologyTuple -> EdgeFamilyTuple
S y = edgeFamilyOfRawOrderTuple y.
```

The already-landed raw-order equivalence proves:

```text
R (S y) = y
S (R E) = E.
```

The raw-order retained-passive map is

```text
F z = topologyTupleEdgeRawOrder z = R (G z).
```

## Target Chart

The correct ambient target chart for `F` is not a second copy of `X`.  It is
the raw-order encoding of the source-recursive edge-family chart:

```text
Y = { y : TopologyTuple | S y in Z }.
```

This records that a raw tuple is valid exactly when the edge family rebuilt
from its raw blocks satisfies the recursive determinant-chart predicate.

## Map Into Target

If `z in X`, then the existing source-map theorem gives

```text
G z in Z.
```

Also

```text
S (F z) = S (R (G z)) = G z.
```

Hence `F z in Y`.

## Inverse Formula

Define the raw-order readback inverse by

```text
H y = topologyTuple (sourceReadback (S y)).
```

For `z in X`,

```text
H (F z)
  = topologyTuple (sourceReadback (S (R (G z))))
  = topologyTuple (sourceReadback (G z))
  = topologyTuple (sourceReadback ((ofTopologyTuple z).edgeMatrix))
  = topologyTuple (ofTopologyTuple z)
  = z.
```

The load-bearing input is `sourceReadback_edgeMatrix_eq` under the determinant
chart hypothesis for `ofTopologyTuple z`.

For `y in Y`, let `E = S y`.  Then `E in Z`, so the existing readback theorem
gives

```text
(sourceReadback E).edgeMatrix = E.
```

Therefore

```text
F (H y)
  = R ((sourceReadback E).edgeMatrix)
  = R E
  = R (S y)
  = y.
```

The inverse formula also proves `H y in X` whenever `y in Y`, using
`sourceReadback_detChart_of_sourceRecursiveDetChart`.

## Image Equality

The previous two inclusions give:

```text
F '' X = Y.
```

The forward inclusion is the map-into-target argument.  The reverse inclusion
uses the witness `H y`.

## Nonclaims

No differentiability of `H`, no formal tangent equivalence, no determinant
unit theorem, no determinant formula, no Jacobian density, no measure
pushforward, no source-rank coverage, no normal crossing, no pole order, and
no RLCT statement is proved by this slice.
