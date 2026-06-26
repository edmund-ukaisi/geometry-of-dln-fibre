# Reproduction - A2 Retained-Passive p.13 Named Source Chart

Date: 2026-06-26.

Status: pen-and-paper prerequisite for a narrow Lean source-chart wrapper.
This is fixed-base matrix realisation and readback only.

## Question

Earlier Lean work proves that any retained-passive coordinate datum `data`
with fixed-base edge matrices `data.edgeMatrix` can be realised by continuous
reversed edge maps, and that source readback recovers `data` when
`data.detChart` holds.

The missing ergonomic object is a named source-chart map

```text
data |-> Cedge_data
```

from determinant-chart retained-passive data to fixed-base continuous reverse
edge families.  The map should be the prescribed-matrix realisation with
prescribed matrices `data.edgeMatrix`.

## Calculation

Fix `W,B,U0,hU0` and set

```text
kappa'(i) =
  throughSubspaceEndpointComplementIndex
    (reverseVertex W) (reverseEdge W B) U0 i.
```

For

```text
data :
  {d : RetainedPassiveNonredundantCoordinateData
        (rho := Fin(finrank K U0)) kappa' // d.detChart}
```

define

```text
Cedge_data(p) =
  paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
    W B U0 hU0 data.1.edgeMatrix p.
```

The fixed-base prescribed-matrix realisation theorem gives, entrywise in `p`,

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0 Cedge_data p
  = data.1.edgeMatrix p.
```

Hence the whole edge-matrix family extracted from `Cedge_data` is
`data.1.edgeMatrix`.

Because `data.2 : data.1.detChart`, the retained-passive source inverse
theorem gives

```text
sourceReadback(data.1.edgeMatrix) = data.1.
```

Substituting the extracted edge matrix of `Cedge_data` yields

```text
sourceReadback
  (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0 Cedge_data)
= data.1.
```

The source-recursive determinant-chart membership also follows from the same
determinant-chart hypothesis:

```text
sourceRecursiveDetChart(data.1.edgeMatrix).
```

After substituting the extracted edge matrix of `Cedge_data`, the point `data`
lies in the fixed-base retained-passive p.13 local source for the named
source-chart map.

Continuity is a direct composition:

```text
data |-> data.1.edgeMatrix
```

is continuous on the determinant-chart subtype, and the prescribed-matrix
realisation map

```text
M |-> paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U0 hU0 M
```

is continuous.

## Boundary

This defines a canonical source edge family for already-given
retained-passive determinant-chart coordinate data.  It does not construct
the retained-passive coordinates from an arbitrary source point.  It does not
prove local image equality, source-rank coverage, source-measure pushforward,
density or Jacobian transport, selected-entry residual-factor identities,
normal crossings, pole order, or RLCT extraction.
