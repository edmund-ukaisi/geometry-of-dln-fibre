# A2 retained-passive fixed-base edge realisation

## Boundary

This slice is fixed-base finite-source bookkeeping.  It uses the existing
fixed-base matrix-realisation API to build continuous reversed edge maps whose
fixed-base matrices are the `edgeMatrix` of a supplied retained-passive
coordinate datum.

It does not construct the retained-passive datum, identify Case 2 endpoint
complement indices, prove a source chart image theorem, prove rank-stratum
coverage, prove a measure pushforward or Jacobian formula, compare the original
DLN loss, prove normal crossings, compute pole order, or extract an RLCT.

## Pen-and-paper reproduction

Fix endpoint data `W,B,U0,hU0`.  Let

```text
kappa' i =
  throughSubspaceEndpointComplementIndex
    (reverseVertex W) (reverseEdge W B) U0 i.
```

A retained-passive datum

```text
data : RetainedPassiveNonredundantCoordinateData
  (rho := Fin (finrank K U0)) kappa'
```

has a fixed-base retained-passive matrix family

```text
data.edgeMatrix p :
  Matrix
    (Fin(finrank K U0) ⊕ kappa'(p+1))
    (Fin(finrank K U0) ⊕ kappa'(p)) K.
```

The fixed-base API already provides a continuous reversed edge family for any
prescribed matrix family `M`:

```text
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U0 hU0 M
```

and proves that the fixed-base edge-matrix extraction recovers `M`:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
  (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices W B U0 hU0 M)
= M.
```

Substitute `M = data.edgeMatrix`.  Then the constructed edge family has
fixed-base edge matrices exactly `data.edgeMatrix`.

If additionally `data.detChart`, the retained-passive source-readback inverse
theorem gives

```text
sourceReadback(data.edgeMatrix) = data.
```

Combining the two equalities gives source readback of the constructed fixed-base
edge family:

```text
sourceReadback
  (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
    (paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
      W B U0 hU0 data.edgeMatrix))
= data.
```

## Checks

- The result is generic in retained-passive endpoint complement indices; it
  does not mention the synthetic Case 2 endpoint family.
- The determinant-chart assumption is needed only for the readback equality,
  not for fixed-base matrix realisation.
- This removes an explicit `hedge` equality only when the source edge family is
  defined from `data.edgeMatrix`; it does not construct a paper source chart.
