# Reproduction - A2 retained-passive direct-chart positive-set measurability

Date: 2026-06-28.

Status: controller pen-and-paper reproduction before Lean.  This is a
measurability hardening step for the retained-passive determinant-chart
residual handoffs.

## Shape

For retained-passive p.13 determinant-chart coordinates, set

```text
rho = Fin (finrank R U0),
kappa' = throughSubspaceEndpointComplementIndex ... U0,
EFam = forall p : Fin (M + 1),
  reverseVertex W p.castSucc ->L[R] reverseVertex W p.succ.
```

The direct retained-passive source chart used by the determinant-chart residual
handoff is

```text
directChart(z) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U0 hU0 (ofTopologyTuple z).
```

The target positive-set hypothesis currently carried by the selected-entry
determinant-chart handoffs is

```text
MeasurableSet {z : TopologyTuple rho kappa' R |
  0 < aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap
      W B U0 hU0 id (directChart z))}.
```

The goal is to prove this once, generically.

## Calculation

The existing source-space measurability theorem works because the identity
source family is continuous as a function of the source edge family:

```text
x |-> x.
```

For the determinant-chart direct chart, the function is instead

```text
z |-> directChart(z).
```

It suffices to prove that the fixed-base edge-matrix family associated to
`directChart(z)` is measurable:

```text
z |->
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
    (fun p => (directChart z p : ... ->L[R] ...)).
```

By the retained-passive source-edge-family readout identity, this edge matrix
is exactly the retained-passive edge matrix of `ofTopologyTuple z`.  The latter
is assembled from the coordinate fields of `ofTopologyTuple z` and the solved
`A1`/`A3` blocks.  The coordinate fields are continuous in `z`.  The solved
blocks use matrix inverse operations on square retained factors; over `R`,
matrix inverse is Borel-measurable, so the solved blocks and hence the
edge-matrix family are measurable.  The proof should use the existing local
API for matrix inverse measurability rather than reprove entrywise adjugate
formulas.

Once the edge-matrix family is measurable, the existing residual-coordinate
API gives

```text
Measurable
  (paperEndpointFixedBaseResidualBlockCoordinateMap W B U0 hU0 id
    ∘ directChart).
```

The finite square-sum map is measurable, and the positive set is the preimage
of `(0, infinity)`.

## Lean target

Add in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
```

near the existing identity-source positive-set lemma:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  measurableSet_residualSquareSum_pos_retainedPassiveP13Canonical_directChart
```

Then use this helper to remove the explicit target positive-set measurability
hypothesis from the Case 2 endpoint-transported selected-entry determinant
chart theorem and the two Case 2 raw-order inverse-Jacobian consumer theorems.

## Boundary

This is only measurability of a finite coordinate positive set.  It does not
prove residual positivity, residual integrability, the determinant-chart
pushforward identity, chart coverage, original external source-prior transport,
local loss or density bounds, source-rank coverage, normal crossings, pole
order, or RLCT extraction.
