# Reproduction - A2 Case 2 endpoint-transport source-edge-family pre-measure inputs

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

Combine three already-proved inputs:

1. the generic fixed-base source-edge-family pre-measure specialization;
2. determinant-chart preservation for endpoint-transported explicit Case 2
   retained-passive data;
3. endpoint-transported stored-`C` residual-factor selected-entry matrix
   readout.

The result is a two-edge fixed-base source chart

```text
sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W₂ B₂ U₀ hU₀ (retainedData yNext)
```

where

```text
retainedData yNext =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e.
```

The supplied endpoint equivalence is

```text
e q :
  case2PostPivotTwoEdgeDomain n S J τ q ≃
  throughSubspaceEndpointComplementIndex
    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q.
```

The desired output is local-source membership and the source-readback residual-
factor matrix identity for this fixed-base source chart.

## Calculation

Specialize the generic source-edge-family theorem to `M = 1`, so

```text
Fin (M + 2) = Fin 3
Fin (M + 1) = Fin 2.
```

Set

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) ∈ center.
```

The theorem

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
```

needs two inputs for `retainedData`.

First, determinant-chart membership:

```text
∀ yNext, (retainedData yNext).detChart.
```

This is exactly

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart
```

after unfolding `retainedData`.

Second, the stored-data residual-factor matrix identity:

```text
residualFactorProduct (retainedData yNext).C (Fin.last 2) 0
  = matrix (chartMap pivotNext yNext ...)
```

with residual-coordinate equivalence

```text
case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
  n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext).
```

This is exactly

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix
```

after unfolding `retainedData`.

The generic source-edge-family theorem then discharges the fixed-base
edge-matrix realization automatically from the definition of
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData`, and returns:

1. `sourceChart yNext` lies in the fixed-base retained-passive p.13 local
   source;
2. the `sourceReadback` residual-factor product of the fixed-base edge matrix
   of `sourceChart yNext` is the successor selected-entry center-coordinate
   matrix.

## Boundary Checks

- This is specialized to the two-edge Case 2 window.  It does not assert an
  arbitrary-depth endpoint-transport theorem.
- The endpoint equivalences `e` and `eNext` are supplied.  The result does not
  construct them or prove that they come from a geometric fixed-base
  normalisation.
- The source chart is built from the endpoint-transported retained-passive datum
  itself.  No separate transport of `edgeMatrix` or `sourceReadback` is proved.
- No source-prior pushforward, Jacobian density comparison, positivity,
  integrability, normal crossings, pole order, or RLCT extraction is used.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Supplied endpoint equivalences transport the
explicit Case 2 selected-entry retained-passive datum into the fixed-base
two-edge retained-passive source-family socket, giving local-source membership
and the source-readback selected-entry residual-factor matrix readout.

**Assumed.** The two-edge fixed-base context; finite-dimensional endpoints; the
Case 2 continuation inequalities `hcont` and `hnext`; endpoint equivalences
`eNext` and `e`; and the fixed-base complement data `U₀, hU₀`.

**Cited.** None.

**Deferred.** Construction/geometric provenance of the endpoint equivalences;
arbitrary-depth endpoint transport; original source-prior pushforward; Jacobian
density comparison; positivity/integrability; normal crossings; pole order; and
RLCT.
