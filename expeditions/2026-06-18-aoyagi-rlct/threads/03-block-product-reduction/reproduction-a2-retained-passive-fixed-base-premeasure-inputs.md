# Reproduction - A2 retained-passive fixed-base pre-measure inputs

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

The chart-produced local-measure handoff needs two source-side inputs:

```text
hchart_mem :
  sourceChart y ∈ paperEndpointFixedBaseRetainedPassiveP13LocalSource ...

hfactor :
  residualFactorProduct (sourceReadback E(y)).C
    = selected-entry center-coordinate matrix.
```

This rung packages those inputs from three retained-passive coordinate-data
hypotheses:

```text
hdet y          : (retainedData y).detChart
hedge y         : fixed-base edge matrix E(y) = (retainedData y).edgeMatrix
hdataFactor y   : residualFactorProduct (retainedData y).C = selected-entry matrix.
```

It is a fixed-base consumer theorem, not a construction of `hedge`.

## Calculation

Let

```text
E(y) =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
    (fun p => Cedge (sourceChart y) p).
```

For local-source membership, unfold the local source:

```text
sourceChart y ∈ paperEndpointFixedBaseRetainedPassiveP13LocalSource ...
```

means

```text
E(y) ∈ sourceRecursiveDetChartSet.
```

By `hedge y`, this is `(retainedData y).edgeMatrix ∈ sourceRecursiveDetChartSet`.
By `sourceRecursiveDetChart_edgeMatrix_of_detChart`, this follows from
`hdet y`.

For the factor identity, use the existing inverse bridge

```text
sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix.
```

It rewrites `sourceReadback E(y)` to `retainedData y` using `hedge y` and the
determinant-chart inverse theorem `sourceReadback_edgeMatrix_eq`; the result is
then exactly `hdataFactor y`.

Lean endpoint:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** From supplied determinant-chart proofs, fixed-
base edge-matrix realization, and stored-data residual-factor readouts, obtain
both local-source membership and the source-readback residual-factor readout
expected by the chart-produced measure handoff.

**Assumed.** `hdet`, `hedge`, and `hdataFactor`; finite-dimensional fixed-base
endpoint hypotheses; and the selected-entry residual-coordinate equivalence.

**Cited.** None.

**Deferred.** Proving `hedge` for an endpoint-transported explicit Case 2
source family; endpoint transport of `edgeMatrix`, source-recursive determinant
charts, `sourceReadback`, and suffix-recursion states; original source-prior
pushforward; Jacobian density comparison; normal crossings; pole order; and
RLCT.
