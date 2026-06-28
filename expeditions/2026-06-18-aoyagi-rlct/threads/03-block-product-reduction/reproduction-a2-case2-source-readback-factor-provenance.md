# Reproduction - A2 Case 2 source-readback factor provenance

## Shape

Fix the endpoint-transported explicit Case 2 selected-entry retained-passive
datum

```text
data(yNext) :=
  (case2PostPivotSelectedEntryRetainedPassiveData
    (rho := Fin (finrank U0)) n hS hcont hnext yNext eNext).endpointTransport e.
```

The fixed-base p.13 source edge family attached to this datum is

```text
sourceChart(yNext) :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 data(yNext).
```

Let

```text
E(yNext) :=
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W2 B2 U0 hU0
    (fun p => sourceChart(yNext) p).
```

The target is to prove that the retained-passive source readback of `E(yNext)`
is exactly `data(yNext)`, and therefore its adjacent `C 1` and `C 0` factors
are the displayed Case 2 post-pivot residual block and following factor after
submatrixing by the forward endpoint equivalences.

## Calculation

The fixed-base edge-family realization theorem says

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges
  (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData data)
= data.edgeMatrix.
```

The endpoint-transported explicit Case 2 datum has determinant-chart proof

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_detChart.
```

Therefore the retained-passive readback inverse theorem gives

```text
sourceReadback E(yNext)
= sourceReadback data(yNext).edgeMatrix
= data(yNext).
```

The factor identities then follow by rewriting the readback to `data(yNext)`
and applying the previously landed endpoint-transport factor-alignment lemmas:

```text
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_one_submatrix_eq_displayedPostPivotResidualBlock
case2PostPivotSelectedEntryRetainedPassiveData_endpointTransport_C_zero_submatrix_eq_displayedPostPivotFreeFollowingFactor.
```

## Boundary

This proves actual fixed-base source-readback provenance for the constructed
endpoint-transported Case 2 source chart.  It is not another residual-product
wrapper: the adjacent factors are facts about `sourceReadback E(yNext)`.

The endpoint equivalences `eNext` and `e` remain supplied.  The theorem does
not construct `tau`, prove `hTau`, prove label-preserving endpoint provenance,
identify an arbitrary `ofTopologyTuple` datum with this source readback,
transport an original prior, compare Jacobians, prove normal crossings,
compute pole order, or extract RLCT.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The fixed-base source readback of the
endpoint-transported explicit Case 2 source edge family equals the transported
datum, and its adjacent two factors are the displayed Case 2 post-pivot
residual block and following factor after forward endpoint reindexing.

**Assumed.** The endpoint equivalences `eNext` and `e`, determinant-continuity
fixed-base context, and Aoyagi Case 2 continuation hypotheses `hS`, `hcont`,
and `hnext`.

**Deferred.** `tau`/`hTau` construction, label-preserving endpoint provenance,
arbitrary retained-passive `ofTopologyTuple` alignment, source-prior transport,
Jacobian comparison, normal crossings, pole order, and RLCT.
