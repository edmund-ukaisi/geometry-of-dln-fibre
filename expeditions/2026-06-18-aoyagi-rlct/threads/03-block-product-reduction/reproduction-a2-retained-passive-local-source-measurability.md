# Reproduction - A2 Retained-Passive Local-Source Measurability

Date: 2026-06-26.

Status: reproduced and formalised in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

## Target

The previous retained-passive local-source bridge defined

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
```

as the fixed-base edge-matrix preimage of
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet`.

The local-measure consumer still takes a separate hypothesis

```text
hlocalSource_meas : MeasurableSet localSource.
```

The next narrow target is therefore:

```text
MeasurableSet paperEndpointFixedBaseRetainedPassiveP13LocalSource
```

under a global continuity hypothesis on the source edge family.

## Reproduction

Let

```text
Cedge : alpha -> forall p : Fin (M + 1),
  reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ
```

be globally continuous.  Define

```text
Efixed x =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
    (fun p => (Cedge x p : reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ)).
```

The existing fixed-base theorem

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
```

gives `ContinuousAt Efixed x` from `ContinuousAt Cedge x`.  Since `Cedge` is
globally continuous, `Efixed` is globally continuous by checking continuity at
each point.

The existing retained-passive topology theorem

```text
RetainedPassiveNonredundantCoordinateData.isOpen_sourceRecursiveDetChartSet
```

says the source-recursive determinant-chart set is open in the ambient
edge-family space.  Hence

```text
Efixed^{-1}(sourceRecursiveDetChartSet)
```

is open in `alpha`.  If `alpha` has `OpensMeasurableSpace`, every open set is
measurable.  This proves the local source is measurable.

## Boundary

This is only a topology/measurability bridge.  It does not prove source-rank
openness, global source coverage, residual integrability, loss comparison,
density bounds, measure pushforward, Jacobian transport, normal crossings,
pole order, or RLCT extraction.
