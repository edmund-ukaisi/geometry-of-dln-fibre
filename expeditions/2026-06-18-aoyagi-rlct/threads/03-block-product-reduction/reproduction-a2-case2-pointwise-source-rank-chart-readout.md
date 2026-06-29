# Reproduction - A2 Case 2 pointwise source-rank chart readout

Date: 2026-06-29.

Status: pen-and-paper reproduction for a narrow source-image support package.

## Question

For an arbitrary coordinate point `yNext` in the continuing Case 2
selected-entry chart, can we package the two pointwise facts already proved
separately?

1. The endpoint-transported retained-passive p.13 source edge family has the
   intended source-rank pattern, provided the base-product rank and the two
   edge-rank equations are supplied.
2. Its fixed-base residual-coordinate map is exactly the selected-entry chart
   map at `yNext`.

Answer: yes.  This is a source-image support/readout statement for one chart
point.  It is not a source-image equality or coverage theorem.

## Source Calculation

Aoyagi's p.13 retained-passive construction writes source edges from
determinant-chart data and reads them back by the same Schur-complement
coordinates.  In the continuing Case 2 selected-entry specialization, the
endpoint-transported retained-passive data encode the next residual block by
the selected-entry chart map.  Therefore the fixed-base residual-coordinate
map of the produced edge family is

```text
c ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext yNext
       (residualCoordEquiv c).
```

The same p.13 rank bookkeeping says that the two source edge ranks are

```text
rank(edge 0) = r + card tau,
rank(edge 1) = r + rank(case2SuccessorSelectedEntryMatrix ... yNext ...).
```

Thus, under the pointwise rank equations

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix ... yNext ...) = rEdge 1,
```

the same source edge family lies in
`paperEndpointFixedBaseSourceRankStratum`.

The retained-passive determinant-chart construction also gives membership in
`paperEndpointFixedBaseRetainedPassiveP13LocalSource` for every `yNext`.

## Lean Target

Add a theorem in `RetainedPassiveCase2LocalJacobianMeasure.lean`, near the
existing chart-map readout theorem:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_chartMap
```

The proof should combine:

```text
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Nonclaims

This theorem does not prove selected-entry source coverage, source/image
equality, exact-rank openness, source-prior transport, Jacobian compatibility,
normal crossings, pole order, or RLCT.  The successor-rank equation is
supplied for the chosen `yNext`; no numerical rank formula is proved.
