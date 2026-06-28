# Reproduction - A2 Case 2 endpoint-transport source-edge-family residual square-sum

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

For the two-edge Case 2 endpoint-transport source chart from

```text
retainedData yNext =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e
```

and

```text
sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W₂ B₂ U₀ hU₀ (retainedData yNext),
```

prove the fixed-base residual-square-sum readout

```text
aoyagiCoordinateSquareSum
  (paperEndpointFixedBaseResidualBlockCoordinateMap
    W₂ B₂ U₀ hU₀ (fun E => E) (sourceChart yNext))
= SelectedEntrySignedBox.CenterCoord.residual pivotNext yNext.
```

This is the residual-square-sum consequence of the already-proved
source-readback selected-entry matrix readout for this source chart.

## Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) ∈ center.
```

The endpoint-transport pre-measure wrapper gives a pair:

```text
hpre.1 :
  sourceChart yNext ∈ paperEndpointFixedBaseRetainedPassiveP13LocalSource ...

hpre.2 :
  residualFactorProduct (sourceReadback E(yNext)).C (Fin.last 2) 0
    = matrix (chartMap pivotNext yNext residualCoordEquiv)
```

where

```text
residualCoordEquiv =
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext).
```

Only the second component is needed for the square-sum readout.  Apply the
generic bridge

```text
aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix
```

with `M = 1`, `Cedge = fun E => E`, the source chart above, and `hpre.2`.
This bridge reads the selected-entry matrix identity through
`AoyagiResidualBlockCoordinateIndex.value_matrix` and the selected-entry
identity

```text
SelectedEntrySignedBox.CenterCoord.residual =
  aoyagiCoordinateSquareSum (SelectedEntrySignedBox.CenterCoord.chartMap ...)
```

after reindexing by the residual-coordinate equivalence.

No local-source membership, measure, density, Jacobian, normal-crossing, pole
order, or RLCT argument is used in this corollary.

Lean endpoint:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

## Boundary Checks

- The theorem is two-edge only (`M = 1` in the generic bridge).
- Endpoint equivalences `e` and `eNext` are supplied.
- The theorem does not construct endpoint equivalences or prove their geometric
  source.
- The theorem does not prove source-measure pushforward, source-chart
  measurability, Jacobian density comparison, positivity, integrability, normal
  crossings, pole order, or RLCT.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** For the fixed-base source chart built from the
endpoint-transported explicit Case 2 retained-passive datum, the fixed-base
residual-block coordinate square-sum is the successor selected-entry center
residual.

**Assumed.** The two-edge fixed-base context; finite-dimensional endpoints; the
Case 2 continuation inequalities `hcont` and `hnext`; endpoint equivalences
`eNext` and `e`; and the fixed-base complement data `U₀, hU₀`.

**Cited.** None.

**Deferred.** Endpoint-equivalence construction/provenance; measure pushforward;
Jacobian comparison; positivity/integrability; normal crossings; pole order; and
RLCT.
