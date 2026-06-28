# Reproduction - A2 Case 2 endpoint-transport chart-produced finite integral

Date: 2026-06-28.

Status: reproduced; Lean targets selected and proved.

## Target

For the endpoint-transported explicit Case 2 retained-passive datum

```text
retainedData yNext =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e
```

and the fixed-base source chart

```text
sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData yNext),
```

prove two facts.

1. `sourceChart` is continuous in the successor selected-entry coordinates.
2. The selected-entry signed-box pushforward measure

   ```text
   mu = Measure.map sourceChart
     ((Pi_i volume|(-Rres_i,Rres_i)).withDensity
       (fun y => ofReal (sourceDensity pivotNext y)))
   ```

   satisfies the existing local finite-integral bound, under the same explicit
   local loss lower bound, density nonnegativity/upper bound, radii, exponent,
   and fixed-base source-data hypotheses as the generic retained-passive
   local-measure handoff.

## Continuity Calculation

Endpoint transport of retained-passive coordinate data changes only the
endpoint-indexed matrix fields by fixed submatrix reindexing:

```text
F2_p  -> F2_p.submatrix id (e p.castSucc).symm
A3_p  -> A3_p.submatrix (e p.castSucc.succ).symm id
C_p   -> C_p.submatrix (e p.succ).symm (e p.castSucc).symm
F3    -> F3.submatrix (e last).symm id.
```

The square retained fields `A1passive` and `Ctop` are unchanged.  Since each
coordinate projection on the retained-passive product topology is continuous
and matrix submatrix reindexing is continuous, the endpoint-transport map is
continuous on the ambient retained-passive coordinate space.  Restricting to
the determinant-chart subtype is continuous because `detChart` is preserved by
endpoint transport.

For Case 2, the already-proved selected-entry retained-passive datum is
continuous into its determinant-chart subtype.  Composing with endpoint
transport gives a continuous map

```text
yNext |-> retainedData yNext
```

into the fixed-base determinant-chart subtype.  Composing once more with

```text
continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
```

gives continuity of `sourceChart`.

Lean endpoints:

```text
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype
PaperEndpointFixedBaseRegularCoordinateSourceData.continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
```

## Finite-Integral Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1)
pivotNext = (J + 2, J + 2) in center.
```

The pre-measure wrapper for this exact source chart gives:

```text
hpre.1 :
  sourceChart yNext in paperEndpointFixedBaseRetainedPassiveP13LocalSource ...

hpre.2 :
  residualFactorProduct (sourceReadback E(yNext)).C (Fin.last 2) 0
    = matrix (chartMap pivotNext yNext residualCoordEquiv),
```

with

```text
residualCoordEquiv =
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext).
```

The generic chart-produced handoff

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix_chartProducedMeasure
```

then applies with `M = 1`, `Cedge = fun E => E`, `x0 = base`, and the
chart-produced measure `Measure.map sourceChart sourceMeasure`.  The
continuity result supplies the `AEMeasurable sourceChart` input.  The source
chart image and source-readback matrix inputs are exactly `hpre.1` and
`hpre.2`.

Lean endpoint:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

## Boundary Checks

- The theorem is two-edge only (`M = 1`).
- Endpoint equivalences `eNext` and `e` are supplied.
- The source measure is chart-produced from the selected-entry signed box; it is
  not an externally constructed source prior.
- The theorem keeps local loss and density hypotheses explicit.
- The theorem keeps the fixed-base regular-coordinate source-data hypothesis
  explicit.
- The theorem adds standard measurable-space/Borel assumptions for the
  fixed-base source edge-family space.
- The theorem does not construct endpoint equivalences, compare source priors
  or Jacobians, prove source-rank coverage, prove positivity beyond the
  supplied density hypotheses, produce normal crossings, compute pole order, or
  extract RLCT.

## Proved / Assumed / Cited / Deferred

**Proved.** Endpoint transport is continuous on retained-passive coordinate
data; the endpoint-transported Case 2 fixed-base source chart is continuous;
and the selected-entry signed-box chart-produced source measure satisfies the
generic local finite-integral bound under the explicit local hypotheses.

**Assumed.** The two-edge fixed-base context; finite-dimensional endpoints;
Case 2 continuation inequalities `hcont` and `hnext`; endpoint equivalences
`eNext` and `e`; fixed-base complement data `U0, hU0`; measurable/Borel
structure on the source edge-family space; fixed-base source data at the base
edge family; positive radii; exponent inequality; local loss lower bound; and
local density nonnegativity/upper bound.

**Cited.** None.

**Deferred.** Endpoint-equivalence construction/provenance; original source
prior identification; Jacobian comparison for an external prior; source-rank
coverage; normal crossings; pole order; and RLCT.
