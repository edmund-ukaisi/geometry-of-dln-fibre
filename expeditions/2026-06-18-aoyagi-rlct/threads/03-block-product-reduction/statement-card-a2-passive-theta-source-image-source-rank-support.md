# Statement Card - A2 passive-theta source-image source-rank support

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Public names:

```text
case2PassiveThetaEndpointSourceChart_mem_sourceRankStratum
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_sourceRankStratum
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_restrict_sourceRankStratum_eq_self
```

## Expected Output

The pointwise theorem proves:

```text
sourceChart theta in
  paperEndpointFixedBaseSourceRankStratum W2 B2 id r rEdge
```

from:

```text
(retainedData theta).detChart
finrank range(paperTotalMap W2 B2) = r
r + Fintype.card tau = rEdge 0
r + rank(case2SuccessorSelectedEntryMatrix theta.yNext) = rEdge 1
```

The local image theorem returns an open `V` with:

```text
z0 in V
V subset G
forall z in V, (retainedData z).detChart
forall z in V, readback (sourceChart z) = z
Set.InjOn sourceChart V
ContinuousOn sourceChart V
MeasurableSet (sourceChart '' V)
forall z in V, successor-rank(z) -> sourceChart z in sourceStratum
(forall z in V, successor-rank(z)) ->
  forall E in sourceChart '' V, E in sourceStratum
```

The measure theorem returns the same local data and proves:

```text
forall thetaMeasure,
  (forall^ae z with respect to thetaMeasure.restrict V, successor-rank(z)) ->
  let mu := Measure.map sourceChart (thetaMeasure.restrict V)
  mu.restrict sourceStratum = mu
```

## Inputs Used

- `paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq`.
- `rank_case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfMatrix`.
- `rank_case2DisplayedPostPivotResidualBlock_sourceResidualOfMatrix`.
- `RetainedPassiveNonredundantCoordinateData.rank_endpointTransport_C`.
- The stronger local source-image theorem, now exposing determinant-chart
  membership of the retained data on `V`.
- `measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem`.

## Mathematical Meaning

The theorem records the elementary rank calculation behind the p.13 retained
passive chart: the source edge ranks are `r` plus the ranks of the two stored
residual `C` blocks, and in Case 2 those stored ranks are `|tau|` and the
successor selected-entry residual rank.  Supplying those rank equations places
the chart-produced source edge family in the named source-rank stratum.

## Nonclaims

- No source-rank coverage.
- No equality between `sourceChart '' V` and a source-rank stratum.
- No exact-rank openness theorem.
- No original source-prior domination, equality, or transport.
- No determinant-chart Haar or raw-order Haar transport.
- No normal crossings, pole order, or RLCT extraction.
