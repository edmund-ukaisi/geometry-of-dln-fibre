# Statement Card - A2 Case 2 same-shrink raw domination and source chart package

## Expected Lean Name

```text
exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

## Statement Shape

For every open neighborhood `G` of a Case 2 passive-theta point in the
determinant sector with nonzero selected pivot, Lean returns one open
neighborhood `V` with `z0 in V` and `V subset G`.

On this same `V`, the theorem packages:

- source-chart readback: `readback (sourceChart z) = z` for `z in V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`;
- for every source measure restricted to `V`, the one-stage raw composite and
  two-stage raw pushforward both equal the direct source-chart pushforward;
- under explicit determinant-side reverse domination and a same-shrink lower
  bound for `sourceDensity`, finite reverse raw-source domination by
  `Measure.map rawMap (coordinateSourceMeasure.restrict V)`.

The raw-domination hypothesis socket is:

```text
rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V)

Cdet < infinity

epsilon <= sourceDensity z
```

for `baseJ.restrict V`-a.e. `z`, with `epsilon` nonzero and finite.  The
conclusion is:

```text
(Cdet * epsilon^{-1}) < infinity

rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) *
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Inputs Used

- The source-chart image package
  `exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet`.
- The raw-order/source-chart two-stage package
  `exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext`.
- The reverse raw-source density lower adapter
  `exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower`.
- The elementary support fact that if `V subset Vtwo`, then
  `(sourceMeasure.restrict V).restrict Vtwo = sourceMeasure.restrict V`.

## Nonclaims

The determinant-side reverse domination and the lower bound for
`sourceDensity` remain explicit hypotheses.  The statement does not prove
determinant-chart Haar transport, exact raw-Haar pushforward, raw-Haar
normalization, source-image coverage, source-rank coverage, original
source-prior transport, normal crossings, pole order, or RLCT extraction.
