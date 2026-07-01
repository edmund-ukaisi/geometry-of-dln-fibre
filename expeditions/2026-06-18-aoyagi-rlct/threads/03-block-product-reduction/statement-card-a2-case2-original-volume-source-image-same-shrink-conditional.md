# Statement Card - A2 Case 2 original-volume source-image same-shrink conditional

## Claim

There is one local Case 2 determinant/punctured-sector shrink `V subset G`
which carries both the source-chart image package and the conditional
original-volume/source-image density identity.

Expected public Lean name:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceImageReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

## Statement Shape

On the local `V`, Lean proves:

- `readback (sourceChart z) = z` for `z in V`;
- `Set.InjOn sourceChart V`;
- `ContinuousOn sourceChart V`;
- `MeasurableSet (sourceChart '' V)`;
- `sourceChart '' V subset p13SourceSet`.

For any `thetaReference`, raw Haar measure `rawHaar`, and measurable
`chartPiece subset sourceChart '' V`, if

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet,
```

then with

```text
sourceRef = Measure.map sourceChart (thetaReference.restrict V)
c = ((Measure.map rawLinearEquiv rawHaar)
      .addHaarScalarFactor (originalTupleVolume d)),
invHaarDensity _ = (c^-1 : NNReal)
```

Lean proves:

```text
originalVolume.restrict chartPiece =
  (sourceRef.withDensity invHaarDensity).restrict chartPiece
```

and the density is a.e. bounded by the same constant.

## Inputs Used

- `exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext`;
- `case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData`;
- `paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet`;
- `map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet`;
- `measure_eq_inv_smul_of_eq_nnreal_smul`;
- local source-chart continuity through the retained-passive p.13 source chart.

## Nonclaims

No raw-Haar pushforward is proved.  No raw-order image is identified with raw
Haar.  No determinant-chart Haar transport, full source-image coverage,
source-rank coverage, original source-prior transport, Haar scalar
normalization, normal crossings, pole order, or RLCT extraction is claimed.

## Verification

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
